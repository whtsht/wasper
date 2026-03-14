use super::runtime::{ExecState, Instance};
use super::stack::{Frame, Label, Stack};
use super::store::{FuncInst, Store};
use super::table::*;
use super::trap::Trap;
use super::value::{Ref, Value};
use super::{cast, memory};
use crate::binary::Instr;
use crate::binary::ValType;
#[cfg(not(feature = "std"))]
use crate::lib::*;
use core::ops::Neg;
use num_traits::float::Float;

pub fn step(
    instances: &mut Vec<Instance>,
    instrs: &Vec<Instr>,
    pc: usize,
    store: &mut Store,
    stack: &mut Stack,
) -> Result<ExecState, Trap> {
    let frame = stack.top_frame().clone();
    let instance = &mut instances[frame.instance_addr];
    match &instrs[pc] {
        //////////////////////////
        // Control Instructions //
        //////////////////////////
        Instr::Nop => {}
        Instr::Unreachable => return Err(Trap::Unreachable),
        Instr::Block { bt, end_offset } => {
            stack.push_label(Label {
                n: instance.block_to_arity(bt),
                stack_offset: stack.values_len(),
                pc: end_offset + pc,
                cont: false,
            });
        }
        Instr::Loop { bt } => {
            stack.push_label(Label {
                n: instance.block_to_arity(bt),
                stack_offset: stack.values_len(),
                pc,
                cont: true,
            });
        }
        Instr::If {
            bt,
            else_offset,
            end_offset,
        } => {
            let c = stack.pop_value::<i32>();
            if c != 0 {
                stack.push_label(Label {
                    n: instance.block_to_arity(bt),
                    stack_offset: stack.values_len(),
                    pc: end_offset + pc,
                    cont: false,
                });
            } else if let Some(else_offset) = else_offset {
                stack.push_label(Label {
                    n: instance.block_to_arity(bt),
                    stack_offset: stack.values_len(),
                    pc: end_offset + pc,
                    cont: false,
                });
                return Ok(ExecState::Continue(else_offset + pc));
            } else {
                return Ok(ExecState::Continue(end_offset + pc));
            }
        }
        Instr::Br(l) => {
            if *l as usize >= stack.labels_len() {
                return match unwind_stack(&frame, stack) {
                    Some(new_pc) => Ok(ExecState::Continue(new_pc)),
                    None => Ok(ExecState::Return),
                };
            }
            let new_pc = stack.jump(*l as usize);
            return Ok(ExecState::Continue(new_pc));
        }
        Instr::BrIf(l) => {
            let c = stack.pop_value::<i32>();
            if c != 0 {
                if *l as usize >= stack.labels_len() {
                    return match unwind_stack(&frame, stack) {
                        Some(new_pc) => Ok(ExecState::Continue(new_pc)),
                        None => Ok(ExecState::Return),
                    };
                }
                let new_pc = stack.jump(*l as usize);
                return Ok(ExecState::Continue(new_pc));
            }
        }
        Instr::BrTable { indexs, default } => {
            let i = stack.pop_value::<i32>() as usize;
            return if i < indexs.len() {
                let l = indexs[i] as usize;
                if l >= stack.labels_len() {
                    return match unwind_stack(&frame, stack) {
                        Some(new_pc) => Ok(ExecState::Continue(new_pc)),
                        None => Ok(ExecState::Return),
                    };
                }
                let new_pc = stack.jump(indexs[i] as usize);
                Ok(ExecState::Continue(new_pc))
            } else {
                let l = *default as usize;
                if l >= stack.labels_len() {
                    return match unwind_stack(&frame, stack) {
                        Some(new_pc) => Ok(ExecState::Continue(new_pc)),
                        None => Ok(ExecState::Return),
                    };
                }
                let new_pc = stack.jump(l as usize);
                return Ok(ExecState::Continue(new_pc));
            };
        }
        Instr::Return => {
            return match unwind_stack(&frame, stack) {
                Some(new_pc) => Ok(ExecState::Continue(new_pc)),
                None => Ok(ExecState::Return),
            };
        }
        Instr::Call(a) => {
            let addr = instance.funcaddrs[*a as usize];
            let func = &store.funcs[addr];

            return attach(func, stack, pc);
        }
        Instr::CallIndirect(typeidx, tableidx) => {
            let ta = instance.tableaddrs[*tableidx as usize];
            let tab = &store.tables[ta];
            let ft = &instance.types[*typeidx as usize];
            let i = stack.pop_value::<i32>() as usize;
            if i >= tab.elem.len() {
                return Err(Trap::UndefinedElement);
            }
            let r = tab.elem[i];
            if let Ref::Func(a) = r {
                let func = &store.funcs[a];
                if func.functype() != ft {
                    return Err(Trap::IndirectCallTypeMismatch);
                }
                return attach(func, stack, pc);
            } else {
                return Err(Trap::NotFundRef);
            }
        }

        ////////////////////////////
        // Reference Instructions //
        ////////////////////////////
        Instr::RefNull(_) => stack.push_value(Value::Ref(Ref::Null)),
        Instr::RefIsNull => {
            let c = match stack.pop_value::<Value>() {
                Value::Ref(Ref::Null) => Value::I32(1),
                _ => Value::I32(0),
            };
            stack.push_value(c);
        }
        Instr::RefFunc(x) => {
            let addr = instance.funcaddrs[*x as usize];
            stack.push_value(Value::Ref(Ref::Func(addr)));
        }

        /////////////////////////////
        // Parametric Instructions //
        /////////////////////////////
        Instr::Drop => {
            stack.pop_value::<Value>();
        }
        Instr::Select => {
            let c = stack.pop_value::<i32>();
            let val2 = stack.pop_value::<Value>();
            let val1 = stack.pop_value::<Value>();
            if c != 0 {
                stack.push_value(val1);
            } else {
                stack.push_value(val2);
            }
        }

        ///////////////////////////
        // Variable Instructions //
        ///////////////////////////
        Instr::LocalGet(l) => {
            let value = frame.local[*l as usize];
            stack.push_value(value);
        }
        Instr::LocalSet(l) => {
            let value = stack.pop_value();
            stack.top_frame_mut().local[*l as usize] = value;
        }
        Instr::LocalTee(l) => {
            let value: Value = stack.pop_value();
            stack.push_value(value);
            stack.top_frame_mut().local[*l as usize] = value;
        }
        Instr::GlobalGet(i) => {
            let globalindex = instance.globaladdrs[*i as usize];
            stack.push_value(store.globals[globalindex].value);
        }
        Instr::GlobalSet(i) => {
            let value = stack.pop_value();
            let globalindex = instance.globaladdrs[*i as usize];
            store.globals[globalindex].value = value;
        }

        ////////////////////////
        // Table Instructions //
        ////////////////////////
        Instr::TableGet(x) => table_get(x, instance, store, stack)?,
        Instr::TableSet(x) => table_set(x, instance, store, stack)?,
        Instr::TableInit(x, y) => table_init(x, y, instance, store, stack)?,
        Instr::TableCopy(x, y) => table_copy(x, y, instance, store, stack)?,
        Instr::TableGrow(x) => table_grow(x, instance, store, stack),
        Instr::TableSize(x) => table_size(x, instance, store, stack),
        Instr::TableFill(x) => table_fill(x, instance, store, stack)?,
        Instr::ElemDrop(x) => elem_drop(x, instance, store),

        /////////////////////////
        // Memory Instructions //
        /////////////////////////
        Instr::I32Load(memarg) => memory::i32_load(memarg, instance, store, stack)?,
        Instr::I64Load(memarg) => memory::i64_load(memarg, instance, store, stack)?,
        Instr::F32Load(memarg) => memory::f32_load(memarg, instance, store, stack)?,
        Instr::F64Load(memarg) => memory::f64_load(memarg, instance, store, stack)?,
        Instr::I32Load8S(memarg) => memory::i32_load_8s(memarg, instance, store, stack)?,
        Instr::I32Load8U(memarg) => memory::i32_load_8u(memarg, instance, store, stack)?,
        Instr::I32Load16S(memarg) => memory::i32_load_16s(memarg, instance, store, stack)?,
        Instr::I32Load16U(memarg) => memory::i32_load_16u(memarg, instance, store, stack)?,
        Instr::I64Load8S(memarg) => memory::i64_load_8s(memarg, instance, store, stack)?,
        Instr::I64Load8U(memarg) => memory::i64_load_8u(memarg, instance, store, stack)?,
        Instr::I64Load16S(memarg) => memory::i64_load_16s(memarg, instance, store, stack)?,
        Instr::I64Load16U(memarg) => memory::i64_load_16u(memarg, instance, store, stack)?,
        Instr::I64Load32S(memarg) => memory::i64_load_32s(memarg, instance, store, stack)?,
        Instr::I64Load32U(memarg) => memory::i64_load_32u(memarg, instance, store, stack)?,
        Instr::I32Store(memarg) => memory::i32_store(memarg, instance, store, stack)?,
        Instr::I64Store(memarg) => memory::i64_store(memarg, instance, store, stack)?,
        Instr::F32Store(memarg) => memory::f32_store(memarg, instance, store, stack)?,
        Instr::F64Store(memarg) => memory::f64_store(memarg, instance, store, stack)?,
        Instr::I32Store8(memarg) => memory::i32_store_8(memarg, instance, store, stack)?,
        Instr::I32Store16(memarg) => memory::i32_store_16(memarg, instance, store, stack)?,
        Instr::I64Store8(memarg) => memory::i64_store_8(memarg, instance, store, stack)?,
        Instr::I64Store16(memarg) => memory::i64_store_16(memarg, instance, store, stack)?,
        Instr::I64Store32(memarg) => memory::i64_store_32(memarg, instance, store, stack)?,
        Instr::MemorySize => memory::memory_size(instance, store, stack),
        Instr::MemoryGrow => memory::memory_grow(instance, store, stack),
        Instr::MemoryInit(x) => memory::memory_init(x, instance, store, stack)?,
        Instr::DataDrop(x) => memory::data_drop(x, instance, store),
        Instr::MemoryCopy => memory::memory_copy(instance, store, stack)?,
        Instr::MemoryFill => memory::memory_fill(instance, store, stack)?,

        //////////////////////////
        // Numeric Instructions //
        //////////////////////////
        Instr::I32Const(a) => stack.push_value(*a),
        Instr::I64Const(a) => stack.push_value(*a),
        Instr::F32Const(a) => stack.push_value(*a),
        Instr::F64Const(a) => stack.push_value(*a),
        // iadd_N
        Instr::I32Add => stack.binop(i32::wrapping_add),
        Instr::I64Add => stack.binop(i64::wrapping_add),
        // isub_N
        Instr::I32Sub => stack.binop(i32::wrapping_sub),
        Instr::I64Sub => stack.binop(i64::wrapping_sub),
        // imul_N
        Instr::I32Mul => stack.binop(i32::wrapping_mul),
        Instr::I64Mul => stack.binop(i64::wrapping_mul),
        // idiv_u_N
        Instr::I32DivU => stack.binop_trap(|a: i32, b| {
            (a as u32)
                .checked_div(b as u32)
                .ok_or(Trap::DivideByZeroInt)
                .map(|r| r as i32)
        })?,
        Instr::I64DivU => stack.binop_trap(|a: i64, b| {
            (a as u64)
                .checked_div(b as u64)
                .ok_or(Trap::DivideByZeroInt)
                .map(|r| r as i64)
        })?,
        // idiv_s_N
        Instr::I32DivS => stack.binop_trap(|a: i32, b| {
            if b == 0 {
                Err(Trap::DivideByZeroInt)
            } else {
                a.checked_div(b).ok_or(Trap::IntegerOverflow)
            }
        })?,
        Instr::I64DivS => stack.binop_trap(|a: i64, b| {
            if b == 0 {
                Err(Trap::DivideByZeroInt)
            } else {
                a.checked_div(b).ok_or(Trap::IntegerOverflow)
            }
        })?,
        // irem_u_N
        Instr::I32RemU => stack.binop_trap(|a: i32, b| {
            if b == 0 {
                Err(Trap::DivideByZeroInt)
            } else {
                Ok((a as u32).wrapping_rem(b as u32) as i32)
            }
        })?,
        Instr::I64RemU => stack.binop_trap(|a: i64, b| {
            if b == 0 {
                Err(Trap::DivideByZeroInt)
            } else {
                Ok((a as u64).wrapping_rem(b as u64) as i64)
            }
        })?,
        // irem_s_N
        Instr::I32RemS => stack.binop_trap(|a: i32, b| {
            if b == 0 {
                Err(Trap::DivideByZeroInt)
            } else {
                Ok(a.wrapping_rem(b))
            }
        })?,
        Instr::I64RemS => stack.binop_trap(|a: i64, b| {
            if b == 0 {
                Err(Trap::DivideByZeroInt)
            } else {
                Ok(a.wrapping_rem(b))
            }
        })?,
        // iand_N
        Instr::I32And => stack.binop(|a: i32, b| a & b),
        Instr::I64And => stack.binop(|a: i64, b| a & b),
        // ior_N
        Instr::I32Or => stack.binop(|a: i32, b| a | b),
        Instr::I64Or => stack.binop(|a: i64, b| a | b),
        // ixor_N
        Instr::I32Xor => stack.binop(|a: i32, b| a ^ b),
        Instr::I64Xor => stack.binop(|a: i64, b| a ^ b),
        // ishl_N
        Instr::I32Shl => stack.binop(|a: i32, b| a.wrapping_shl(b as u32)),
        Instr::I64Shl => stack.binop(|a: i64, b| a.wrapping_shl(b as u32)),
        // ishr_u_N
        Instr::I32ShrU => stack.binop(|a: i32, b| (a as u32).wrapping_shr(b as u32) as i32),
        Instr::I64ShrU => stack.binop(|a: i64, b| (a as u64).wrapping_shr(b as u32) as i64),
        // ishr_s_N
        Instr::I32ShrS => stack.binop(|a: i32, b| a.wrapping_shr(b as u32)),
        Instr::I64ShrS => stack.binop(|a: i64, b| a.wrapping_shr(b as u32)),
        // irotl_N
        Instr::I32RotL => stack.binop(|a: i32, b| a.rotate_left(b as u32)),
        Instr::I64RotL => stack.binop(|a: i64, b| a.rotate_left(b as u32)),
        // irotr_N
        Instr::I32RotR => stack.binop(|a: i32, b| a.rotate_right(b as u32)),
        Instr::I64RotR => stack.binop(|a: i64, b| a.rotate_right(b as u32)),
        // iclz_N
        Instr::I32Clz => stack.unop(|v: i32| v.leading_zeros() as i32),
        Instr::I64Clz => stack.unop(|v: i64| v.leading_zeros() as i64),
        // ictz_N
        Instr::I32Ctz => stack.unop(|v: i32| v.trailing_zeros() as i32),
        Instr::I64Ctz => stack.unop(|v: i64| v.trailing_zeros() as i64),
        // ipopcnt_N
        Instr::I32Popcnt => stack.unop(|v: i32| v.count_ones() as i32),
        Instr::I64Popcnt => stack.unop(|v: i64| v.count_ones() as i64),
        // ieqz_N
        Instr::I32Eqz => stack.testop(|v: i32| if v == 0 { 1 } else { 0 }),
        Instr::I64Eqz => stack.testop(|v: i64| if v == 0 { 1 } else { 0 }),
        // ieq_N
        Instr::I32Eq => stack.relop(|a: i32, b| if a == b { 1 } else { 0 }),
        Instr::I64Eq => stack.relop(|a: i64, b| if a == b { 1 } else { 0 }),
        // ine_N
        Instr::I32Ne => stack.relop(|a: i32, b| if a != b { 1 } else { 0 }),
        Instr::I64Ne => stack.relop(|a: i64, b| if a != b { 1 } else { 0 }),
        // ilt_u_N
        Instr::I32LtU => stack.relop(|a: i32, b| if (a as u32) < b as u32 { 1 } else { 0 }),
        Instr::I64LtU => stack.relop(|a: i64, b| if (a as u64) < b as u64 { 1 } else { 0 }),
        // ilt_s_N
        Instr::I32LtS => stack.relop(|a: i32, b| if a < b { 1 } else { 0 }),
        Instr::I64LtS => stack.relop(|a: i64, b| if a < b { 1 } else { 0 }),
        // igt_u_N
        Instr::I32GtU => stack.relop(|a: i32, b| if a as u32 > b as u32 { 1 } else { 0 }),
        Instr::I64GtU => stack.relop(|a: i64, b| if a as u64 > b as u64 { 1 } else { 0 }),
        // igt_s_N
        Instr::I32GtS => stack.relop(|a: i32, b| if a > b { 1 } else { 0 }),
        Instr::I64GtS => stack.relop(|a: i64, b| if a > b { 1 } else { 0 }),
        // ile_u_N
        Instr::I32LeU => stack.relop(|a: i32, b| if a as u32 <= b as u32 { 1 } else { 0 }),
        Instr::I64LeU => stack.relop(|a: i64, b| if a as u64 <= b as u64 { 1 } else { 0 }),
        // ile_s_N
        Instr::I32LeS => stack.relop(|a: i32, b| if a <= b { 1 } else { 0 }),
        Instr::I64LeS => stack.relop(|a: i64, b| if a <= b { 1 } else { 0 }),
        // ige_u_N
        Instr::I32GeU => stack.relop(|a: i32, b| if a as u32 >= b as u32 { 1 } else { 0 }),
        Instr::I64GeU => stack.relop(|a: i64, b| if a as u64 >= b as u64 { 1 } else { 0 }),
        // ige_s_N
        Instr::I32GeS => stack.relop(|a: i32, b| if a >= b { 1 } else { 0 }),
        Instr::I64GeS => stack.relop(|a: i64, b| if a >= b { 1 } else { 0 }),
        // fadd_N
        Instr::F32Add => stack.binop(|a: f32, b| a + b),
        Instr::F64Add => stack.binop(|a: f64, b| a + b),
        // fsub_N
        Instr::F32Sub => stack.binop(|a: f32, b| a - b),
        Instr::F64Sub => stack.binop(|a: f64, b| a - b),
        // fmul_N
        Instr::F32Mul => stack.binop(|a: f32, b| a * b),
        Instr::F64Mul => stack.binop(|a: f64, b| a * b),
        // fdiv_N
        Instr::F32Div => stack.binop(|a: f32, b| a / b),
        Instr::F64Div => stack.binop(|a: f64, b| a / b),
        // fmin_N
        Instr::F32Min => stack.binop(|a: f32, b| {
            if a.is_nan() || b.is_nan() {
                f32::NAN
            } else {
                a.min(b)
            }
        }),
        Instr::F64Min => stack.binop(|a: f64, b| {
            if a.is_nan() || b.is_nan() {
                f64::NAN
            } else {
                a.min(b)
            }
        }),
        // fmax_N
        Instr::F32Max => stack.binop(|a: f32, b| {
            if a.is_nan() || b.is_nan() {
                f32::NAN
            } else {
                a.max(b)
            }
        }),
        Instr::F64Max => stack.binop(|a: f64, b| {
            if a.is_nan() || b.is_nan() {
                f64::NAN
            } else {
                a.max(b)
            }
        }),
        // fcopysign_N
        Instr::F32Copysign => stack.binop(|a: f32, b: f32| Float::copysign(a, b)),
        Instr::F64Copysign => stack.binop(|a: f64, b: f64| Float::copysign(a, b)),
        // fabs_N
        Instr::F32Abs => stack.unop(|f: f32| Float::abs(f)),
        Instr::F64Abs => stack.unop(|f: f64| Float::abs(f)),
        // fneg_N
        Instr::F32Neg => stack.unop(f32::neg),
        Instr::F64Neg => stack.unop(f64::neg),
        // fsqrt_N
        Instr::F32Sqrt => stack.unop(|f: f32| Float::sqrt(f)),
        Instr::F64Sqrt => stack.unop(|f: f64| Float::sqrt(f)),
        // fceil_N
        Instr::F32Ceil => stack.unop(|f: f32| Float::ceil(f)),
        Instr::F64Ceil => stack.unop(|f: f64| Float::ceil(f)),
        // ffloor_N
        Instr::F32Floor => stack.unop(|f: f32| Float::floor(f)),
        Instr::F64Floor => stack.unop(|f: f64| Float::floor(f)),
        // ftrunc_N
        Instr::F32Trunc => stack.unop(|f: f32| Float::trunc(f)),
        Instr::F64Trunc => stack.unop(|f: f64| Float::trunc(f)),
        // fnearest_N
        Instr::F32Nearest => stack.unop(|v: f32| {
            let fround = Float::round(v);
            if Float::abs(v - fround) == 0.5 && fround % 2.0 != 0.0 {
                v.trunc()
            } else {
                fround
            }
        }),
        Instr::F64Nearest => stack.unop(|v: f64| {
            let fround = Float::round(v);
            if Float::abs(v - fround) == 0.5 && fround % 2.0 != 0.0 {
                v.trunc()
            } else {
                fround
            }
        }),
        // feq_N
        Instr::F32Eq => stack.relop(|a: f32, b| if a == b { 1 } else { 0 }),
        Instr::F64Eq => stack.relop(|a: f64, b| if a == b { 1 } else { 0 }),
        // fne_N
        Instr::F32Ne => stack.relop(|a: f32, b| if a != b { 1 } else { 0 }),
        Instr::F64Ne => stack.relop(|a: f64, b| if a != b { 1 } else { 0 }),
        // flt_N
        Instr::F32Lt => stack.relop(|a: f32, b| if a < b { 1 } else { 0 }),
        Instr::F64Lt => stack.relop(|a: f64, b| if a < b { 1 } else { 0 }),
        // fgt_N
        Instr::F32Gt => stack.relop(|a: f32, b| if a > b { 1 } else { 0 }),
        Instr::F64Gt => stack.relop(|a: f64, b| if a > b { 1 } else { 0 }),
        // fle_N
        Instr::F32Le => stack.relop(|a: f32, b| if a <= b { 1 } else { 0 }),
        Instr::F64Le => stack.relop(|a: f64, b| if a <= b { 1 } else { 0 }),
        // fge_N
        Instr::F32Ge => stack.relop(|a: f32, b| if a >= b { 1 } else { 0 }),
        Instr::F64Ge => stack.relop(|a: f64, b| if a >= b { 1 } else { 0 }),

        // conversion, shrink or expand
        Instr::I64ExtendI32U => stack.cvtop(|v: i32| v as u32 as i64),
        Instr::I64ExtendI32S => stack.cvtop(|v: i32| v as i64),
        Instr::I32WrapI64 => stack.cvtop(|v: i64| v as i32),
        Instr::I32TruncF32U => stack.cvtop_trap(|v: f32| cast::f32_to_u32(v).map(|v| v as i32))?,
        Instr::I32TruncF64U => stack.cvtop_trap(|v: f64| cast::f64_to_u32(v).map(|v| v as i32))?,
        Instr::I64TruncF32U => stack.cvtop_trap(|v: f32| cast::f32_to_u64(v).map(|v| v as i64))?,
        Instr::I64TruncF64U => stack.cvtop_trap(|v: f64| cast::f64_to_u64(v).map(|v| v as i64))?,
        Instr::I32TruncF32S => stack.cvtop_trap(cast::f32_to_i32)?,
        Instr::I32TruncF64S => stack.cvtop_trap(cast::f64_to_i32)?,
        Instr::I64TruncF32S => stack.cvtop_trap(cast::f32_to_i64)?,
        Instr::I64TruncF64S => stack.cvtop_trap(cast::f64_to_i64)?,
        Instr::F64PromoteF32 => stack.cvtop(|v: f32| v as f64),
        Instr::F32DemoteF64 => stack.cvtop(|v: f64| v as f32),
        Instr::F32ConvertI32U => stack.cvtop(|v: i32| v as u32 as f32),
        Instr::F32ConvertI64U => stack.cvtop(|v: i64| v as u64 as f32),
        Instr::F64ConvertI32U => stack.cvtop(|v: i32| v as u32 as f64),
        Instr::F64ConvertI64U => stack.cvtop(|v: i64| v as u64 as f64),
        Instr::F32ConvertI32S => stack.cvtop(|v: i32| v as f32),
        Instr::F32ConvertI64S => stack.cvtop(|v: i64| v as f32),
        Instr::F64ConvertI32S => stack.cvtop(|v: i32| v as f64),
        Instr::F64ConvertI64S => stack.cvtop(|v: i64| v as f64),
        Instr::I32ReinterpretF32 => stack.cvtop(|v: f32| f32::to_bits(v).cast_signed()),
        Instr::I64ReinterpretF64 => stack.cvtop(|v: f64| f64::to_bits(v).cast_signed()),
        Instr::F32ReinterpretI32 => stack.cvtop(|v: i32| f32::from_bits(i32::cast_unsigned(v))),
        Instr::F64ReinterpretI64 => stack.cvtop(|v: i64| f64::from_bits(i64::cast_unsigned(v))),
        Instr::I32Extend8S => stack.unop(|v: i32| (v as i8) as i32),
        Instr::I32Extend16S => stack.unop(|v: i32| (v as i16) as i32),
        Instr::I64Extend8S => stack.unop(|v: i64| (v as i8) as i64),
        Instr::I64Extend16S => stack.unop(|v: i64| (v as i16) as i64),
        Instr::I64Extend32S => stack.unop(|v: i64| (v as i32) as i64),
        Instr::I32TruncSatF32S => stack.cvtop(|v: f32| cast::f32_to_i32_sat(v)),
        Instr::I32TruncSatF32U => stack.cvtop(|v: f32| cast::f32_to_u32_sat(v) as i32),
        Instr::I32TruncSatF64S => stack.cvtop(|v: f64| cast::f64_to_i32_sat(v)),
        Instr::I32TruncSatF64U => stack.cvtop(|v: f64| cast::f64_to_u32_sat(v) as i32),
        Instr::I64TruncSatF32S => stack.cvtop(|v: f32| cast::f32_to_i64_sat(v)),
        Instr::I64TruncSatF32U => stack.cvtop(|v: f32| cast::f32_to_u64_sat(v) as i64),
        Instr::I64TruncSatF64S => stack.cvtop(|v: f64| cast::f64_to_i64_sat(v)),
        Instr::I64TruncSatF64U => stack.cvtop(|v: f64| cast::f64_to_u64_sat(v) as i64),

        //////////////////////////
        // Pseudo Instructions ///
        //////////////////////////
        Instr::RJump(r) => return Ok(ExecState::Continue(*r + pc)),
        Instr::PopLabel => {
            stack.pop_label();
        }
    }
    Ok(ExecState::Continue(pc + 1))
}

pub fn unwind_stack(frame: &Frame, stack: &mut Stack) -> Option<usize> {
    let n = frame.n;
    let mut results: Vec<Value> = vec![];
    for _ in 0..n {
        results.push(stack.pop_value());
    }
    stack.values_unwind(frame.stack_offset);
    for _ in 0..n {
        stack.push_value(results.pop().unwrap());
    }
    stack.pop_frame();
    if stack.frames_len() == 0 {
        None
    } else {
        Some(frame.pc)
    }
}

pub fn attach(func: &FuncInst, stack: &mut Stack, pc: usize) -> Result<ExecState, Trap> {
    match func {
        FuncInst::HostFunc { name, functype } => {
            let mut local = vec![];
            for _ in 0..functype.0 .0.len() {
                local.push(stack.pop_value());
            }
            local.reverse();

            Ok(ExecState::EnvFunc {
                name: name.clone(),
                params: local,
            })
        }
        FuncInst::InnerFunc {
            instance_addr,
            functype,
            locals,
            start,
        } => {
            let mut local = vec![];
            for _ in 0..functype.0 .0.len() {
                local.push(stack.pop_value());
            }
            local.reverse();
            for val in locals.iter() {
                match val {
                    ValType::I32 => local.push(Value::I32(0)),
                    ValType::I64 => local.push(Value::I64(0)),
                    ValType::F32 => local.push(Value::F32(0.0)),
                    ValType::F64 => local.push(Value::F64(0.0)),
                    _ => todo!(),
                }
            }
            let new_frame = Frame {
                n: functype.1 .0.len(),
                instance_addr: *instance_addr,
                local,
                stack_offset: stack.values_len(),
                pc: pc + 1,
            };
            stack.push_frame(new_frame);
            Ok(ExecState::Continue(*start))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::step;
    use crate::{
        binary::Instr,
        exec::{
            runtime::Instance,
            stack::{Frame, Stack},
            store::Store,
            trap::Trap,
            value::Value,
        },
    };

    fn test_instr(
        instrs: &Vec<Instr>,
        stack: &mut Stack,
        store: &mut Store,
        instances: &mut Vec<Instance>,
    ) -> Result<(), Trap> {
        for pc in 0..instrs.len() {
            step(instances, instrs, pc, store, stack).map(|_| ())?;
        }
        Ok(())
    }

    fn default() -> (Stack, Store, Vec<Instance>) {
        let mut stack = Stack::new();
        stack.push_frame(Frame::default());
        (stack, Store::new(), vec![Instance::default()])
    }

    #[test]
    fn extend() {
        let (mut stack, mut store, mut instances) = default();
        let instrs = vec![Instr::I32Const(0b11111000000011111), Instr::I32Extend8S];
        test_instr(&instrs, &mut stack, &mut store, &mut instances).unwrap();
        assert_eq!(stack.values(), &vec![Value::I32(0b11111)]);
    }

    #[test]
    fn reinterpret() {
        let (mut stack, mut store, mut instances) = default();
        let instrs = vec![Instr::F32Const(-0.0), Instr::I32ReinterpretF32];
        test_instr(&instrs, &mut stack, &mut store, &mut instances).unwrap();
        assert_eq!(stack.values(), &vec![Value::I32(-2147483648)]);
    }
}
