use crate::binary::Expr;
use crate::binary::GlobalType;
#[cfg(not(feature = "std"))]
use crate::lib::*;

use super::host_env::DebugHostEnv;
use super::host_env::HostEnv;
use super::importer::DefaultImporter;
use super::importer::Importer;
use super::stack::{Frame, Label, Stack, Value};
use super::trap::Trap;
use crate::binary::{Block, Export};
use crate::binary::{ExportDesc, Func, FuncType, ImportDesc, Instr, Module};

pub type Addr = usize;

pub const HOST_MODULE: &str = "__env";

#[derive(Debug)]
pub enum ExecState {
    Breaking(u32),
    Continue,
    Return,
}

#[derive(Debug, PartialEq, Default, Clone)]
pub struct Instance {
    funcaddrs: Vec<Addr>,
    globaladdrs: Vec<Addr>,
    types: Vec<FuncType>,
    start: Option<usize>,
    exports: Vec<Export>,
    stack: Stack,
}

impl Instance {
    pub fn binary_op<F: Fn(T, T) -> T, T: From<Value> + Into<Value>>(&mut self, func: F) {
        let lhs = self.stack.pop_value::<T>();
        let rhs = self.stack.pop_value::<T>();
        self.stack.push_value(func(lhs, rhs));
    }

    pub fn block_to_arity(&self, bt: &Block) -> usize {
        match bt {
            Block::Empty => 0,
            Block::ValType(_) => 1,
            Block::TypeIdx(idx) => self.types[*idx as usize].1 .0.len(),
        }
    }

    pub fn jump(&mut self, l: usize) {
        let label = self.stack.th_label(l);
        let mut values: Vec<Value> = vec![];
        for _ in 0..label.n {
            values.push(self.stack.pop_value());
        }

        let len = self.stack.values_len() - label.offset;
        for _ in 0..len {
            self.stack.pop_value::<Value>();
        }

        for _ in 0..=l {
            self.stack.pop_label();
        }

        for value in values.into_iter().rev() {
            self.stack.push_value(value);
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum FuncInst {
    InnerFunc {
        functype: FuncType,
        instance_addr: Addr,
        func: Func,
    },
    HostFunc {
        functype: FuncType,
        name: String,
    },
}

#[derive(Debug, PartialEq, Clone)]
pub struct GlobalInst {
    pub globaltype: GlobalType,
    pub value: Value,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Store {
    funcs: Vec<FuncInst>,
    globals: Vec<GlobalInst>,
}

pub trait Allocatable {
    fn allocate(store: &mut Store, value: Self) -> Addr;
}

impl Allocatable for FuncInst {
    fn allocate(store: &mut Store, value: Self) -> Addr {
        store.funcs.push(value);
        store.funcs.len() - 1
    }
}

impl Allocatable for GlobalInst {
    fn allocate(store: &mut Store, value: Self) -> Addr {
        store.globals.push(value);
        store.globals.len() - 1
    }
}

impl Store {
    pub fn new() -> Self {
        Self {
            funcs: vec![],
            globals: vec![],
        }
    }

    pub fn update_func_inst(&mut self, funcaddrs: Vec<Addr>, instance_addr: Addr) {
        for funcaddr in funcaddrs {
            match &mut self.funcs[funcaddr as usize] {
                FuncInst::InnerFunc {
                    instance_addr: addr,
                    ..
                } => {
                    *addr = instance_addr;
                }
                _ => {}
            }
        }
    }

    pub fn allocate<T: Allocatable>(&mut self, value: T) -> Addr {
        Allocatable::allocate(self, value)
    }
}

use core::fmt::Debug;
#[derive(Debug)]
pub struct Runtime<E: HostEnv + Debug, I: Importer + Debug> {
    root: usize,
    instances: Vec<Instance>,
    store: Store,
    importer: I,
    env: E,
}

#[derive(Debug)]
pub enum RuntimeError {
    ModuleNotFound,
    ConstantExpression,
    Trap(Trap),
}

#[cfg(feature = "std")]
pub fn debug_runtime(
    module: Module,
) -> Result<Runtime<DebugHostEnv, DefaultImporter>, RuntimeError> {
    let mut runtime = Runtime {
        root: 0,
        instances: vec![],
        store: Store::new(),
        importer: DefaultImporter::new(),
        env: DebugHostEnv {},
    };

    let instance = runtime.new_instance(module)?;
    runtime.instances.push(instance);

    Ok(runtime)
}

pub fn eval_const(expr: Expr) -> Result<Value, RuntimeError> {
    Ok(match expr.0[0] {
        Instr::I32Const(value) => Value::I32(value),
        Instr::I64Const(value) => Value::I64(value),
        Instr::F32Const(value) => Value::F32(value),
        Instr::F64Const(value) => Value::F64(value),
        _ => return Err(RuntimeError::ConstantExpression),
    })
}

impl<E: HostEnv + Debug, I: Importer + Debug> Runtime<E, I> {
    pub fn new(importer: I, env: E, module: Module) -> Result<Self, RuntimeError> {
        let mut runtime = Runtime {
            root: 0,
            instances: vec![],
            store: Store::new(),
            importer,
            env,
        };

        let instance = runtime.new_instance(module)?;

        runtime.instances.push(instance);

        runtime.root = runtime.instances.len() - 1;

        Ok(runtime)
    }

    pub fn new_instance(&mut self, module: Module) -> Result<Instance, RuntimeError> {
        let mut funcaddrs = vec![];

        for import in module.imports {
            match import.desc {
                ImportDesc::TypeIdx(idx) => match import.module.as_str() {
                    HOST_MODULE => {
                        let addr = self.store.allocate(FuncInst::HostFunc {
                            functype: module.types[idx as usize].clone(),
                            name: import.name,
                        });
                        funcaddrs.push(addr);
                    }
                    modname => funcaddrs.push(self.get_func_addr(modname, &import.name)?),
                },
                _ => {}
            }
        }

        let mut globaladdrs = vec![];
        for global in module.globals {
            globaladdrs.push(self.store.allocate(GlobalInst {
                globaltype: global.type_,
                value: eval_const(global.value)?,
            }));
        }

        let mut inner_funcaddr = vec![];
        for func in module.funcs {
            let addr = self.store.allocate(FuncInst::InnerFunc {
                functype: module.types[func.typeidx as usize].clone(),
                instance_addr: self.instances.len(),
                func,
            });
            inner_funcaddr.push(addr);
            funcaddrs.push(addr);
        }

        let instance_addr = self.instances.len();
        self.store.update_func_inst(inner_funcaddr, instance_addr);

        Ok(Instance {
            funcaddrs,
            globaladdrs,
            types: module.types,
            start: module.start.map(|idx| idx as usize),
            exports: module.exports,
            stack: Stack::new(),
        })
    }

    pub fn get_func_addr(&mut self, modname: &str, funcname: &str) -> Result<usize, RuntimeError> {
        let module = self
            .importer
            .import(modname)
            .ok_or_else(|| RuntimeError::ModuleNotFound)?;
        let instance = self.new_instance(module)?;
        if let Some(desc) = instance
            .exports
            .iter()
            .filter(|export| export.name == funcname)
            .map(|export| &export.desc)
            .next()
        {
            if let ExportDesc::Func(index) = desc {
                let ret = Ok(instance.funcaddrs[*index as usize]);
                self.instances.push(instance);
                return ret;
            } else {
                panic!("expected function, found {:?}", desc);
            }
        } else {
            panic!("a function named {}.{} was not found", modname, funcname)
        }
    }

    pub fn start(&mut self) {
        if let Some(index) = self.instances[self.root].start {
            match self.store.funcs[index].clone() {
                FuncInst::HostFunc { name, .. } => {
                    self.env.call(&name, &mut self.instances[self.root].stack)
                }
                FuncInst::InnerFunc { func, .. } => {
                    let mut frame = Frame {
                        instance_addr: self.root,
                        local: vec![],
                    };

                    match exec(
                        &mut self.env,
                        &mut self.instances,
                        &mut self.store,
                        &func.body.0,
                        &mut frame,
                    ) {
                        Ok(_) => {}
                        Err(trap) => println!("RuntimeError: {}", trap),
                    }
                }
            }
        }
    }

    pub fn invoke(&mut self, name: &str, params: Vec<Value>) -> Result<Vec<Value>, Trap> {
        if let Some(export) = self.instances[self.root]
            .exports
            .iter()
            .filter(|export| &export.name == name)
            .next()
        {
            if let ExportDesc::Func(index) = export.desc {
                match self.store.funcs[self.instances[self.root].funcaddrs[index as usize]].clone()
                {
                    FuncInst::HostFunc { name, .. } => {
                        self.env.call(&name, &mut self.instances[self.root].stack)
                    }
                    FuncInst::InnerFunc { func, .. } => {
                        let mut frame = Frame {
                            instance_addr: self.root,
                            local: params,
                        };
                        exec(
                            &mut self.env,
                            &mut self.instances,
                            &mut self.store,
                            &func.body.0,
                            &mut frame,
                        )?;
                    }
                }
                Ok(self.instances[self.root].stack.get_returns())
            } else {
                panic!("Error: {} is not a function", name);
            }
        } else {
            panic!("Error: A function named {} was not found", name);
        }
    }
}

pub fn exec<E: HostEnv + Debug>(
    env: &mut E,
    instances: &mut Vec<Instance>,
    store: &mut Store,
    instrs: &Vec<Instr>,
    frame: &mut Frame,
) -> Result<ExecState, Trap> {
    let mut next = 0;
    loop {
        if next >= instrs.len() {
            return Ok(ExecState::Return);
        }
        match step(env, instances, &instrs[next], frame, store)? {
            ExecState::Continue => {}
            ret => return Ok(ret),
        }
        next += 1;
    }
}

pub fn step<E: HostEnv + Debug>(
    env: &mut E,
    instances: &mut Vec<Instance>,
    instr: &Instr,
    frame: &mut Frame,
    store: &mut Store,
) -> Result<ExecState, Trap> {
    let instance = &mut instances[frame.instance_addr];
    match instr {
        Instr::I32Const(a) => instance.stack.push_value(*a),
        Instr::I32Add => instance.binary_op(|a: i32, b: i32| a + b),
        Instr::Nop => {}
        Instr::Unreachable => return Err(Trap::Unreachable),
        Instr::Block { in1, bt } => {
            instance.stack.push_label(Label {
                n: instance.block_to_arity(bt),
                offset: instance.stack.values_len(),
            });
            match exec(env, instances, store, in1, frame)? {
                ExecState::Breaking(l) if l > 0 => return Ok(ExecState::Breaking(l - 1)),
                _ => {}
            }
        }
        Instr::Loop { in1, .. } => loop {
            match exec(env, instances, store, in1, frame)? {
                ExecState::Breaking(l) if l > 0 => return Ok(ExecState::Breaking(l - 1)),
                ExecState::Return => return Ok(ExecState::Return),
                _ => {}
            }
        },
        Instr::If { in1, in2, .. } => {
            let c = instance.stack.pop_value::<i32>();
            if c != 0 {
                match exec(env, instances, store, in1, frame)? {
                    ExecState::Breaking(l) if l > 0 => return Ok(ExecState::Breaking(l - 1)),
                    ExecState::Return => return Ok(ExecState::Return),
                    _ => {}
                }
            } else if let Some(in2) = in2 {
                match exec(env, instances, store, in2, frame)? {
                    ExecState::Breaking(l) if l > 0 => {
                        return Ok(ExecState::Breaking(l - 1));
                    }
                    ExecState::Return => return Ok(ExecState::Return),
                    _ => {}
                }
            }
        }
        Instr::Br(l) => {
            instance.jump(*l as usize);
            return Ok(ExecState::Breaking(*l));
        }
        Instr::BrIf(l) => {
            let c = instance.stack.pop_value::<i32>();
            if c != 0 {
                instance.jump(*l as usize);
                return Ok(ExecState::Breaking(*l));
            }
        }
        Instr::BrTable { indexs, default } => {
            let i = instance.stack.pop_value::<i32>() as usize;
            return if i <= indexs.len() {
                instance.jump(indexs[i] as usize);
                Ok(ExecState::Breaking(indexs[i]))
            } else {
                instance.jump(*default as usize);
                Ok(ExecState::Breaking(*default))
            };
        }
        Instr::Return => return Ok(ExecState::Return),
        Instr::Call(a) => {
            let func = store.funcs[*a as usize].clone();
            match func {
                FuncInst::HostFunc { name, .. } => {
                    env.call(name.as_str(), &mut instance.stack);
                }
                FuncInst::InnerFunc {
                    functype,
                    instance_addr,
                    func,
                } => {
                    let mut local = vec![];
                    for _ in 0..functype.0 .0.len() {
                        local.push(instance.stack.pop_value());
                    }
                    let mut new_frame = Frame {
                        instance_addr,
                        local,
                    };
                    exec(env, instances, store, &func.body.0, &mut new_frame)?;

                    if frame.instance_addr != new_frame.instance_addr {
                        unsafe {
                            let origin_instance =
                                core::ptr::addr_of_mut!(instances[frame.instance_addr]);
                            let derived_instance =
                                core::ptr::addr_of_mut!(instances[new_frame.instance_addr]);
                            for result in (*derived_instance).stack.get_returns() {
                                (*origin_instance).stack.push_value(result)
                            }
                        }
                    }
                }
            }
        }
        Instr::LocalGet(l) => {
            let value = frame.local[*l as usize];
            instance.stack.push_value(value);
        }
        Instr::GlobalGet(i) => {
            let globalindex = instance.globaladdrs[*i as usize];
            instance.stack.push_value(store.globals[globalindex].value);
        }
        Instr::GlobalSet(i) => {
            let value = instance.stack.pop_value();
            let globalindex = instance.globaladdrs[*i as usize];
            store.globals[globalindex].value = value;
        }
        _ => return Err(Trap::NotImplemented),
    }
    Ok(ExecState::Continue)
}

#[cfg(test)]
mod tests {
    use super::{Runtime, HOST_MODULE};
    use crate::exec::host_env::DebugHostEnv;
    use crate::exec::importer::DefaultImporter;
    use crate::exec::runtime::debug_runtime;
    use crate::exec::stack::Value;
    use crate::loader::parser::Parser;
    use crate::tests::wat2wasm;

    #[test]
    fn simple() {
        let wasm = wat2wasm(format!(
            r#"(module
                       (import "{}" "start" (func $start))
                       (start $start)
                   )"#,
            HOST_MODULE
        ))
        .unwrap();
        let mut parser = Parser::new(&wasm);
        let module = parser.module().unwrap();
        let mut runtime = debug_runtime(module).unwrap();
        runtime.start();
    }

    #[test]
    fn instr() {
        let wasm = wat2wasm(
            r#"(module
                       (func (export "main") (result i32)
                           i32.const 10
                           i32.const 20
                           i32.add
                       )
                 )"#,
        )
        .unwrap();
        let mut parser = Parser::new(&wasm);
        let module = parser.module().unwrap();
        let mut runtime = debug_runtime(module).unwrap();
        assert_eq!(runtime.invoke("main", vec![]), Ok(vec![Value::I32(30)]))
    }

    #[test]
    fn branch() {
        let wasm = wat2wasm(
            r#"(module
                        (func (export "main") (result i32 i32 i32)
                            (block (result i32 i32 i32)
                                i32.const 0
                                (block (result i32 i32)
                                    i32.const 1
                                    (block (param i32) (result i32)
                                        i32.const 2
                                        i32.add
                                        i32.const 5
                                        i32.const 6
                                        br 2
                                    )
                                    i32.const 10
                                )
                             )
                        )
                    )"#,
        )
        .unwrap();
        let mut parser = Parser::new(&wasm);
        let module = parser.module().unwrap();
        let mut runtime = debug_runtime(module).unwrap();
        assert_eq!(
            runtime.invoke("main", vec![]),
            Ok(vec![Value::I32(3), Value::I32(5), Value::I32(6)])
        );
    }

    #[test]
    fn call_func() {
        let wasm = wat2wasm(
            r#"(module
                    (func $triple (result i32 i32 i32)
                        (block (result i32 i32 i32)
                            i32.const 0
                            (block (result i32 i32)
                                i32.const 1
                                (block (param i32) (result i32)
                                    i32.const 2
                                    i32.add
                                    i32.const 5
                                    i32.const 6
                                    br 2
                                )
                                i32.const 10
                            )
                        )
                    )
                    (func (export "main") (result i32 i32 i32 i32 i32 i32)
                         (block (result i32 i32 i32)
                            i32.const 0
                            (block (result i32 i32)
                                i32.const 1
                                (block (param i32) (result i32)
                                    call $triple
                                    i32.add
                                    br 2
                                )
                                i32.const 10
                            )
                        )
                        call $triple
                    )
            )"#,
        )
        .unwrap();

        let mut parser = Parser::new(&wasm);
        let module = parser.module().unwrap();
        let mut runtime = debug_runtime(module).unwrap();
        assert_eq!(
            runtime.invoke("main", vec![]),
            Ok(vec![
                Value::I32(1),
                Value::I32(3),
                Value::I32(11),
                Value::I32(3),
                Value::I32(5),
                Value::I32(6)
            ])
        );
    }

    #[test]
    fn extern_module() {
        let math = Parser::new(
            &wat2wasm(
                r#"(module
                            (func (export "add") (param i32 i32) (result i32)
                                local.get 0
                                local.get 1
                                i32.add
                            )
                        )"#,
            )
            .unwrap(),
        )
        .module()
        .unwrap();

        let main = Parser::new(
            &wat2wasm(
                r#"(module
                            (import "math" "add" (func $add (param i32 i32) (result i32)))
                            (func (export "main") (result i32)
                                i32.const 2
                                i32.const 4
                                call $add
                            )
                        )"#,
            )
            .unwrap(),
        )
        .module()
        .unwrap();

        let mut importer = DefaultImporter::new();
        importer.add_module(math, "math");

        let mut runtime = Runtime::new(importer, DebugHostEnv {}, main).unwrap();

        assert_eq!(runtime.invoke("main", vec![]), Ok(vec![Value::I32(6)]));
    }

    #[test]
    fn global_module() {
        let inc = Parser::new(
            &wat2wasm(
                r#"(module
                        (global $v (mut i32) (i32.const 0))
                        (func (export "inc") (result i32)
                            global.get $v
                            i32.const 1
                            i32.add
                            global.set $v
                            global.get $v
                        )
                    )"#,
            )
            .unwrap(),
        )
        .module()
        .unwrap();

        let main = Parser::new(
            &wat2wasm(
                r#"(module
                        (import "inc" "inc" (func $inc (result i32)))
                        (func (export "main") (result i32 i32 i32 i32 i32)
                             call $inc
                             call $inc
                             call $inc
                             call $inc
                             call $inc
                        )
                    )"#,
            )
            .unwrap(),
        )
        .module()
        .unwrap();

        let mut importer = DefaultImporter::new();
        importer.add_module(inc, "inc");

        let mut runtime = Runtime::new(importer, DebugHostEnv {}, main).unwrap();
        assert_eq!(
            runtime.invoke("main", vec![]),
            Ok(vec![
                Value::I32(1),
                Value::I32(2),
                Value::I32(3),
                Value::I32(4),
                Value::I32(5)
            ])
        );
    }
}
