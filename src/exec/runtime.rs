#[cfg(not(feature = "std"))]
use crate::lib::*;

use super::env::Env;
use super::importer::Importer;
use super::instr::{attach, step};
use super::stack::Stack;
use super::store::{FuncInst, Store};
use super::trap::Trap;
use super::value::{Ref, Value};
use crate::binary::{Block, Export, Import};
use crate::binary::{ExportDesc, FuncType, ImportDesc, Instr, Module};
use crate::binary::{Expr, ValType};
use core::fmt::Debug;

pub type Addr = usize;
pub const PAGE_SIZE: usize = 65536;

#[derive(Debug, PartialEq, Eq)]
pub enum ExecState {
    Continue(usize),
    Return,
    EnvFunc { name: String, params: Vec<Value> },
}

#[derive(Debug, PartialEq, Default, Clone)]
pub struct Instance {
    pub globaladdrs: Vec<Addr>,
    pub tableaddrs: Vec<Addr>,
    // In the current version of WebAssembly, all memory instructions
    // implicitly operate on memory index 0. This restriction may be
    // lifted in future versions.
    pub memaddr: Option<Addr>,
    pub types: Vec<FuncType>,
    pub dataaddrs: Vec<Addr>,
    pub funcaddrs: Vec<Addr>,
    pub elemaddrs: Vec<Addr>,
    pub start: Option<usize>,
    pub exports: Vec<Export>,
}

impl Instance {
    pub fn block_to_arity(&self, bt: &Block) -> usize {
        match bt {
            Block::Empty => 0,
            Block::ValType(_) => 1,
            Block::TypeIdx(idx) => self.types[*idx as usize].1 .0.len(),
        }
    }
}

#[derive(Debug)]
pub struct Runtime {
    pub instrs: Vec<Instr>,
    pub instances: Vec<Instance>,
    pub root: usize,
    pub stack: Stack,
    pub pc: usize,
    pub env_name: &'static str,
}

#[derive(Debug, PartialEq, Eq)]
pub enum RuntimeError {
    ModuleNotFound(String),
    NotFound(ImportType),
    Env(&'static str),
    ConstantExpression,
    NoStartFunction,
    Trap(Trap),
}

#[derive(Debug, PartialEq, Eq)]
pub enum ImportType {
    Func(String),
    Table(String),
    Global(String),
    Mem,
}

pub fn eval_const(expr: &Expr) -> Result<Value, RuntimeError> {
    Ok(match expr.0[0] {
        Instr::I32Const(value) => Value::I32(value),
        Instr::I64Const(value) => Value::I64(value),
        Instr::F32Const(value) => Value::F32(value),
        Instr::F64Const(value) => Value::F64(value),
        Instr::RefNull(_) => Value::Ref(Ref::Null),
        Instr::RefFunc(idx) => Value::I32(idx as i32),
        _ => return Err(RuntimeError::ConstantExpression),
    })
}

impl Runtime {
    pub fn allocate_func(
        &mut self,
        functype: FuncType,
        locals: Vec<ValType>,
        instrs: Vec<Instr>,
        instance_addr: Addr,
        store: &mut Store,
    ) -> Addr {
        let start = self.instrs.len();
        self.instrs.extend(instrs);
        self.instrs.extend(vec![Instr::Return]);
        store.funcs.push(FuncInst::InnerFunc {
            instance_addr,
            start,
            functype,
            locals,
        })
    }

    pub fn instances(self) -> Vec<Instance> {
        self.instances
    }

    pub fn new(env_name: &'static str) -> Self {
        Runtime {
            root: 0,
            instrs: vec![],
            instances: vec![],
            stack: Stack::new(),
            pc: 0,
            env_name,
        }
    }

    pub fn add_module(&mut self, store: &mut Store, module: Module) -> Result<(), RuntimeError> {
        struct EmptyImporter {}
        impl Importer for EmptyImporter {
            fn import(&mut self, _: &str) -> Option<Module> {
                panic!()
            }
        }

        let mut importer = EmptyImporter {};
        let instance = self.new_instance(store, module, &mut importer)?;

        self.instances.push(instance);

        self.root = self.instances.len() - 1;
        Ok(())
    }

    pub fn set_pc(&mut self, pc: usize) {
        self.pc = pc;
    }

    pub fn inc_pc(&mut self) {
        self.pc += 1;
    }

    pub fn import_module<I: Importer>(
        &mut self,
        store: &mut Store,
        importer: &mut I,
        modname: &str,
    ) -> Result<(), RuntimeError> {
        let module = importer
            .import(modname)
            .ok_or(RuntimeError::ModuleNotFound(modname.into()))?;
        let instance = self.new_instance(store, module, importer)?;

        self.instances.push(instance);

        self.root = self.instances.len() - 1;
        Ok(())
    }

    fn new_instance<I: Importer>(
        &mut self,
        store: &mut Store,
        module: Module,
        importer: &mut I,
    ) -> Result<Instance, RuntimeError> {
        let mut funcaddrs = vec![];
        let mut globaladdrs = vec![];
        let mut tableaddrs = vec![];
        let mut memaddr = None;

        for import in module.imports {
            if import.module == self.env_name {
                match import.desc {
                    ImportDesc::Func(ty) => funcaddrs.push(self.import_env_func(
                        store,
                        module.types[ty as usize].clone(),
                        import.name,
                    )),
                    ImportDesc::Table(_) => {}
                    ImportDesc::Mem(_) => {}
                    ImportDesc::Global(_) => {}
                }
            } else {
                match import.desc {
                    ImportDesc::Func(_) => {
                        funcaddrs.push(self.import_func(store, &import, importer)?)
                    }
                    ImportDesc::Mem(_) => {
                        memaddr = Some(self.import_memory(store, &import, importer)?)
                    }
                    ImportDesc::Table(_) => {
                        tableaddrs.push(self.import_table(store, &import, importer)?)
                    }
                    ImportDesc::Global(_) => {
                        globaladdrs.push(self.import_global(store, &import, importer)?)
                    }
                }
            }
        }

        for global in module.globals {
            globaladdrs.push(store.allocate_global(global)?);
        }

        for table in module.tables {
            tableaddrs.push(store.allocate_table(table));
        }

        let mut elemaddrs = vec![];
        for elem in module.elems {
            if let Some(addr) = store.allocate_elem(elem)? {
                elemaddrs.push(addr);
            }
        }

        let mut inner_funcaddr = vec![];
        for func in module.funcs {
            let functype = module.types[func.typeidx as usize].clone();
            let addr = self.allocate_func(
                functype,
                func.locals,
                func.body.0,
                self.instances.len(),
                store,
            );
            inner_funcaddr.push(addr);
            funcaddrs.push(addr);
        }
        let instance_addr = self.instances.len();
        store.update_func_inst(&inner_funcaddr, instance_addr);

        if module.mems.len() > 0 {
            memaddr = Some(store.allocate_mem(&module.mems[0]))
        }

        let mut dataaddrs = vec![];
        for data in module.datas {
            let memidx = memaddr.unwrap();
            if let Some(addr) = store.allocate_data(memidx, data)? {
                dataaddrs.push(addr);
            }
        }

        Ok(Instance {
            funcaddrs,
            types: module.types,
            globaladdrs,
            tableaddrs,
            elemaddrs,
            memaddr,
            dataaddrs,
            start: module.start.map(|idx| idx as usize),
            exports: module.exports,
        })
    }

    pub fn import_env_func(&mut self, store: &mut Store, functype: FuncType, name: String) -> Addr {
        store.funcs.push(FuncInst::HostFunc { functype, name })
    }

    pub fn import_func<I: Importer>(
        &mut self,
        store: &mut Store,
        import: &Import,
        importer: &mut I,
    ) -> Result<usize, RuntimeError> {
        let module = importer
            .import(&import.module)
            .ok_or_else(|| RuntimeError::ModuleNotFound(import.module.clone()))?;
        let instance = self.new_instance(store, module, importer)?;
        if let Some(desc) = instance
            .exports
            .iter()
            .filter(|export| export.name == import.name)
            .map(|export| &export.desc)
            .next()
        {
            if let ExportDesc::Func(index) = desc {
                let ret = Ok(instance.funcaddrs[*index as usize]);
                self.instances.push(instance);
                return ret;
            }
        }
        Err(RuntimeError::NotFound(ImportType::Func(
            import.name.clone(),
        )))
    }

    pub fn import_memory<I: Importer>(
        &mut self,
        store: &mut Store,
        import: &Import,
        importer: &mut I,
    ) -> Result<Addr, RuntimeError> {
        let module = importer
            .import(&import.module)
            .ok_or_else(|| RuntimeError::ModuleNotFound(import.module.clone()))?;
        let instance = self.new_instance(store, module, importer)?;
        if let Some(desc) = instance
            .exports
            .iter()
            .filter(|e| e.name == import.name)
            .map(|export| &export.desc)
            .next()
        {
            if let ExportDesc::Mem(_) = desc {
                if let Some(addr) = instance.memaddr {
                    self.instances.push(instance);
                    return Ok(addr);
                }
            }
        }
        Err(RuntimeError::NotFound(ImportType::Mem))
    }

    pub fn import_table<I: Importer>(
        &mut self,
        store: &mut Store,
        import: &Import,
        importer: &mut I,
    ) -> Result<Addr, RuntimeError> {
        let module = importer
            .import(&import.module)
            .ok_or_else(|| RuntimeError::ModuleNotFound(import.module.clone()))?;
        let instance = self.new_instance(store, module, importer)?;
        if let Some(desc) = instance
            .exports
            .iter()
            .filter(|export| export.name == import.name)
            .map(|export| &export.desc)
            .next()
        {
            if let ExportDesc::Table(addr) = desc {
                let ret = Ok(instance.tableaddrs[*addr as usize]);
                self.instances.push(instance);
                return ret;
            }
        }
        Err(RuntimeError::NotFound(ImportType::Table(
            import.name.clone(),
        )))
    }

    pub fn import_global<I: Importer>(
        &mut self,
        store: &mut Store,
        import: &Import,
        importer: &mut I,
    ) -> Result<Addr, RuntimeError> {
        let module = importer
            .import(&import.module)
            .ok_or_else(|| RuntimeError::ModuleNotFound(import.module.clone()))?;
        let instance = self.new_instance(store, module, importer)?;
        if let Some(desc) = instance
            .exports
            .iter()
            .filter(|export| export.name == import.name)
            .map(|export| &export.desc)
            .next()
        {
            if let ExportDesc::Global(addr) = desc {
                let ret = Ok(instance.globaladdrs[*addr as usize]);
                self.instances.push(instance);
                return ret;
            }
        }
        Err(RuntimeError::NotFound(ImportType::Global(
            import.name.clone(),
        )))
    }

    pub fn start<E: Env>(&mut self, store: &mut Store, env: &mut E) -> Result<(), RuntimeError> {
        match self.attach_start(store)? {
            ExecState::Continue(pc) => {
                self.pc = pc;
                self.exec(store, env)
                    .map_err(|trap| RuntimeError::Trap(trap))?;
            }
            ExecState::EnvFunc { name, params } => {
                let instance = &self.instances[self.root];
                let memory = instance.memaddr.map(|a| &mut store.mems[a]);
                env.call(&name, params, memory)
                    .map_err(|err| RuntimeError::Env(err))?;
            }
            _ => {}
        }
        Ok(())
    }

    pub fn invoke<E: Env>(
        &mut self,
        store: &mut Store,
        env: &mut E,
        name: &str,
        params: Vec<Value>,
    ) -> Result<Vec<Value>, RuntimeError> {
        match self.attach_invoke(store, name, params)? {
            ExecState::Continue(pc) => {
                self.pc = pc;
                self.exec(store, env)
                    .map_err(|trap| RuntimeError::Trap(trap))
            }
            ExecState::Return => unreachable!(),
            ExecState::EnvFunc { name, params } => {
                let instance = &self.instances[self.root];
                let memory = instance.memaddr.map(|a| &mut store.mems[a]);
                env.call(&name, params, memory)
                    .map_err(|err| RuntimeError::Env(err))
            }
        }
    }

    fn attach(
        func: &FuncInst,
        stack: &mut Stack,
        pc: &mut usize,
    ) -> Result<ExecState, RuntimeError> {
        match attach(func, stack, *pc).map_err(|trap| RuntimeError::Trap(trap)) {
            Ok(state) => {
                if let ExecState::Continue(start) = state {
                    *pc = start;
                    Ok(state)
                } else {
                    Ok(state)
                }
            }
            Err(err) => Err(err),
        }
    }

    pub fn attach_start(&mut self, store: &mut Store) -> Result<ExecState, RuntimeError> {
        let instance = &self.instances[self.root];
        self.stack = Stack::new();
        if let Some(index) = instance.start {
            let func = &store.funcs[index];
            Self::attach(func, &mut self.stack, &mut self.pc)
        } else {
            Err(RuntimeError::NoStartFunction)
        }
    }

    pub fn attach_invoke(
        &mut self,
        store: &mut Store,
        name: &str,
        params: Vec<Value>,
    ) -> Result<ExecState, RuntimeError> {
        let instance = &self.instances[self.root];
        self.stack = Stack::new();
        if let Some(export) = instance
            .exports
            .iter()
            .filter(|export| &export.name == name)
            .next()
        {
            match export.desc {
                ExportDesc::Func(index) => {
                    let func = &store.funcs[instance.funcaddrs[index as usize]];
                    self.stack.extend_values(params);
                    Self::attach(func, &mut self.stack, &mut self.pc)
                }
                _ => Err(RuntimeError::NotFound(ImportType::Func(name.into()))),
            }
        } else {
            Err(RuntimeError::NotFound(ImportType::Func(name.into())))
        }
    }

    fn exec<E: Env>(&mut self, store: &mut Store, env: &mut E) -> Result<Vec<Value>, Trap> {
        loop {
            match step(
                &mut self.instances,
                &self.instrs,
                self.pc,
                store,
                &mut self.stack,
            )? {
                ExecState::Continue(pc) => {
                    self.pc = pc;
                }
                ExecState::Return => break,
                ExecState::EnvFunc { params, name } => {
                    let instance = &self.instances[self.root];
                    let memory = instance.memaddr.map(|a| &mut store.mems[a]);
                    let results = env
                        .call(&name, params, memory)
                        .map_err(|err| Trap::Env(err))?;
                    for result in results {
                        self.stack.push_value(result);
                    }
                    self.pc += 1;
                }
            }
        }
        Ok(self.stack.get_returns())
    }

    pub fn step(&mut self, store: &mut Store) -> Result<ExecState, Trap> {
        match step(
            &mut self.instances,
            &self.instrs,
            self.pc,
            store,
            &mut self.stack,
        ) {
            Ok(state) => {
                if let ExecState::Continue(next) = state {
                    self.pc = next;
                    Ok(state)
                } else if let ExecState::EnvFunc { .. } = state {
                    self.pc += 1;
                    Ok(state)
                } else {
                    Ok(state)
                }
            }
            Err(err) => Err(err),
        }
    }

    pub fn set_results(&mut self, results: Vec<Value>) {
        self.stack.extend_values(results);
    }
}

#[cfg(test)]
mod tests {
    use super::Runtime;
    use crate::binary::Module;
    use crate::exec::env::DebugEnv;
    use crate::exec::importer::Importer;
    use crate::exec::store::Store;
    use crate::exec::value::Value;
    use crate::loader::parser::Parser;
    use crate::tests::wat2wasm;

    #[test]
    fn store() {
        let wasm = wat2wasm(
            r#"(module
                  (memory 1)
                  (global $x (mut i32) (i32.const -12))
                  (table 2 funcref)
                  (func $f1 (result i32) i32.const 42)
                  (func $f2 (result i32) i32.const 13)
                  (elem (i32.const 0) $f1 $f2)
                  (data (i32.const 0) "hello world\n")

                  (func (export "main") (result i32)
                      i32.const 3
                  )
                  )"#,
        )
        .unwrap();
        let mut parser = Parser::new(&wasm);

        #[derive(Debug)]
        struct TestImporter {
            module: Module,
        }
        impl Importer for TestImporter {
            fn import(&mut self, modname: &str) -> Option<crate::binary::Module> {
                if modname == "debug" {
                    Some(self.module.clone())
                } else {
                    None
                }
            }
        }
        let mut store = Store::new();

        let module = parser.module().unwrap();
        let mut impoter = TestImporter { module };
        let mut runtime = Runtime::new("env");
        runtime
            .import_module(&mut store, &mut impoter, "debug")
            .unwrap();
        let mut env = DebugEnv {};
        assert_eq!(
            runtime.invoke(&mut store, &mut env, "main", vec![]),
            Ok(vec![Value::I32(3)])
        );
        store.free_runtime(runtime);
        assert_eq!(store.funcs.to_vec().len(), 0);
        assert_eq!(store.elems.to_vec().len(), 0);
        assert_eq!(store.datas.to_vec().len(), 0);
        assert_eq!(store.globals.to_vec().len(), 0);
        assert_eq!(store.mems.to_vec().len(), 0);
        assert_eq!(store.tables.to_vec().len(), 0);
    }
}
