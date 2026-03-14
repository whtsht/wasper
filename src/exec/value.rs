use super::runtime::Addr;

#[derive(Debug, Clone, Copy)]
pub enum Value {
    I32(i32),
    I64(i64),
    F32(f32),
    F64(f64),
    Ref(Ref),
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Value::I32(a), Value::I32(b)) => a == b,
            (Value::I64(a), Value::I64(b)) => a == b,
            (Value::F32(a), Value::F32(b)) => {
                (a.is_nan() && b.is_nan())
                    || (a.is_finite() && b.is_finite())
                    || (a.is_infinite() && b.is_infinite())
                    || a == b
            }
            (Value::F64(a), Value::F64(b)) => {
                (a.is_nan() && b.is_nan())
                    || (a.is_finite() && b.is_finite())
                    || (a.is_infinite() && b.is_infinite())
                    || a == b
            }
            (Value::Ref(a), Value::Ref(b)) => a == b,
            _ => false,
        }
    }
}

impl Eq for Value {}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Ref {
    Null,
    Func(Addr),
    Extern(Addr),
}

impl From<Value> for Ref {
    fn from(value: Value) -> Self {
        if let Value::Ref(value) = value {
            value
        } else {
            unreachable!()
        }
    }
}

impl Into<Value> for Ref {
    fn into(self) -> Value {
        Value::Ref(self)
    }
}

impl From<Value> for i32 {
    fn from(value: Value) -> Self {
        if let Value::I32(value) = value {
            value
        } else {
            unreachable!()
        }
    }
}

impl Into<Value> for i32 {
    fn into(self) -> Value {
        Value::I32(self)
    }
}

impl From<Value> for i64 {
    fn from(value: Value) -> Self {
        if let Value::I64(value) = value {
            value
        } else {
            unreachable!("{:?}", value)
        }
    }
}

impl Into<Value> for i64 {
    fn into(self) -> Value {
        Value::I64(self)
    }
}

impl From<Value> for f32 {
    fn from(value: Value) -> Self {
        if let Value::F32(value) = value {
            value
        } else {
            unreachable!()
        }
    }
}

impl Into<Value> for f32 {
    fn into(self) -> Value {
        Value::F32(self)
    }
}

impl From<Value> for f64 {
    fn from(value: Value) -> Self {
        if let Value::F64(value) = value {
            value
        } else {
            unreachable!()
        }
    }
}

impl Into<Value> for f64 {
    fn into(self) -> Value {
        Value::F64(self)
    }
}

pub trait LittleEndian {
    fn read(buf: &[u8], addr: usize) -> Self;
    fn write(buf: &mut [u8], addr: usize, v: Self);
}

fn read_bytes<'a, A>(buf: &'a [u8], addr: usize) -> A
where
    A: TryFrom<&'a [u8]>,
    A::Error: core::fmt::Debug,
{
    buf[addr..addr + core::mem::size_of::<A>()]
        .try_into()
        .expect("read bytes for value")
}

fn write_bytes(buf: &mut [u8], addr: usize, bytes: &[u8]) {
    for i in 0..bytes.len() {
        buf[addr + i] = bytes[i];
    }
}

macro_rules! impl_le_rw {
    ($t:ty) => {
        impl LittleEndian for $t {
            fn read(buf: &[u8], addr: usize) -> Self {
                <$t>::from_le_bytes(read_bytes(buf, addr))
            }
            fn write(buf: &mut [u8], addr: usize, v: Self) {
                write_bytes(buf, addr, &v.to_le_bytes());
            }
        }
    };
}

impl_le_rw!(i8);
impl_le_rw!(i16);
impl_le_rw!(i32);
impl_le_rw!(i64);
impl_le_rw!(u64);
impl_le_rw!(f32);
impl_le_rw!(f64);

impl LittleEndian for u8 {
    fn read(buf: &[u8], addr: usize) -> Self {
        buf[addr]
    }
    fn write(buf: &mut [u8], addr: usize, v: Self) {
        buf[addr] = v;
    }
}
impl_le_rw!(u16);
impl_le_rw!(u32);
