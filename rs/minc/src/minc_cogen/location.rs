#[allow(dead_code)]
#[derive(Copy, Clone, PartialEq)]
/// Registers in x86-64.
pub enum Register {
    RAX,
    RBX,
    RCX,
    RDX,
    RDI,
    RSI,
    RBP,
    R8,
    R9,
    R10,
    R11,
    R12,
    R13,
    R14,
    R15,
}

// Display for Register
impl std::fmt::Display for Register {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Register::RAX => write!(f, "%rax"),
            Register::RBX => write!(f, "%rbx"),
            Register::RCX => write!(f, "%rcx"),
            Register::RDX => write!(f, "%rdx"),
            Register::RDI => write!(f, "%rdi"),
            Register::RSI => write!(f, "%rsi"),
            Register::RBP => write!(f, "%rbp"),
            Register::R8 => write!(f, "%r8"),
            Register::R9 => write!(f, "%r9"),
            Register::R10 => write!(f, "%r10"),
            Register::R11 => write!(f, "%r11"),
            Register::R12 => write!(f, "%r12"),
            Register::R13 => write!(f, "%r13"),
            Register::R14 => write!(f, "%r14"),
            Register::R15 => write!(f, "%r15"),
        }
    }
}

/// Array of argument registers.
pub static ARGS_REGS: [Register; 6] = [
    Register::RDI,
    Register::RSI,
    Register::RDX,
    Register::RCX,
    Register::R8,
    Register::R9,
];

#[allow(dead_code)]
/// Array of callee-save registers.
pub static CALLEE_SAVE_REGS: [Register; 5] = [
    Register::RBX,
    Register::R12,
    Register::R13,
    Register::R14,
    Register::R15,
];

#[derive(Copy, Clone, PartialEq)]
/// Stack representation.
/// Holds the offset from the base pointer.
pub enum Stack {
    RSP(i64),
}

// Display for Stack
impl std::fmt::Display for Stack {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Stack::RSP(offset) => write!(
                f,
                "{}(%rsp)",
                if *offset == 0 {
                    format!("")
                } else {
                    format!("{}", offset)
                }
            ),
        }
    }
}

#[derive(Copy, Clone, PartialEq)]
/// Location of variables and operands.
/// For immediate values, the location is the value itself.
pub enum Location {
    Register(Register),
    Stack(Stack),
    Immediate(i64),
}

// Display for Location
impl std::fmt::Display for Location {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Location::Register(reg) => write!(f, "{}", reg),
            Location::Stack(stack) => write!(f, "{}", stack),
            Location::Immediate(n) => write!(f, "${}", n),
        }
    }
}
