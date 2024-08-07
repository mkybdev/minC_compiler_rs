use crate::minc_ast;
use fancy_regex::Regex;

// Terminology:
// BFS - offset value from the Beginning of the Free Space of the stack (not Breadth-First Search)
// location - offset value of the variable address from the base pointer of the stack
// scope - a block of code where variables are defined and used
// _op - _operand
// _insns - _instructions

#[allow(unreachable_code, unused_variables)]
/// Takes a program.
/// Concatenates the following in this order:
///     Header,
///     Individual function definitions,
///     Trailer.
/// Returns the concatenated string as the machine code of the program.
pub fn ast_to_asm_program(_program: minc_ast::Program) -> String {
    let content = _program
        .defs
        .iter()
        .enumerate()
        .map(|(i, def)| ast_to_asm_def(def, i)) // Compiles each function definition
        .collect::<Vec<String>>()
        .join("\n");
    format!("{}\n{}\n{}\n", header(), format_asm(content), trailer())
}

#[allow(unreachable_code, unused_variables)]
/// Returns the header part of the machine code.
fn header() -> String {
    format!("\t{}\n\t{}\n", ".file \"program.minc\"", ".text")
}

#[allow(unreachable_code, unused_variables)]
/// Returns the trailer part of the machine code.
fn trailer() -> String {
    format!(
        "\t{}\n\t{}",
        ".ident \"MCC\"", ".section .note.GNU-stack,\"\",@progbits"
    )
}

#[allow(unreachable_code, unused_variables)]
/// Formats the machine code.
fn format_asm(asm: String) -> String {
    Regex::new(r"\n\s*\n\s*\n")
        .unwrap()
        .replace_all(&asm, "\n\n")
        .to_string()
}

#[allow(unreachable_code, unused_variables, dead_code)]
#[derive(Copy, Clone, PartialEq)]
/// Registers in x86-64.
enum Register {
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

/// Register array for arguments.
static ARGS_REGS: [Register; 6] = [
    Register::RDI,
    Register::RSI,
    Register::RDX,
    Register::RCX,
    Register::R8,
    Register::R9,
];

#[allow(dead_code)]
/// Register array for callee-save registers.
static CALLEE_SAVE_REGS: [Register; 5] = [
    Register::RBX,
    Register::R12,
    Register::R13,
    Register::R14,
    Register::R15,
];

#[allow(unreachable_code, unused_variables)]
#[derive(Copy, Clone, PartialEq)]
/// Stack representation.
enum Stack {
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

#[allow(unreachable_code, unused_variables)]
#[derive(Copy, Clone, PartialEq)]
/// Location of variables and operands.
enum Location {
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

#[allow(unreachable_code, unused_variables)]
#[derive(Clone)]
/// Environment for variables in a scope.
struct Environment {
    /// Map of variable names to their locations.
    env: std::collections::HashMap<String, Location>,
}

#[allow(unreachable_code, unused_variables)]
impl Environment {
    /// Returns a new environment.
    fn new() -> Environment {
        Environment {
            env: std::collections::HashMap::new(),
        }
    }

    /// Takes a variable name.
    /// Returns the location of the variable in the environment if it exists.
    fn lookup(&self, x: &str) -> Option<Location> {
        let loc = self.env.get(x);
        match loc {
            Some(loc) => Some(*loc),
            None => None,
        }
    }

    /// Takes a Location.
    /// Returns whether there exists a variable mapped to the location.
    fn contains(&self, loc: Location) -> bool {
        self.env.values().any(|&l| l == loc)
    }

    /// Takes a variable name and a location.
    /// Returns a new environment with the variable added.
    fn add(&self, x: &str, loc: Location) -> Environment {
        let mut env2 = Environment {
            env: self.env.clone(),
        };
        // Maps the variable name to the location
        // This means that the shadowing of variables is not supported
        env2.env.insert(x.to_string(), loc);
        env2
    }

    /// Takes a list of variable declarations and a stack location.
    /// Assigns locations (v, v+8, v+16, ...) to the variables declared in decls.
    /// Returns a new environment with the variables added and the next stack location.
    fn extend(&self, decls: &Vec<minc_ast::Decl>, loc: Stack) -> (Environment, i64) {
        let env2 = Environment {
            env: self.env.clone(),
        };
        // Iterates over the declarations
        match loc {
            Stack::RSP(loc) => {
                decls.iter().fold((env2, loc), |(env, loc), decl| {
                    // Adds the variable to the environment and increments BFS
                    (
                        env.add(&decl.name, Location::Stack(Stack::RSP(loc))),
                        loc + 8,
                    )
                })
            }
        }
    }
}

#[allow(unreachable_code, unused_variables)]
/// Takes a top-level definition.
/// Concatenates the following in this order:
///      Prologue (Grows stack, saves arguments),
///      Function body,
///      Epilogue (Shrinks stack, returns value).
/// Returns the concatenated string as the machine code of the function definition.
fn ast_to_asm_def(def: &minc_ast::Def, i: usize) -> String {
    // Always a function definition for now
    match def {
        // Extracts the function name, parameters, return type, and body
        minc_ast::Def::Fun(name, params, return_type, body) => {
            // Generates the prologue
            // Returns the prologue, environment, and free registers
            let (prologue, env, mut free_regs, v) = gen_prologue(def, i);
            let body_insns = ast_to_asm_stmt(
                body,
                env,
                v,
                &mut free_regs,
                &mut format!(".L{}0", i),
                &mut Location::Register(Register::RBX),
            ); // Compiles the function body
            format!("{}\n{}\n{}\n", prologue, body_insns, gen_epilogue(def, i))
        }
    }
}

#[allow(unreachable_code, unused_variables)]
/// Takes a definition.
/// Returns the prologue part of the definition.
fn gen_prologue(def: &minc_ast::Def, i: usize) -> (String, Environment, Vec<Register>, i64) {
    match def {
        minc_ast::Def::Fun(name, params, ..) => {
            // Save arguments to the environment
            const GROWTH: i64 = 100;
            let env = params
                .iter()
                .enumerate()
                .fold(Environment::new(), |env, (i, param)| {
                    let loc = if i < ARGS_REGS.len() {
                        Location::Register(ARGS_REGS[i])
                    } else {
                        // offset for rbp, stack growth + offset for arguments
                        Location::Stack(Stack::RSP(
                            (8 + 8 * GROWTH) + 8 * (i - ARGS_REGS.len() + 1) as i64,
                        ))
                    }; // Get the argument location
                    env.add(&param.name, loc)
                })
                .add(name, Location::Register(Register::RBP)); // Add the function name to the environment
            (
                format!(
                    "\t{}\n\t{}\n\t{}\n{}\n{}\n\t{}\n\t{}\n\t{}\n\t{}\n\t{}\n",
                    ".p2align 4",
                    format!(".globl {}", name),
                    format!(".type {}, @function", name),
                    format!("{}:", name),
                    format!(".LFB{}:", i),
                    ".cfi_startproc",
                    "endbr64",
                    "pushq %rbp",                          // Save base pointer
                    "movq %rsp, %rbp",                     // Save stack pointer
                    format!("subq ${}, %rsp", 8 * GROWTH)  // Grow stack
                ),
                env,
                [
                    vec![Register::RAX],
                    if params.len() < ARGS_REGS.len() {
                        ARGS_REGS[params.len()..].to_vec()
                    } else {
                        vec![]
                    }, // Registers for arguments which are not used
                    vec![Register::R10, Register::R11],
                ]
                .concat(),
                if params.len() > ARGS_REGS.len() {
                    (8 + 8 * GROWTH) + 8 * (params.len() - ARGS_REGS.len() + 1) as i64
                } else {
                    0
                }, // BFS
            )
        }
    }
}

#[allow(unreachable_code, unused_variables)]
/// Takes a definition.
/// Returns the epilogue part of the definition.
fn gen_epilogue(def: &minc_ast::Def, i: usize) -> String {
    match def {
        minc_ast::Def::Fun(name, ..) => {
            format!(
                "{}\n\t{}\n\t{}\n\t{}\n\t{}\n{}\n\t{}\n",
                format!(".LR{}:", i),
                "movq %rbp, %rsp", // Restore stack pointer
                "popq %rbp",       // Restore callee-save register
                "ret",
                ".cfi_endproc",
                format!(".LFE{}:", i),
                format!(".size {}, .-{}", name, name)
            )
        }
    }
}

#[allow(unreachable_code, unused_variables)]
/// Returns the next label.
fn next_label(label: &mut String) -> String {
    let next = label.clone();
    *label = format!(
        ".L{:0>2}",
        label
            .chars()
            .skip(2)
            .collect::<String>()
            .parse::<i64>()
            .unwrap()
            + 1
    );
    next
}

#[allow(unreachable_code, unused_variables)]
/// Takes a statement, an environment, BFS, and free registers.
/// Returns the machine code of the statement.
fn ast_to_asm_stmt(
    stmt: &minc_ast::Stmt,
    env: Environment,
    v: i64,
    regs: &mut Vec<Register>,
    label: &mut String,
    csr: &mut Location,
) -> String {
    match stmt {
        minc_ast::Stmt::Empty => format!(""),
        minc_ast::Stmt::Continue => format!(""),
        minc_ast::Stmt::Break => format!(""),
        minc_ast::Stmt::Return(expr) => {
            // Compiles the return statement as follows:
            //     [Compiled expression]
            //     movq [Expression], %rax
            let (insns, op) = ast_to_asm_expr(expr, env, v, regs, csr); // Compiles the expression
            format!(
                "{}\n{}\n{}\n",
                insns,
                match op {
                    Location::Register(Register::RAX) => format!(""),
                    _ => format!("\tmovq {}, %rax", op), // Moves the result to the return register
                },
                format!("\tjmp .LR{}", label.chars().collect::<Vec<char>>()[2])
            )
        }
        minc_ast::Stmt::Expr(expr) => {
            let (insns, op) = ast_to_asm_expr(expr, env, v, regs, csr); // Compiles the expression
            format!("{}\n", insns)
        }
        minc_ast::Stmt::Compound(decls, stmts) => {
            // A new compound statement means a new scope
            // Extends the environment with the new variables
            let (env2, v2) = env.extend(decls, Stack::RSP(v));
            cogen_stmts(stmts, env2, v2, regs, label, csr) // Compiles the statements
        }
        minc_ast::Stmt::If(cond, then_stmt, Some(else_stmt)) => {
            // Compiles the if-else statement as follows:
            //     [Compiled condition]
            //     cmpq $0, [Condition]
            //     je .Lc <- jump to else part if condition is false
            //     [Compiled then statement]
            //     jmp .Le
            //     .Lc: <- else part
            //          [Compiled else statement]
            //     .Le:
            let (cond_insns, cond_op) = ast_to_asm_expr(cond, env.clone(), v, regs, csr); // Compiles the condition
            let label_lc = next_label(label);
            let label_le = next_label(label);
            format!(
                "{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n",
                cond_insns,
                format!("\tcmpq $0, {}", cond_op), // Compares the condition with 0
                format!("\tje {}", label_lc),
                ast_to_asm_stmt(then_stmt, env.clone(), v, regs, label, csr), // Compiles the then statement
                format!("\tjmp {}", label_le),
                format!("{}:", label_lc),
                ast_to_asm_stmt(else_stmt, env, v, regs, label, csr), // Compiles the else statement
                format!("{}:", label_le),
            )
        }
        minc_ast::Stmt::If(cond, then_stmt, None) => {
            // Compiles the if statement as follows:
            //     [Compiled condition]
            //     cmpq $0, [Condition]
            //     je .Lc <- jump to end if condition is false
            //     [Compiled then statement]
            //     .Lc:
            let (cond_insns, cond_op) = ast_to_asm_expr(cond, env.clone(), v, regs, csr); // Compiles the condition
            let label_lc = next_label(label);
            format!(
                "{}\n{}\n{}\n{}\n{}\n",
                cond_insns,
                format!("\tcmpq $0, {}", cond_op), // Compares the condition with 0
                format!("\tje {}", label_lc),
                ast_to_asm_stmt(then_stmt, env.clone(), v, regs, label, csr), // Compiles the then statement
                format!("{}:", label_lc),
            )
        }
        minc_ast::Stmt::While(cond, body) => {
            // Compiles the while statement as follows:
            //     jmp .Lc
            //     .Ls:
            //          [Compiled body]
            //     .Lc:
            //          [Compiled condition]
            //          cmpq $0, [Condition]
            //          jne .Ls
            let (cond_insns, cond_op) = ast_to_asm_expr(cond, env.clone(), v, regs, csr); // Compiles the condition
            let label_lc = next_label(label);
            let label_ls = next_label(label);
            format!(
                "{}\n{}\n{}\n{}\n{}\n{}\n{}\n",
                format!("\tjmp {}", label_lc),
                format!("{}:", label_ls),                        // Body part
                ast_to_asm_stmt(body, env, v, regs, label, csr), // Compiles the body
                format!("{}:", label_lc),                        // Condition part
                cond_insns,
                format!("\tcmpq $0, {}", cond_op), // Compares the condition with 0
                format!("\tjne {}", label_ls),
            )
        }
    }
}

#[allow(unreachable_code, unused_variables)]
/// Takes a list of statements, an environment, and BFS.
/// Returns the machine code of the statements.
fn cogen_stmts(
    stmts: &Vec<minc_ast::Stmt>,
    env: Environment,
    v: i64,
    regs: &mut Vec<Register>,
    label: &mut String,
    csr: &mut Location,
) -> String {
    stmts
        .iter()
        .map(|stmt| ast_to_asm_stmt(stmt, env.clone(), v, regs, label, csr)) // Compiles each statement
        .collect::<Vec<String>>()
        .join("\n")
}

#[allow(unreachable_code, unused_variables, dead_code)]
/// Returns the next callee-save register.
fn next_callee_save_reg(loc: &mut Location) -> Location {
    let next = loc.clone();
    *loc = match next {
        Location::Register(r) => {
            if let Some(i) = CALLEE_SAVE_REGS.iter().position(|&x| x == r) {
                if i + 1 != CALLEE_SAVE_REGS.len() {
                    Location::Register(CALLEE_SAVE_REGS[i + 1])
                } else {
                    Location::Stack(Stack::RSP(0))
                }
            } else {
                Location::Stack(Stack::RSP(0))
            }
        }
        Location::Stack(Stack::RSP(v)) => Location::Stack(Stack::RSP(v + 8)),
        _ => Location::Stack(Stack::RSP(0)),
    };
    next
}

#[allow(unreachable_code, unused_variables)]
/// Takes an expression, an environment, BFS and free registers.
/// Returns the machine code of the expression and the location of the result.
fn ast_to_asm_expr(
    expr: &minc_ast::Expr,
    env: Environment,
    v: i64,
    regs: &mut Vec<Register>,
    csr: &mut Location,
) -> (String, Location) {
    match expr {
        minc_ast::Expr::IntLiteral(n) => {
            (format!(""), Location::Immediate(*n)) // Returns the integer literal
        }
        minc_ast::Expr::Id(x) => {
            // If the variable is found in the environment
            if let Some(loc) = env.lookup(x) {
                (format!(""), loc) // Returns the location of the variable
            } else {
                panic!("Variable {} not found", x)
            }
        }
        minc_ast::Expr::Op(op, e) => {
            let op = op.as_str();
            match op {
                // Arithmetic instructions
                "+" | "-" | "*" | "/" | "%" => {
                    match op {
                        // Compiles as follows:
                        //    [Compiled second operand]
                        //    movq [Second operand], [Stack]
                        //    [Compiled first operand]
                        //    addq/subq [Second operand in stack], [First operand]
                        "+" | "-" => {
                            // For positive/negative numbers
                            if e.len() == 1 {
                                // Compiles the operand
                                let (insns0, op0) = ast_to_asm_expr(&e[0], env, v, regs, csr);
                                match op0 {
                                    Location::Immediate(n) => (
                                        format!(""),
                                        match op {
                                            "+" => op0,
                                            "-" => Location::Immediate(-n),
                                            _ => panic!("Unknown operator {}", op),
                                        },
                                    ),
                                    _ => (
                                        match op {
                                            "+" => format!("{}\n", insns0),
                                            "-" => format!(
                                                "{}\n{}\n",
                                                insns0,
                                                format!("\tnegq {}", op0) // Negates the number
                                            ),
                                            _ => panic!("Unknown operator {}", op),
                                        },
                                        op0, // The result is stored in the first operand
                                    ),
                                }
                            } else {
                                // Compiles the second operand
                                let (insns1, op1) =
                                    ast_to_asm_expr(&e[1], env.clone(), v, regs, csr);
                                // Compiles the first operand
                                // The second operand is compiled first to ensure that the result is stored in the first operand
                                let (insns0, op0) = ast_to_asm_expr(&e[0], env, v + 8, regs, csr);
                                match (op0, op1) {
                                    (Location::Immediate(n0), Location::Immediate(n1)) => (
                                        format!(""),
                                        Location::Immediate(match op {
                                            "+" => n0 + n1,
                                            "-" => n0 - n1,
                                            _ => panic!("Unknown operator {}", op),
                                        }),
                                    ),
                                    (Location::Immediate(n0), _) => {
                                        let m = Stack::RSP(v); // Where to copy the second operand
                                        (
                                            format!(
                                                "{}\n{}\n{}\n{}",
                                                insns1,
                                                match op1 {
                                                    Location::Stack(_) =>
                                                        format!("\tpushq {}\n\tpopq {}", op1, m),
                                                    _ => format!("\tmovq {}, {}", op1, m),
                                                },
                                                insns0,
                                                match op {
                                                    "+" => format!("\taddq ${}, {}", n0, m),
                                                    "-" => format!(
                                                        "\tsubq ${}, {}\n\tnegq {}",
                                                        n0, m, m
                                                    ),
                                                    _ => panic!("Unknown operator {}", op),
                                                }
                                            ),
                                            Location::Stack(m),
                                        )
                                    }
                                    (_, Location::Immediate(n1)) => {
                                        let m = Stack::RSP(v);
                                        (
                                            format!(
                                                "{}\n{}\n{}\n{}",
                                                insns1,
                                                insns0,
                                                match op0 {
                                                    Location::Stack(_) =>
                                                        format!("\tpushq {}\n\tpopq {}", op0, m),
                                                    _ => format!("\tmovq {}, {}", op0, m),
                                                },
                                                match op {
                                                    "+" => format!("\taddq ${}, {}", n1, m),
                                                    "-" => format!("\tsubq ${}, {}", n1, m),
                                                    _ => panic!("Unknown operator {}", op),
                                                }
                                            ),
                                            Location::Stack(m),
                                        )
                                    }
                                    _ => {
                                        let m = Stack::RSP(v); // Where to copy %rax
                                        (
                                            format!(
                                                "{}\n{}\n{}\n{}\n{}\n{}\n",
                                                insns1, // Compiles the second operand
                                                format!("\tpushq {}", op1),
                                                format!("\tpopq {}", m),
                                                insns0, // Compiles the first operand
                                                format!("\tmovq {}, %rax", op0),
                                                match op {
                                                    "+" => format!("\taddq {}, %rax", m),
                                                    "-" => format!("\tsubq {}, %rax", m),
                                                    _ => panic!("Unknown operator {}", op),
                                                },
                                            ),
                                            Location::Register(Register::RAX), // The result is stored in rax
                                        )
                                    }
                                }
                            }
                        }
                        // Compiles as follows:
                        //    [Compiled second operand]
                        //    movq [Second operand], [Stack]
                        //    [Compiled first operand]
                        //    movq [First operand], %rax
                        //    mulq [Second operand in stack] <- result in rax
                        "*" => {
                            // Compiles the second operand
                            let (insns1, op1) = ast_to_asm_expr(&e[1], env.clone(), v, regs, csr);
                            // Compiles the first operand
                            // The second operand is compiled first to ensure that the result is stored in the first operand
                            let (insns0, op0) = ast_to_asm_expr(&e[0], env, v + 8, regs, csr);
                            let m = Stack::RSP(v); // Where to copy the first operand or %rax
                            (
                                format!(
                                    "{}\n{}\n{}\n{}\n{}\n",
                                    insns1, // Compiles the second operand
                                    match op1 {
                                        Location::Stack(_) =>
                                            format!("\tpushq {}\n\tpopq {}", op1, m),
                                        _ => format!("\tmovq {}, {}", op1, m),
                                    },
                                    insns0, // Compiles the first operand
                                    format!("\tmovq {}, %rax", op0),
                                    format!("\tmulq {}", m),
                                ),
                                Location::Register(Register::RAX), // The result is stored in rax
                            )
                        }
                        // Compiles as follows:
                        //    [Compiled second operand]
                        //    movq [Second operand], [Stack]
                        //    [Compiled first operand]
                        //    movq [First operand], %rax
                        //    xor %rdx, %rdx <- clear rdx
                        //    divq [Second operand in stack] <- result in rax, remainder in rdx
                        "/" | "%" => {
                            // Compiles the second operand
                            let (insns1, op1) = ast_to_asm_expr(&e[1], env.clone(), v, regs, csr);
                            // Compiles the first operand
                            // The second operand is compiled first to ensure that the result is stored in the first operand
                            let (insns0, op0) = ast_to_asm_expr(&e[0], env, v + 8, regs, csr);
                            let m = Stack::RSP(v); // Where to copy the first operand
                            (
                                format!(
                                    "{}\n{}\n{}\n{}\n{}\n{}\n",
                                    insns1, // Compiles the second operand
                                    match op1 {
                                        Location::Stack(_) =>
                                            format!("\tpushq {}\n\tpopq {}", op1, m),
                                        _ => format!("\tmovq {}, {}", op1, m),
                                    },
                                    insns0, // Compiles the first operand
                                    format!("\tmovq {}, %rax", op0),
                                    format!("\txor %rdx, %rdx"),
                                    format!("\tdivq {}", m),
                                ),
                                match op {
                                    "/" => Location::Register(Register::RAX), // The result is stored in rax
                                    "%" => Location::Register(Register::RDX), // The result is stored in rdx
                                    _ => panic!("Unknown operator {}", op),
                                },
                            )
                        }
                        _ => panic!("Unknown operator {}", op),
                    }
                }
                // Comparison instructions
                // Compiles as follows:
                //    [Compiled second operand]
                //    movq [Second operand], [Stack]
                //    [Compiled first operand]
                //    movq [First operand], [Stack]
                //    movq $0, %rax
                //    movq [First operand in stack], [First operand]
                //    cmpq [Second operand in stack], [First operand]
                //    setl/setle/setg/setge/sete/setne %al
                //    movzbq %al, %rax <- zero extends %al to %rax
                "<" | "<=" | ">" | ">=" | "==" | "!=" => {
                    // Compiles the second operand
                    let (insns1, op1) = ast_to_asm_expr(&e[1], env.clone(), v, regs, csr);
                    // Compiles the first operand
                    let (insns0, op0) = ast_to_asm_expr(&e[0], env, v + 8, regs, csr);
                    let m0 = Stack::RSP(v + 8); // Where to copy the first operand
                    let m1 = Stack::RSP(v); // Where to copy the second operand
                    (
                        format!(
                            "{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n",
                            insns1,
                            match op1 {
                                Location::Stack(_) => format!("\tpushq {}\n\tpopq {}", op1, m1),
                                _ => format!("\tmovq {}, {}", op1, m1),
                            }, // Copies the second operand to the stack
                            insns0,
                            match op0 {
                                Location::Stack(_) => format!("\tpushq {}\n\tpopq {}", op0, m0),
                                _ => format!("\tmovq {}, {}", op0, m0),
                            }, // Copies the first operand to the stack
                            "\tmovq $0, %rax", // Initializes the result to 0
                            format!("\tmovq {}, %rax", m0), // Restores the first operand
                            format!("\tcmpq {}, %rax", m1), // Compares the first and second operands
                            // Sets the result to 1 if the condition is true, 0 if not
                            match op {
                                "<" => "\tsetl %al",
                                "<=" => "\tsetle %al",
                                ">" => "\tsetg %al",
                                ">=" => "\tsetge %al",
                                "==" => "\tsete %al",
                                "!=" => "\tsetne %al",
                                _ => panic!("Unknown operator {}", op),
                            },
                            "\tmovzbq %al, %rax",
                        ),
                        Location::Register(Register::RAX), // The result is stored in rax
                    )
                }
                // Logical instructions
                "!" | "~" => match op {
                    // Compiles as follows:
                    //    [Compiled operand]
                    //    testq [Operand], [Operand] <- sets flags: 1 if 0, 0 if not 0
                    //    sete %al <- sets %al to 1 if the zero flag is set, 0 if not
                    //    movzbq %al, %rax <- zero extends %al to %rax
                    "!" => {
                        if e.len() != 1 {
                            panic!("Expected 1 operand for !")
                        } else {
                            let (insns, op) = ast_to_asm_expr(&e[0], env, v, regs, csr);
                            match op {
                                Location::Register(r) => regs.push(r), // Adds the operand to the free registers
                                _ => {}
                            }
                            (
                                format!(
                                    "{}\n{}\n{}\n{}\n",
                                    insns,
                                    format!("\ttestq {}, {}", op, op),
                                    "\tsete %al",
                                    "\tmovzbq %al, %rax",
                                ),
                                Location::Register(Register::RAX),
                            )
                        }
                    }
                    // Compiles as follows:
                    //    [Compiled operand]
                    //    notq [Operand]
                    "~" => {
                        if e.len() != 1 {
                            panic!("Expected 1 operand for ~")
                        } else {
                            let (insns, op) = ast_to_asm_expr(&e[0], env, v, regs, csr);
                            match op {
                                Location::Register(r) => regs.push(r), // Adds the operand to the free registers
                                _ => {}
                            }
                            (
                                // bitwise not
                                format!("{}\n{}\n", insns, format!("\tnotq {}", op)),
                                op,
                            )
                        }
                    }
                    _ => panic!("Unknown operator {}", op),
                },
                // Assignment instruction
                "=" => {
                    if e.len() != 2 {
                        panic!("Expected 2 operands for =")
                    } else {
                        // Compiles the second operand
                        let (insns1, op1) = ast_to_asm_expr(&e[1], env.clone(), v, regs, csr);
                        // Get the location of the first operand
                        if let minc_ast::Expr::Id(x) = &e[0] {
                            // If the variable is found in the environment
                            if let Some(loc) = env.lookup(x) {
                                (
                                    format!(
                                        "{}\n{}\n",
                                        insns1,
                                        match op1 {
                                            Location::Stack(_) =>
                                                format!("\tpushq {}\n\tpopq {}", op1, loc),
                                            _ => format!("\tmovq {}, {}", op1, loc),
                                        },
                                    ),
                                    Location::Register(Register::RAX),
                                )
                            } else {
                                panic!("Variable {} not found", x)
                            }
                        } else {
                            panic!("Expected an identifier for the first operand")
                        }
                    }
                }
                _ => panic!("Unknown operator {}", op),
            }
        }
        minc_ast::Expr::Call(f, args) => {
            // Compiles the arguments
            let (insns, arg_vars) = ast_to_asm_exprs(args, env.clone(), v, regs, csr);

            // Get function name
            match &**f {
                minc_ast::Expr::Id(name) => {
                    let recursive = if let Some(_) = env.lookup(name) {
                        true
                    } else {
                        false
                    };
                    (
                        format!(
                            "{}\n{}\n",
                            insns,
                            make_call(name.to_string(), arg_vars, env, v, recursive)
                        ),
                        Location::Register(Register::RAX),
                    )
                }
                _ => panic!("Function name must be an identifier"),
            }
        }
        minc_ast::Expr::Paren(sub_expr) => {
            ast_to_asm_expr(sub_expr, env, v, regs, csr) // Compiles the sub-expression
        }
    }
}

#[allow(unreachable_code, unused_variables, dead_code)]
/// Returns the machine code of the expressions and the locations of the results.
fn ast_to_asm_exprs(
    args: &Vec<minc_ast::Expr>,
    env: Environment,
    v: i64,
    regs: &mut Vec<Register>,
    csr: &mut Location,
) -> (String, Vec<Location>) {
    let mut insns_res: Vec<String> = vec![];
    let mut locs: Vec<Location> = vec![];
    for (i, arg) in args.iter().enumerate() {
        let (insns, op) = ast_to_asm_expr(arg, env.clone(), v + i as i64 * 8, regs, csr);
        insns_res.push(insns);
        locs.push(op);
    }
    (insns_res.join("\n"), locs)
}

#[allow(unreachable_code, unused_variables)]
/// Put the arguments in the right registers specified by ABI
/// If the registers are already used as local variables, puts them on the stack
/// After calling function, pop the variables from the stack
fn make_call(f: String, args: Vec<Location>, env: Environment, v: i64, recursive: bool) -> String {
    let mut call_insns = String::new();
    let mut offset = 0;
    let mut stacked: Vec<Location> = vec![];
    let mut to_copied: Vec<(Location, Location, i64)> = vec![];
    let mut to_passed: Vec<(Location, Location)> = vec![];
    for (i, arg_var) in args.iter().enumerate() {
        let arg_pos: Location = if i < ARGS_REGS.len() {
            Location::Register(ARGS_REGS[i])
        } else {
            Location::Stack(Stack::RSP(8 * (i - ARGS_REGS.len() + 1) as i64))
        };
        if env.contains(arg_pos) {
            stacked.push(arg_pos);
            offset += 8;
            call_insns.push_str(&format!("\tpushq {}\n", arg_pos));
        }
        to_copied.push((arg_var.clone(), arg_pos, v + 8 * i as i64));
    }
    for (from, to, loc) in to_copied.iter() {
        let m = Location::Stack(Stack::RSP(*loc + 8 * stacked.len() as i64));
        let tmp = match from {
            Location::Stack(Stack::RSP(v2)) => format!(
                "\tpushq {}\n\tpopq {}\n",
                Stack::RSP(v2 + 8 * stacked.len() as i64),
                m
            ),
            _ => format!("\tmovq {}, {}\n", from, m),
        };
        call_insns.push_str(&tmp);
        to_passed.push((m, *to));
    }
    for (from, to) in to_passed.iter() {
        call_insns.push_str(&format!("\tpushq {}\n\tpopq {}\n", from, to));
    }
    if !recursive {
        call_insns.push_str(&format!("\taddq $8, %rsp\n"));
    }
    call_insns.push_str(&format!("\tcall {}\n", f));
    if !recursive {
        call_insns.push_str(&format!("\tsubq $8, %rsp\n"));
    }
    for arg_pos in stacked.iter().rev() {
        call_insns.push_str(&format!("\tpopq {}\n", arg_pos));
    }
    call_insns
}
