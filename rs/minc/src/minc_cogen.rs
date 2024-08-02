use crate::minc_ast;

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
    format!(
        "{}\n{}\n{}\n",
        header(),
        _program
            .defs
            .iter()
            .map(|def| ast_to_asm_def(def)) // Compiles each function definition
            .collect::<Vec<String>>()
            .join("\n"),
        trailer()
    )
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

#[allow(unreachable_code, unused_variables, dead_code)]
#[derive(Copy, Clone)]
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
static CALLEE_SAVE_REGS: [Register; 6] = [
    Register::RBX,
    Register::RBP,
    Register::R12,
    Register::R13,
    Register::R14,
    Register::R15,
];

#[allow(unreachable_code, unused_variables)]
#[derive(Copy, Clone)]
/// Stack representation.
enum Stack {
    RSP(i64),
}

// Display for Stack
impl std::fmt::Display for Stack {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Stack::RSP(offset) => write!(f, "{}(%rsp)", offset),
        }
    }
}

#[allow(unreachable_code, unused_variables)]
#[derive(Copy, Clone)]
/// Location of variables and operands.
enum Location {
    Register(Register),
    Stack(Stack),
}

// Display for Location
impl std::fmt::Display for Location {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Location::Register(reg) => write!(f, "{}", reg),
            Location::Stack(stack) => write!(f, "{}", stack),
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
fn ast_to_asm_def(def: &minc_ast::Def) -> String {
    // Always a function definition for now
    match def {
        // Extracts the function name, parameters, return type, and body
        minc_ast::Def::Fun(name, params, return_type, body) => {
            // Generates the prologue
            // Returns the prologue, environment, and free registers
            let (prologue, env, mut free_regs) = gen_prologue(def);
            format!(
                "{}\n{}\n{}\n",
                prologue,
                ast_to_asm_stmt(body, env, 0, &mut free_regs), // Compiles the function body
                gen_epilogue(def)
            )
        }
    }
}

#[allow(unreachable_code, unused_variables)]
/// Takes a definition.
/// Returns the prologue part of the definition.
fn gen_prologue(def: &minc_ast::Def) -> (String, Environment, Vec<Register>) {
    match def {
        minc_ast::Def::Fun(name, params, ..) => {
            // Save arguments to the environment
            let env = params
                .iter()
                .enumerate()
                .fold(Environment::new(), |env, (i, param)| {
                    let loc = Location::Register(ARGS_REGS[i]); // Get the argument register
                    env.add(&param.name, loc)
                });
            (
                format!(
                    "\t{}\n\t{}\n\t{}\n{}\n{}\n\t{}\n\t{}\n\t{}\n\t{}\n\t{}\n",
                    ".p2align 4",
                    format!(".globl {}", name),
                    format!(".type {}, @function", name),
                    format!("{}:", name),
                    ".LFB0:",
                    ".cfi_startproc",
                    "endbr64",
                    "pushq %rbx",      // Save callee-save register
                    "movq %rsp, %rbx", // Save stack pointer
                    "subq $16, %rsp"   // Allocate space for local variables (temporary)
                ),
                env,
                [
                    vec![Register::RAX],
                    ARGS_REGS[params.len()..].to_vec(), // Registers for arguments which are not used
                    vec![Register::R10, Register::R11],
                ]
                .concat(),
            )
        }
    }
}

#[allow(unreachable_code, unused_variables)]
/// Takes a definition.
/// Returns the epilogue part of the definition.
fn gen_epilogue(def: &minc_ast::Def) -> String {
    match def {
        minc_ast::Def::Fun(name, ..) => {
            format!(
                "\t{}\n\t{}\n\t{}\n\t{}\n{}\n\t{}\n",
                "movq %rbx, %rsp", // Restore stack pointer
                "popq %rbx",       // Restore callee-save register
                "ret",
                ".cfi_endproc",
                ".LFE0:",
                format!(".size {}, .-{}", name, name)
            )
        }
    }
}

#[allow(unreachable_code, unused_variables)]
/// Takes a statement, an environment, BFS, and free registers.
/// Returns the machine code of the statement.
fn ast_to_asm_stmt(
    stmt: &minc_ast::Stmt,
    env: Environment,
    v: i64,
    regs: &mut Vec<Register>,
) -> String {
    match stmt {
        minc_ast::Stmt::Empty => format!(""),
        minc_ast::Stmt::Continue => format!(""),
        minc_ast::Stmt::Break => format!(""),
        minc_ast::Stmt::Return(expr) => {
            // Compiles the return statement as follows:
            //     [Compiled expression]
            //     movq [Expression], %rax
            let (insns, op) = ast_to_asm_expr(expr, env, v, regs); // Compiles the expression
            format!(
                "{}\n{}\n",
                insns,
                format!("\tmovq {}(%rsp), %rax", op), // Moves the result to the return register
            )
        }
        minc_ast::Stmt::Expr(expr) => format!(""),
        minc_ast::Stmt::Compound(decls, stmts) => {
            // A new compound statement means a new scope
            // Extends the environment with the new variables
            let (env2, v2) = env.extend(decls, Stack::RSP(v));
            cogen_stmts(stmts, env2, v2, regs) // Compiles the statements
        }
        minc_ast::Stmt::If(cond, then_stmt, Some(else_stmt)) => {
            format!("")
        }
        minc_ast::Stmt::If(cond, then_stmt, None) => {
            format!("")
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
            let (cond_insns, cond_op) = ast_to_asm_expr(cond, env.clone(), v, regs); // Compiles the condition
            format!(
                "{}\n{}\n{}\n{}\n{}\n{}\n{}\n",
                "\tjmp .Lc",
                ".Ls:",                              // Statements part
                ast_to_asm_stmt(body, env, v, regs), // Compiles the body
                ".Lc:",                              // Condition part
                cond_insns,
                format!("\tcmpq $0, {}", cond_op), // Compares the condition with 0
                "\tjne .Ls"
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
) -> String {
    stmts
        .iter()
        .map(|stmt| ast_to_asm_stmt(stmt, env.clone(), v, regs)) // Compiles each statement
        .collect::<Vec<String>>()
        .join("\n")
}

#[allow(unreachable_code, unused_variables)]
/// Takes an expression, an environment, BFS and free registers.
/// Returns the machine code of the expression and the location of the result.
fn ast_to_asm_expr(
    expr: &minc_ast::Expr,
    env: Environment,
    v: i64,
    regs: &mut Vec<Register>,
) -> (String, Register) {
    match expr {
        minc_ast::Expr::IntLiteral(n) => {
            let reg = regs[0]; // Get the first free register
            (format!("\tmovq ${}, {}", n, reg), reg)
        }
        minc_ast::Expr::Id(x) => {
            // If the variable is found in the environment
            if let Some(loc) = env.lookup(x) {
                let reg = regs[0]; // Get the first free register
                (format!("\tmovq {}, {}", loc, reg), reg)
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
                                let (insns0, op0) = ast_to_asm_expr(&e[0], env, v, regs);
                                (
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
                                )
                            } else {
                                // Compiles the second operand
                                let (insns1, op1) = ast_to_asm_expr(&e[1], env.clone(), v, regs);
                                regs.remove(0); // Removes the first free register
                                                // Compiles the first operand
                                                // The second operand is compiled first to ensure that the result is stored in the first operand
                                let (insns0, op0) = ast_to_asm_expr(&e[0], env, v + 8, regs);
                                let m = Stack::RSP(v); // Where to copy the first operand
                                (
                                    format!(
                                        "{}\n{}\n{}\n{}\n",
                                        insns1, // Compiles the second operand
                                        format!("\tmovq {}, {}", op1, m),
                                        insns0, // Compiles the first operand
                                        match op {
                                            "+" => format!("\taddq {}, {}", m, op0),
                                            "-" => format!("\tsubq {}, {}", m, op0),
                                            _ => panic!("Unknown operator {}", op),
                                        }
                                    ),
                                    op0, // The result is stored in the first operand
                                )
                            }
                        }
                        // Compiles as follows:
                        //    [Compiled second operand]
                        //    movq [Second operand], [Stack]
                        //    [Compiled first operand]
                        //    imulq [Second operand in stack], [First operand], [First operand]
                        "*" => {
                            // Compiles the second operand
                            let (insns1, op1) = ast_to_asm_expr(&e[1], env.clone(), v, regs);
                            regs.remove(0); // Removes the first free register
                                            // Compiles the first operand
                                            // The second operand is compiled first to ensure that the result is stored in the first operand
                            let (insns0, op0) = ast_to_asm_expr(&e[0], env, v + 8, regs);
                            let m = Stack::RSP(v); // Where to copy the first operand
                            (
                                format!(
                                    "{}\n{}\n{}\n{}\n",
                                    insns1, // Compiles the second operand
                                    format!("\tmovq {}, {}", op1, m),
                                    insns0, // Compiles the first operand
                                    format!("\timulq {}, {}, {}", m, op0, op0), // Multiplies the operands
                                ),
                                op0, // The result is stored in the first operand
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
                            let (insns1, op1) = ast_to_asm_expr(&e[1], env.clone(), v, regs);
                            regs.remove(0); // Removes the first free register
                                            // Compiles the first operand
                                            // The second operand is compiled first to ensure that the result is stored in the first operand
                            let (insns0, op0) = ast_to_asm_expr(&e[0], env, v + 8, regs);
                            let m = Stack::RSP(v); // Where to copy the first operand
                            (
                                format!(
                                    "{}\n{}\n{}\n{}\n{}\n{}\n",
                                    insns1, // Compiles the second operand
                                    format!("\tmovq {}, {}", op1, m),
                                    insns0, // Compiles the first operand
                                    format!("\tmovq {}, %rax", op0),
                                    format!("\txor %rdx, %rdx"),
                                    format!("\tdivq {}", m),
                                ),
                                match op {
                                    "/" => Register::RAX, // The result is stored in rax
                                    "%" => Register::RDX, // The result is stored in rdx
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
                "<" | "<=" | ">" | ">=" | "==" | "!=" => {
                    // Compiles the second operand
                    let (insns1, op1) = ast_to_asm_expr(&e[1], env.clone(), v, regs);
                    regs.remove(0); // Removes the first free register
                                    // Compiles the first operand
                    let (insns0, op0) = ast_to_asm_expr(&e[0], env, v + 8, regs);
                    let m0 = Stack::RSP(v); // Where to copy the first operand
                    let m1 = Stack::RSP(v + 8); // Where to copy the second operand
                    (
                        format!(
                            "{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n",
                            insns1,
                            format!("\tmovq {}, {}", op1, m1), // Copies the second operand to the stack
                            insns0,
                            format!("\tmovq {}, {}", op0, m0), // Copies the first operand to the stack
                            "\tmovq $0, %rax",                 // Initializes the result to 0
                            format!("\tmovq {}, {}", m0, op0), // Restores the first operand
                            format!("\tcmpq {}, {}", m1, op0), // Compares the first and second operands
                            // Sets the result to 1 if the condition is true, 0 if not
                            match op {
                                "<" => "\tsetl %al",
                                "<=" => "\tsetle %al",
                                ">" => "\tsetg %al",
                                ">=" => "\tsetge %al",
                                "==" => "\tsete %al",
                                "!=" => "\tsetne %al",
                                _ => panic!("Unknown operator {}", op),
                            }
                        ),
                        Register::RAX, // The result is stored in rax
                    )
                }
                // Logical instructions
                "!" | "~" => match op {
                    // Compiles as follows:
                    //    [Compiled operand]
                    //    testq [Operand], [Operand] <- sets flags: 1 if 0, 0 if not 0
                    //    sete %al <- sets %al to 1 if the zero flag is set, 0 if not
                    "!" => {
                        if e.len() != 1 {
                            panic!("Expected 1 operand for !")
                        } else {
                            let (insns, op) = ast_to_asm_expr(&e[0], env, v, regs);
                            (
                                format!(
                                    "{}\n{}\n{}\n",
                                    insns,
                                    format!("\ttestq {}, {}", op, op),
                                    "\tsete %al"
                                ),
                                Register::RAX,
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
                            let (insns, op) = ast_to_asm_expr(&e[0], env, v, regs);
                            (
                                // bitwise not
                                format!("{}\n{}\n", insns, format!("\tnotq {}", op)),
                                op,
                            )
                        }
                    }
                    _ => panic!("Unknown operator {}", op),
                },
                _ => panic!("Unknown operator {}", op),
            }
        }
        minc_ast::Expr::Call(f, args) => {
            // arg_vars: The locations of the arguments
            let (insns, arg_vars) = ast_to_asm_exprs(args, env, v, regs);
            let arg_regs = vec!["%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9"];
            let mut call_insns = arg_vars
                .iter()
                .enumerate()
                .map(|(i, arg_var)| {
                    format!(
                        "\tmovq {}, {}",
                        arg_var,
                        if i < arg_regs.len() {
                            format!("{}", arg_regs[i])
                        } else {
                            format!("{}(%rsp)", 8 * (i - arg_regs.len()))
                        }
                    )
                })
                .collect::<Vec<String>>()
                .join("\n");
            match &**f {
                minc_ast::Expr::Id(name) => {
                    call_insns.push_str(&format!("\tcall {}@PLT", name));
                }
                _ => panic!("Function name must be an identifier"),
            }
            (format!("{}\n{}", insns, call_insns), arg_vars[0])
        }
        minc_ast::Expr::Paren(sub_expr) => (format!(""), Register::RAX),
    }
}

#[allow(unreachable_code, unused_variables)]
fn ast_to_asm_exprs(
    args: &Vec<minc_ast::Expr>,
    env: Environment,
    v: i64,
    regs: &mut Vec<Register>,
) -> (String, Vec<Register>) {
    args.iter()
        .enumerate()
        .map(|(offset, expr)| ast_to_asm_expr(expr, env.clone(), v + offset as i64 * 8, regs))
        .fold(
            (format!(""), Vec::new()),
            |(insns, mut arg_vars), (insns2, arg_var)| {
                arg_vars.push(arg_var);
                (format!("{}\n{}", insns, insns2), arg_vars)
            },
        )
}
