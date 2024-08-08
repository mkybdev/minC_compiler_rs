use crate::{cogen_concat_tab, minc_ast};
mod cogen;
mod constants;
mod environment;
mod location;
use crate::cogen_concat;
use constants::*;
use environment::*;
use location::*;

// fancy_regex: for regex pattern matching
use fancy_regex::Regex;

/// Takes a program.
/// Returns the concatenated string as the machine code of the program.
pub fn ast_to_asm_program(_program: minc_ast::Program) -> String {
    let content = _program
        .defs
        .iter()
        .enumerate()
        .map(|(i, def)| ast_to_asm_def(def, i)) // Compiles each function definition
        .collect::<Vec<String>>()
        .join("\n");
    // Concatenates the header, function definitions, and trailer
    cogen_concat!(header(), format_asm(content), trailer(), "")
}

/// Returns the header part of the machine code.
fn header() -> String {
    cogen_concat_tab!(".file \"program.minc\"", ".text")
}

/// Returns the trailer part of the machine code.
fn trailer() -> String {
    cogen_concat_tab!(".ident \"MCC\"", ".section .note.GNU-stack,\"\",@progbits")
}

/// Formats the machine code in the following ways:
///     Replaces multiple empty lines with a single empty line.
/// Returns the formatted machine code.
fn format_asm(asm: String) -> String {
    Regex::new(r"\n\s*\n\s*\n")
        .unwrap()
        .replace_all(&asm, "\n\n")
        .to_string()
}

/// Takes a top-level definition (and function number for now).
/// Returns the machine code of the function definition.
fn ast_to_asm_def(def: &minc_ast::Def, num: usize) -> String {
    // Always a function definition for now
    match def {
        // Extracts the function body
        minc_ast::Def::Fun(.., body) => {
            // Gets the prologue, environment, and stack offset
            let (prologue, env, v) = gen_prologue(def, num);
            // Compiles the function body
            let body_insns = ast_to_asm_stmt(body, env, v, &mut format!(".L{}0", num));
            // Gets the epilogue and concatenates the prologue, body, and epilogue
            cogen_concat!(prologue, body_insns, gen_epilogue(def, num))
        }
    }
}

/// Takes a definition (and function number for now).
/// Returns the prologue part of the definition, environment, and stack offset.
fn gen_prologue(def: &minc_ast::Def, num: usize) -> (String, Environment, i64) {
    // Always a function definition for now
    match def {
        // Extracts the function name and parameters
        minc_ast::Def::Fun(name, params, ..) => {
            // Stack growth for arguments, local variables
            // This is a meaningless number for now, which is left for future implementation
            const GROWTH: i64 = 100;
            // Iterates over the parameters and adds them to the environment
            let env = params
                .iter()
                .enumerate()
                .fold(Environment::new(), |env, (i, param)| {
                    let loc = if i < ARGS_REGS.len() {
                        // Get the argument register specified by ABI
                        Location::Register(ARGS_REGS[i])
                    } else {
                        // Get the argument location on the stack
                        // Offset is calculated based on the number of arguments and the stack growth
                        Location::Stack(Stack::RSP(
                            (LONG_SIZE + LONG_SIZE * GROWTH) // Callee-save register + stack growth
                                + LONG_SIZE * (i - ARGS_REGS.len() + 1) as i64, // Spilled arguments
                        ))
                    };
                    env.add(&param.name, loc) // Adds the parameter to the environment
                })
                .add(name, Location::Stack(Stack::RSP(0))); // Add the function itself to the environment
            (
                // Prologue
                cogen_concat!(
                    cogen_concat_tab!(
                        ".p2align 4",
                        format!(".globl {}", name),
                        format!(".type {}, @function", name)
                    ),
                    format!("{}:", name),
                    format!(".LFB{}:", num), // Generates a function beginning label from the function number
                    cogen_concat_tab!(
                        ".cfi_startproc",
                        "endbr64",
                        "pushq %rbp",      // Saves callee-save register
                        "movq %rsp, %rbp", // Saves stack pointer
                        format!("subq ${}, %rsp", LONG_SIZE * GROWTH)  // Grows stack
                    )
                ),
                env,       // Environment
                LONG_SIZE, // Stack offset (for function itself)
            )
        }
    }
}

/// Takes a definition (and function number for now).
/// Returns the epilogue part of the definition.
fn gen_epilogue(def: &minc_ast::Def, num: usize) -> String {
    // Always a function definition for now
    match def {
        // Extracts the function name
        minc_ast::Def::Fun(name, ..) => {
            cogen_concat!(
                format!(".LR{}:", num), // Generates a function return label from the function number
                cogen_concat_tab!(
                    "movq %rbp, %rsp", // Restores stack pointer
                    "popq %rbp",       // Restores callee-save register
                    "ret",
                    ".cfi_endproc"
                ),
                format!(".LFE{}:", num), // Generates a function end label from the function number
                cogen_concat_tab!(format!(".size {}, .-{}", name, name))
            )
        }
    }
}

/// Takes a label.
/// Returns the next label.
fn next_label(label: &mut String) -> String {
    let next = label.clone();
    *label = format!(
        ".L{:0>2}", // Generates a new label with a two-digit number
        label
            .chars()
            .skip(2) // Skips the first two characters
            .collect::<String>()
            .parse::<i64>()
            .unwrap()
            + 1  // Increments the label number
    );
    next // Returns the next label
}

/// Takes a statement, an environment, stack offset, and a label.
/// Returns the machine code of the statement.
fn ast_to_asm_stmt(stmt: &minc_ast::Stmt, env: Environment, v: i64, label: &mut String) -> String {
    match stmt {
        minc_ast::Stmt::Empty => format!(""),
        minc_ast::Stmt::Continue => format!(""),
        minc_ast::Stmt::Break => format!(""),
        minc_ast::Stmt::Return(expr) => {
            let (insns, op) = ast_to_asm_expr(expr, env, v); // Compiles the expression
            cogen_concat!(
                insns, // Compiled expression
                cogen_concat_tab!(
                    match op {
                        Location::Register(Register::RAX) => format!(""), // No need to move to %rax
                        _ => format!("movq {}, %rax", op), // Moves the result to %rax
                    },
                    format!("jmp .LR{}", label.chars().collect::<Vec<char>>()[2]) // Jumps to the return label
                )
            )
        }
        minc_ast::Stmt::Expr(expr) => {
            // Compiles the expression statement
            let (insns, _) = ast_to_asm_expr(expr, env, v); // Compiles the expression
            insns // Returns the compiled expression
        }
        minc_ast::Stmt::Compound(decls, stmts) => {
            // A new compound statement means a new scope
            // Extends the environment with the new variables
            let (env2, v2) = env.extend(decls, Stack::RSP(v)); // Extends the environment from the current stack offset
            cogen_stmts(stmts, env2, v2, label) // Compiles the statements in the new scope
        }
        minc_ast::Stmt::If(cond, then_stmt, Some(else_stmt)) => {
            let (cond_insns, cond_op) = ast_to_asm_expr(cond, env.clone(), v); // Compiles the condition
            let label_lc = next_label(label);
            let label_le = next_label(label);
            cogen_concat!(
                cond_insns, // Compiled condition
                cogen_concat_tab!(
                    format!("cmpq $0, {}", cond_op), // Compares the condition with 0
                    format!("je {}", label_lc) // Jumps to the else part if the condition is false
                ),
                ast_to_asm_stmt(then_stmt, env.clone(), v, label), // Compiles the then statement
                cogen_concat_tab!(format!("jmp {}", label_le)),    // Jumps to the end
                format!("{}:", label_lc),                          // Else part
                ast_to_asm_stmt(else_stmt, env, v, label),         // Compiles the else statement
                format!("{}:", label_le)                           // End
            )
        }
        minc_ast::Stmt::If(cond, then_stmt, None) => {
            let (cond_insns, cond_op) = ast_to_asm_expr(cond, env.clone(), v); // Compiles the condition
            let label_lc = next_label(label);
            cogen_concat!(
                cond_insns, // Compiled condition
                cogen_concat_tab!(
                    format!("cmpq $0, {}", cond_op), // Compares the condition with 0
                    format!("je {}", label_lc)       // Jumps to the end if the condition is false
                ),
                ast_to_asm_stmt(then_stmt, env.clone(), v, label), // Compiles the then statement
                format!("{}:", label_lc)                           // End
            )
        }
        minc_ast::Stmt::While(cond, body) => {
            let (cond_insns, cond_op) = ast_to_asm_expr(cond, env.clone(), v); // Compiles the condition
            let label_lc = next_label(label);
            let label_ls = next_label(label);
            cogen_concat!(
                cogen_concat_tab!(
                format!("jmp {}", label_lc)        // Jumps to the condition part
                ),
                format!("{}:", label_ls),             // Body part
                ast_to_asm_stmt(body, env, v, label), // Compiles the body
                format!("{}:", label_lc),             // Condition part
                cond_insns,                           // Compiled condition
                cogen_concat_tab!(
                    format!("cmpq $0, {}", cond_op), // Compares the condition with 0
                    format!("jne {}", label_ls) // Jumps to the body part if the condition is true
                )
            )
        }
    }
}

/// Takes a list of statements, an environment, stack offset, and a label.
/// Returns the machine code of the statements.
fn cogen_stmts(
    stmts: &Vec<minc_ast::Stmt>,
    env: Environment,
    v: i64,
    label: &mut String,
) -> String {
    // Iterates over the statements and compiles them
    stmts
        .iter()
        .map(|stmt| ast_to_asm_stmt(stmt, env.clone(), v, label)) // Compiles each statement
        .collect::<Vec<String>>()
        .join("\n")
}

/// Takes an expression, an environment, and stack offset.
/// Returns the machine code of the expression and the location of the evaluation result.
fn ast_to_asm_expr(expr: &minc_ast::Expr, env: Environment, v: i64) -> (String, Location) {
    match expr {
        // Integer literal
        minc_ast::Expr::IntLiteral(n) => {
            (format!(""), Location::Immediate(*n)) // Returns the integer literal
        }
        // Variable (Identifier)
        minc_ast::Expr::Id(name) => {
            if let Some(loc) = env.lookup(name) {
                // If the variable is found in the environment
                (format!(""), loc) // Returns the location of the variable
            } else {
                panic!("Variable {} not found", name)
            }
        }
        // Unary/Binary operator expression
        // Extracts the operator and operands
        minc_ast::Expr::Op(op, e) => {
            let op = op.as_str();
            match op {
                // Arithmetic instructions
                "+" | "-" | "*" | "/" | "%" => {
                    match op {
                        "+" | "-" => {
                            // For unary operators
                            if e.len() == 1 {
                                // Compiles the operand
                                let (insns0, op0) = ast_to_asm_expr(&e[0], env, v);
                                match op0 {
                                    // If the operand is an immediate value
                                    Location::Immediate(n) => (
                                        format!(""), // No instructions
                                        match op {
                                            "+" => op0,                     // The result is the operand itself
                                            "-" => Location::Immediate(-n), // Negates the number
                                            _ => panic!("Unknown operator {}", op),
                                        },
                                    ),
                                    _ => (
                                        match op {
                                            "+" => format!("{}\n", insns0), // Compiled operand
                                            "-" => cogen_concat!(
                                                insns0,                                     // Compiled operand
                                                cogen_concat_tab!(format!("negq {}", op0)) // Negates the number
                                            ),
                                            _ => panic!("Unknown operator {}", op),
                                        },
                                        op0, // The result is stored in the operand
                                    ),
                                }
                            } else {
                                // Compiles the second operand
                                let (insns1, op1) = ast_to_asm_expr(&e[1], env.clone(), v);
                                // Compiles the first operand
                                let (insns0, op0) = ast_to_asm_expr(&e[0], env, v + LONG_SIZE);
                                match (op0, op1) {
                                    // If both operands are immediate values
                                    (Location::Immediate(n0), Location::Immediate(n1)) => (
                                        format!(""), // No instructions
                                        Location::Immediate(match op {
                                            "+" => n0 + n1, // Adds the numbers
                                            "-" => n0 - n1, // Subtracts the numbers
                                            _ => panic!("Unknown operator {}", op),
                                        }),
                                    ),
                                    // If the first operand is an immediate value
                                    (Location::Immediate(n0), _) => {
                                        let m = Stack::RSP(v); // Where to copy the second operand
                                        (
                                            cogen_concat!(
                                                insns1, // Compiled second operand
                                                match op1 {
                                                    Location::Stack(_) => cogen_concat_tab!(
                                                        format!("pushq {}", op1),
                                                        format!("popq {}", m)
                                                    ),
                                                    _ => cogen_concat_tab!(format!(
                                                        "movq {}, {}",
                                                        op1, m
                                                    )),
                                                }, // Copies the second operand to the stack
                                                insns0, // Compiled first operand
                                                match op {
                                                    "+" => cogen_concat_tab!(format!(
                                                        "addq ${}, {}",
                                                        n0, m
                                                    )),
                                                    "-" => cogen_concat_tab!(
                                                        format!("subq ${}, {}", n0, m),
                                                        format!("negq {}", m)
                                                    ),
                                                    _ => panic!("Unknown operator {}", op),
                                                }  // Adds or subtracts the numbers
                                            ),
                                            Location::Stack(m),
                                        )
                                    }
                                    // If the second operand is an immediate value
                                    (_, Location::Immediate(n1)) => {
                                        let m = Stack::RSP(v); // Where to copy the first operand
                                        (
                                            cogen_concat!(
                                                insns1, // Compiled second operand
                                                insns0, // Compiled first operand
                                                match op0 {
                                                    Location::Stack(_) => cogen_concat_tab!(
                                                        format!("pushq {}", op0),
                                                        format!("popq {}", m)
                                                    ),
                                                    _ => cogen_concat_tab!(format!(
                                                        "movq {}, {}",
                                                        op0, m
                                                    )),
                                                }, // Copies the first operand to the stack
                                                match op {
                                                    "+" => cogen_concat_tab!(format!(
                                                        "addq ${}, {}",
                                                        n1, m
                                                    )),
                                                    "-" => cogen_concat_tab!(format!(
                                                        "subq ${}, {}",
                                                        n1, m
                                                    )),
                                                    _ => panic!("Unknown operator {}", op),
                                                }  // Adds or subtracts the numbers
                                            ),
                                            Location::Stack(m),
                                        )
                                    }
                                    // If both operands are not immediate values
                                    _ => {
                                        let m = Stack::RSP(v); // Where to copy the second operand
                                        (
                                            cogen_concat!(
                                                insns1, // Compiled second operand
                                                match op1 {
                                                    Location::Stack(_) => cogen_concat_tab!(
                                                        format!("pushq {}", op1),
                                                        format!("popq {}", m)
                                                    ),
                                                    _ => cogen_concat_tab!(format!(
                                                        "movq {}, {}",
                                                        op1, m
                                                    )),
                                                }, // Copies the second operand to the stack
                                                insns0, // Compiled first operand
                                                cogen_concat_tab!(format!("movq {}, %rax", op0)), // Moves the first operand to %rax
                                                match op {
                                                    "+" => cogen_concat_tab!(format!(
                                                        "addq {}, %rax",
                                                        m
                                                    )),
                                                    "-" => cogen_concat_tab!(format!(
                                                        "subq {}, %rax",
                                                        m
                                                    )),
                                                    _ => panic!("Unknown operator {}", op),
                                                }  // Adds or subtracts the numbers
                                            ),
                                            Location::Register(Register::RAX), // The result is stored in %rax
                                        )
                                    }
                                }
                            }
                        }
                        "*" => {
                            // Compiles the second operand
                            let (insns1, op1) = ast_to_asm_expr(&e[1], env.clone(), v);
                            // Compiles the first operand
                            let (insns0, op0) = ast_to_asm_expr(&e[0], env, v + LONG_SIZE);
                            let m = Stack::RSP(v); // Where to copy the second operand
                            (
                                cogen_concat!(
                                    insns1, // Compiled second operand
                                    match op1 {
                                        Location::Stack(_) => cogen_concat_tab!(
                                            format!("pushq {}", op1),
                                            format!("popq {}", m)
                                        ),
                                        _ => cogen_concat_tab!(format!("movq {}, {}", op1, m)),
                                    }, // Copies the second operand to the stack
                                    insns0, // Compiled first operand
                                    cogen_concat_tab!(
                                        format!("movq {}, %rax", op0), // Moves the first operand to %rax
                                        format!("mulq {}", m)
                                    )  // Multiplies the numbers
                                ),
                                Location::Register(Register::RAX), // The result is stored in %rax
                            )
                        }
                        "/" | "%" => {
                            // Compiles the second operand
                            let (insns1, op1) = ast_to_asm_expr(&e[1], env.clone(), v);
                            // Compiles the first operand
                            let (insns0, op0) = ast_to_asm_expr(&e[0], env, v + LONG_SIZE);
                            let m = Stack::RSP(v); // Where to copy the second operand
                            (
                                cogen_concat!(
                                    insns1, // Compiled second operand
                                    match op1 {
                                        Location::Stack(_) => cogen_concat_tab!(
                                            format!("pushq {}", op1),
                                            format!("popq {}", m)
                                        ),
                                        _ => cogen_concat_tab!(format!("movq {}, {}", op1, m)),
                                    }, // Copies the second operand to the stack
                                    insns0, // Compiled first operand
                                    cogen_concat_tab!(
                                        format!("movq {}, %rax", op0), // Moves the first operand to %rax
                                        format!("xor %rdx, %rdx"),     // Clears %rdx
                                        format!("divq {}", m)
                                    )  // Divides the numbers
                                ),
                                match op {
                                    "/" => Location::Register(Register::RAX), // The quotient is stored in %rax
                                    "%" => Location::Register(Register::RDX), // The remainder is stored in %rdx
                                    _ => panic!("Unknown operator {}", op),
                                },
                            )
                        }
                        _ => panic!("Unknown operator {}", op),
                    }
                }
                // Comparison instructions
                "<" | "<=" | ">" | ">=" | "==" | "!=" => {
                    // Compiles the second operand
                    let (insns1, op1) = ast_to_asm_expr(&e[1], env.clone(), v);
                    // Compiles the first operand
                    let (insns0, op0) = ast_to_asm_expr(&e[0], env, v + LONG_SIZE);
                    let m0 = Stack::RSP(v + LONG_SIZE); // Where to copy the first operand
                    let m1 = Stack::RSP(v); // Where to copy the second operand
                    (
                        cogen_concat!(
                            insns1, // Compiled second operand
                            match op1 {
                                Location::Stack(_) => cogen_concat_tab!(
                                    format!("pushq {}", op1),
                                    format!("popq {}", m1)
                                ),
                                _ => cogen_concat_tab!(format!("movq {}, {}", op1, m1)),
                            }, // Copies the second operand to the stack
                            insns0, // Compiled first operand
                            match op0 {
                                Location::Stack(_) => cogen_concat_tab!(
                                    format!("pushq {}", op0),
                                    format!("popq {}", m0)
                                ),
                                _ => cogen_concat_tab!(format!("movq {}, {}", op0, m0)),
                            }, // Copies the first operand to the stack
                            cogen_concat_tab!(
                                "xor %rax, %rax",             // Clears %rax
                                format!("movq {}, %rax", m0), // Restores the first operand
                                format!("cmpq {}, %rax", m1), // Compares the first and second operands
                                // Sets the result to 1 if the condition is true, 0 if not
                                match op {
                                    "<" => "setl %al",
                                    "<=" => "setle %al",
                                    ">" => "setg %al",
                                    ">=" => "setge %al",
                                    "==" => "sete %al",
                                    "!=" => "setne %al",
                                    _ => panic!("Unknown operator {}", op),
                                },
                                "movzbq %al, %rax" // Zero extends %al to %rax
                            )
                        ),
                        Location::Register(Register::RAX), // The result is stored in %rax
                    )
                }
                // Logical instructions
                "!" | "~" => match op {
                    "!" => {
                        if e.len() != 1 {
                            panic!("Expected 1 operand for !")
                        } else {
                            // Compiles the operand
                            let (insns, op) = ast_to_asm_expr(&e[0], env, v);
                            (
                                cogen_concat!(
                                    insns, // Compiled operand
                                    cogen_concat_tab!(
                                        format!("testq {}, {}", op, op), // If the operand is 0, sets ZF to 1
                                        "sete %al",         // Sets %al to 1 if ZF is set
                                        "movzbq %al, %rax"  // Zero extends %al to %rax
                                    )
                                ),
                                Location::Register(Register::RAX), // The result is stored in %rax
                            )
                        }
                    }
                    // Compiles as follows:
                    "~" => {
                        if e.len() != 1 {
                            panic!("Expected 1 operand for ~")
                        } else {
                            // Compiles the operand
                            let (insns, op) = ast_to_asm_expr(&e[0], env, v);
                            (
                                // Bitwise not
                                cogen_concat!(insns, cogen_concat_tab!(format!("notq {}", op))),
                                op, // The result is stored in the operand
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
                        let (insns1, op1) = ast_to_asm_expr(&e[1], env.clone(), v);
                        // Get the location of the first operand
                        if let minc_ast::Expr::Id(x) = &e[0] {
                            // If the variable is found in the environment
                            if let Some(loc) = env.lookup(x) {
                                (
                                    cogen_concat!(
                                        insns1, // Compiled second operand
                                        match op1 {
                                            Location::Stack(_) => cogen_concat_tab!(
                                                format!("pushq {}", op1),
                                                format!("popq {}", loc)
                                            ),
                                            _ =>
                                                cogen_concat_tab!(format!("movq {}, {}", op1, loc)),
                                        }  // Moves the second operand to the first operand
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
        // Function call
        // Extracts the function name and arguments
        minc_ast::Expr::Call(f, args) => {
            // Compiles the arguments
            let (insns, arg_vars) = ast_to_asm_exprs(args, env.clone(), v);
            // Get function name
            match &**f {
                minc_ast::Expr::Id(name) => (
                    cogen_concat!(
                        insns, // Compiled arguments
                        make_call(
                            name.to_string(),
                            arg_vars,
                            env.clone(),
                            v,
                            env.contains_var(name) // Recursive if the environment contains the function itself
                        )  // Get the function call instructions
                    ),
                    Location::Register(Register::RAX), // The result (return value) is stored in %rax
                ),

                _ => panic!("Function name must be an identifier"),
            }
        }
        // Parenthesized expression
        minc_ast::Expr::Paren(sub_expr) => {
            ast_to_asm_expr(sub_expr, env, v) // Compiles the sub-expression
        }
    }
}

/// Takes expressions, an environment, and stack offset.
/// Returns the machine code of the expressions and the locations of the evaluation results.
fn ast_to_asm_exprs(
    args: &Vec<minc_ast::Expr>,
    env: Environment,
    v: i64,
) -> (String, Vec<Location>) {
    // Iterates over the expressions and compiles them
    args.iter()
        .enumerate()
        .map(|(i, arg)| ast_to_asm_expr(arg, env.clone(), v + i as i64 * LONG_SIZE))
        .fold(
            (String::new(), vec![]),
            |(insns_res, mut locs), (insns, op)| {
                locs.push(op); // Adds the location of the evaluation result
                (cogen_concat!(insns_res, insns), locs) // Returns the concatenated compiled expressions and locations
            },
        ) // Returns the compiled expressions and locations
}

/// Takes a function name, arguments, an environment, stack offset, and whether the function is recursive.
/// Returns the machine code of the function call.
fn make_call(f: String, args: Vec<Location>, env: Environment, v: i64, recursive: bool) -> String {
    let mut call_insns: Vec<String> = vec![]; // Function call instructions
    let mut stacked: Vec<Location> = vec![]; // Locations mapped to local variables
    let mut to_copied: Vec<(Location, Location, i64)> = vec![]; // Locations to be copied
    let mut to_passed: Vec<(Location, Location)> = vec![]; // Locations to be passed
    for (i, arg_var) in args.iter().enumerate() {
        // Get the ith argument location specified by ABI
        let arg_pos: Location = if i < ARGS_REGS.len() {
            Location::Register(ARGS_REGS[i])
        } else {
            Location::Stack(Stack::RSP(LONG_SIZE * (i - ARGS_REGS.len() + 1) as i64))
        };
        // If the locations are already mapped to local variables
        if env.contains_loc(arg_pos) {
            call_insns.push(cogen_concat_tab!(format!("pushq {}", arg_pos))); // Pushes the locations to the stack
            stacked.push(arg_pos); // Adds the pushed location
        }
        // Adds the locations to be copied
        to_copied.push((arg_var.clone(), arg_pos, v + LONG_SIZE * i as i64));
    }
    // Copies the locations to be passed (destroyed) to the stack
    for (from, to, loc) in to_copied.iter() {
        // Get the location to be copied
        // If there are stacked locations, adds that amount of space
        let m = Location::Stack(Stack::RSP(*loc + LONG_SIZE * stacked.len() as i64));
        let copy_insns = match from {
            Location::Stack(Stack::RSP(v2)) => cogen_concat_tab!(
                format!(
                    "pushq {}",
                    Stack::RSP(v2 + LONG_SIZE * stacked.len() as i64)
                ),
                format!("popq {}", m)
            ),
            _ => cogen_concat_tab!(format!("movq {}, {}", from, m)),
        }; // Copies the location to the stack
        call_insns.push(copy_insns);
        // Finally, the source location is the copied location
        to_passed.push((m, *to)); // Adds the copied location and the destination location (argument)
    }
    for (from, to) in to_passed.iter() {
        // Moves the locations to be passed to the argument locations
        call_insns.push(cogen_concat_tab!(
            format!("pushq {}", from),
            format!("popq {}", to)
        ));
    }
    // If not recursive, adds and subtracts the stack pointer for return address
    if !recursive {
        call_insns.push(cogen_concat_tab!(format!("addq ${}, %rsp", LONG_SIZE)));
    }
    call_insns.push(cogen_concat_tab!(format!("call {}", f))); // Calls the function
    if !recursive {
        call_insns.push(cogen_concat_tab!(format!("subq ${}, %rsp", LONG_SIZE)));
    }
    // Pops the locations mapped to local variables from the stack
    for arg_pos in stacked.iter().rev() {
        call_insns.push(cogen_concat_tab!(format!("popq {}", arg_pos)));
    }
    call_insns.iter().fold(
        String::new(),
        |res, insns| cogen_concat!(res, insns), // Concatenates the function call instructions
    ) // Returns the function call instructions
}
