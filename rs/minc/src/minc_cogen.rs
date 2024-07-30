use crate::minc_ast;

// Terminology:
// BFS - offset value from the Beginning of the Free Space of the stack (not Breadth-First Search)
// location - offset value of the variable address from the base pointer of the stack
// scope - a block of code where variables are defined and used
// _op - _operand
// _insns - _instructions

#[allow(unreachable_code, unused_variables)]
/// Takes a program
/// Concatenates the following in this order:
///     Header
///     Individual function definitions
///     Trailer
/// Returns the concatenated string as the machine code of the program
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
/// Returns the header part of the machine code
fn header() -> String {
    format!("")
}

#[allow(unreachable_code, unused_variables)]
/// Returns the trailer part of the machine code
fn trailer() -> String {
    format!("")
}

#[allow(unreachable_code, unused_variables)]
#[derive(Clone)]
/// Environment for variables in a scope
struct Environment {
    /// Maps variable names to their locations
    env: std::collections::HashMap<String, i64>,
}

#[allow(unreachable_code, unused_variables)]
impl Environment {
    /// Returns a new environment
    fn new() -> Environment {
        Environment {
            env: std::collections::HashMap::new(),
        }
    }

    /// Takes a variable name
    /// Returns the location string of the variable in the environment if it exists
    fn lookup(&self, x: &str) -> Option<String> {
        let loc = self.env.get(x);
        match loc {
            Some(loc) => Some(format!("{:?}(%rsp)", loc)),
            None => None,
        }
    }

    /// Takes a variable name and a location
    /// Returns a new environment with the variable added
    fn add(&self, x: &str, loc: i64) -> Environment {
        let mut env2 = Environment {
            env: self.env.clone(),
        };
        // Maps the variable name to the location
        // This means that the shadowing of variables is not supported
        env2.env.insert(x.to_string(), loc);
        env2
    }

    /// Takes a list of variable declarations, an environment, and a location
    /// Assigns locations (v, v+8, v+16, ...) to the variables declared in decls
    /// Returns a new environment with the variables added and the next location
    fn extend(&self, decls: &Vec<minc_ast::Decl>, loc: i64) -> (Environment, i64) {
        let env2 = Environment {
            env: self.env.clone(),
        };
        // Iterates over the declarations
        decls.iter().fold((env2, loc), |(env, loc), decl| {
            // Adds the variable to the environment and increments BFS
            (env.add(&decl.name, loc), loc + 8)
        })
    }
}

#[allow(unreachable_code, unused_variables)]
/// Takes a top-level definition
/// Concatenates the following in this order:
///      Prologue (Grows stack, saves arguments)
///      Function body
///      Epilogue (Shrinks stack, returns value)
/// Returns the concatenated string as the machine code of the function definition
fn ast_to_asm_def(def: &minc_ast::Def) -> String {
    // Always a function definition for now
    match def {
        // Extracts the function name, parameters, return type, and body
        minc_ast::Def::Fun(name, params, return_type, body) => {
            format!(
                "{}\n{}\n{}\n",
                gen_prologue(def),
                ast_to_asm_stmt(body, Environment::new(), 0), // Compiles the function body
                gen_epilogue(def)
            )
        }
    }
}

#[allow(unreachable_code, unused_variables)]
/// Takes a definition
/// Returns the prologue part of the definition
fn gen_prologue(def: &minc_ast::Def) -> String {
    format!("")
}

#[allow(unreachable_code, unused_variables)]
/// Takes a definition
/// Returns the epilogue part of the definition
fn gen_epilogue(def: &minc_ast::Def) -> String {
    format!("")
}

#[allow(unreachable_code, unused_variables)]
/// Takes a statement, an environment, and BFS
/// Returns the machine code of the statement
fn ast_to_asm_stmt(stmt: &minc_ast::Stmt, env: Environment, v: i64) -> String {
    match stmt {
        minc_ast::Stmt::Empty => format!(""),
        minc_ast::Stmt::Continue => format!(""),
        minc_ast::Stmt::Break => format!(""),
        minc_ast::Stmt::Return(expr) => format!(""),
        minc_ast::Stmt::Expr(expr) => format!(""),
        minc_ast::Stmt::Compound(decls, stmts) => {
            // A new compound statement means a new scope
            // Extends the environment with the new variables
            let (env2, v2) = env.extend(decls, v);
            cogen_stmts(stmts, env2, v2)
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
            let (cond_op, cond_insns) = ast_to_asm_expr(cond, env.clone(), v); // Compiles the condition
            format!(
                "{}\n{}\n{}\n{}\n{}\n{}\n{}\n",
                "jmp .Lc",
                ".Ls:",
                ast_to_asm_stmt(body, env, v), // Compiles the body
                ".Lc:",
                cond_insns,
                format!("cmpq $0, {}", cond_op),
                "jne .Ls"
            )
        }
    }
}

#[allow(unreachable_code, unused_variables)]
/// Takes a list of statements, an environment, and BFS
/// Returns the machine code of the statements
fn cogen_stmts(stmts: &Vec<minc_ast::Stmt>, env: Environment, v: i64) -> String {
    stmts
        .iter()
        .map(|stmt| ast_to_asm_stmt(stmt, env.clone(), v)) // Compiles each statement
        .collect::<Vec<String>>()
        .join("\n")
}

#[allow(unreachable_code, unused_variables)]
/// Takes an expression, an environment, and BFS
/// Returns the machine code of the expression and the location of the result
fn ast_to_asm_expr(expr: &minc_ast::Expr, env: Environment, v: i64) -> (String, i64) {
    match expr {
        minc_ast::Expr::IntLiteral(n) => (format!(""), v),
        minc_ast::Expr::Id(x) => {
            // If the variable is found in the environment
            if let Some(loc) = env.lookup(x) {
                // Moves the variable to the stack
                (format!("movq {}, {}(%rsp)", loc, v), v)
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
                        //    addq [Second operand in stack], [First operand]
                        "+" => {
                            // Compiles the second operand
                            let (insns1, op1) = ast_to_asm_expr(&e[1], env.clone(), v);
                            // Compiles the first operand
                            // The second operand is compiled first to ensure that the result is stored in the first operand
                            let (insns0, op0) = ast_to_asm_expr(&e[0], env, v + 8);
                            let m = format!("{}(%rsp)", v); // Where to copy the second operand
                            (
                                format!(
                                    "{}\n{}\n{}\n{}\n",
                                    insns1, // Compiles the second operand
                                    format!("movq {}, {}", op1, m), // Copies the second operand to the stack
                                    insns0,                         // Compiles the first operand
                                    format!("addq {}, {}", m, op0) // Adds the first operand to the second operand
                                ),
                                op0, // The result is stored in the first operand
                            )
                        }
                        _ => panic!("Unknown operator {}", op),
                    }
                }
                // Comparison instructions
                "<" | "<=" | ">" | ">=" | "==" | "!=" => {
                    match op {
                        // Compiles as follows:
                        //    [Compiled second operand]
                        //    movq [Second operand], [Stack]
                        //    [Compiled first operand]
                        //    movq [First operand], [Stack]
                        //    movq $0, %rax
                        //    movq [First operand in stack], [First operand]
                        //    cmpq [Second operand in stack], [First operand]
                        //    setl %al
                        "<" => {
                            // Compiles the second operand
                            let (insns1, op1) = ast_to_asm_expr(&e[1], env.clone(), v);
                            // Compiles the first operand
                            let (insns0, op0) = ast_to_asm_expr(&e[0], env, v + 8);
                            let m0 = format!("{}(%rsp)", v); // Where to copy the first operand
                            let m1 = format!("{}(%rsp)", v + 8); // Where to copy the second operand
                            (
                                format!(
                                    "{}\n{}\n{}\n",
                                    format!("movq {}, {}", op1, m1), // Copies the second operand to the stack
                                    insns0,
                                    format!(
                                        "{}\n{}\n{}\n{}\n{}\n",
                                        format!("movq {}, {}", op0, m0), // Copies the first operand to the stack
                                        "movq $0, %rax", // Initializes the result to 0
                                        format!("movq {}, {}", m0, op0), // Restores the first operand
                                        format!("cmpq {}, {}", m1, op0), // Compares the first and second operands
                                        "setl %al" // Sets the result to 1 if the first operand is less than the second operand
                                    ),
                                ),
                                op0, // The result is stored in the first operand
                            )
                        }
                        _ => panic!("Unknown operator {}", op),
                    }
                }
                _ => panic!("Unknown operator {}", op),
            }
        }
        minc_ast::Expr::Call(f, args) => {
            // arg_vars: The locations of the arguments
            let (insns, arg_vars) = ast_to_asm_exprs(args, env.clone(), v);
            let arg_regs = vec!["%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9"];
            let mut call_insns = arg_vars
                .iter()
                .enumerate()
                .map(|(i, arg_var)| {
                    format!(
                        "movq {}, {}",
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
            call_insns.push_str(&format!("call {}@PLT", ast_to_asm_expr(f, env, v).0));
            (format!("{}\n{}", insns, call_insns), arg_vars[0])
        }
        minc_ast::Expr::Paren(sub_expr) => (format!(""), v),
    }
}

#[allow(unreachable_code, unused_variables)]
fn ast_to_asm_exprs(args: &Vec<minc_ast::Expr>, env: Environment, v: i64) -> (String, Vec<i64>) {
    args.iter()
        .enumerate()
        .map(|(offset, expr)| ast_to_asm_expr(expr, env.clone(), v + offset as i64 * 8))
        .fold(
            (format!(""), Vec::new()),
            |(insns, mut arg_vars), (insns2, arg_var)| {
                arg_vars.push(arg_var);
                (format!("{}\n{}", insns, insns2), arg_vars)
            },
        )
}
