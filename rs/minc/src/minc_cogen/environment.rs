use crate::minc_ast;
use crate::minc_cogen::constants::*;
use crate::minc_cogen::location::*;

#[derive(Clone)]
/// Environment for variables in a scope.
pub struct Environment {
    /// Maps variable names to their locations.
    env: std::collections::HashMap<String, Location>,
}

impl Environment {
    /// Returns a new Environment.
    pub fn new() -> Environment {
        Environment {
            env: std::collections::HashMap::new(),
        }
    }

    /// Takes a variable name.
    /// Returns the location of the variable in the environment if it exists.
    pub fn lookup(&self, name: &str) -> Option<Location> {
        let loc = self.env.get(name);
        match loc {
            Some(loc) => Some(*loc),
            None => None,
        }
    }

    /// Takes a Location.
    /// Returns whether there exists a variable mapped to the location in the Environment.
    pub fn contains_loc(&self, loc: Location) -> bool {
        self.env.values().any(|&l| l == loc)
    }

    /// Takes a variable name.
    /// Returns whether the variable exists in the Environment.
    pub fn contains_var(&self, name: &str) -> bool {
        self.env.contains_key(name)
    }

    /// Takes a variable name and a location.
    /// Returns a new environment with the variable added.
    pub fn add(&self, name: &str, loc: Location) -> Environment {
        let mut env2 = Environment {
            env: self.env.clone(),
        };
        // Maps the variable name to the location
        // Shadowing of variables is supported
        env2.env.insert(name.to_string(), loc);
        env2
    }

    /// Takes variable declarations and a stack location.
    /// Maps consecutive adjacent stack locations to the variables declared in decls.
    /// Returns a new environment with the variables added and the next stack location offset.
    pub fn extend(&self, decls: &Vec<minc_ast::Decl>, loc: Stack) -> (Environment, i64) {
        match loc {
            Stack::RSP(loc) => {
                // Iterates over the declarations
                decls.iter().fold((self.clone(), loc), |(env, loc), decl| {
                    // Adds the variable to the environment and increments the stack location offset
                    (
                        env.add(&decl.name, Location::Stack(Stack::RSP(loc))),
                        loc + LONG_SIZE,
                    )
                })
            }
        }
    }
}
