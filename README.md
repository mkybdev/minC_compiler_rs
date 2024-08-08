# minC_compiler_rs
minC (subset of C language) Compiler Implementation in Rust

# Supported Features
- Definitions
    - Function Definition

- Types
    - Long (8 bytes) Integer

- Statements
    - Return
    - Compound
        - Braces-enclosed Statements
        - Includes Local Variable Declarations
            - Declarations must be at the beginning
            - Top-level (Global) Variable Declaration Not Supported
    - If
        - If-Else
    - While

- Expressions
    - Assignment
    - Binary / Unary Operations
        - Arithmetic
            - `+, -, *, /, %`
        - Comparative
            - `==, !=, <=, >=, <, >`
        - Logic
            - `!, ~`

- Identifiers
    - `/[A-Za-z_][A-Za-z_0-9]*/`


# TODOs
- Statements
    - Empty
    - Continue
    - Break

- Not Tested Features
    - Parentheses
    - `~` operator
    
- Stack Growth Implementation