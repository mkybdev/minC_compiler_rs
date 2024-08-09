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
        - else if
    - While
        - Continue
        - Break

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
- Stack Growth Implementation