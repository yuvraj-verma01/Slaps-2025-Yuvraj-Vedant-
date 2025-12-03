# Parser Implementation Guide

## Overview
This guide provides detailed instructions for implementing a Dafny parser that 
can extract loop variables, pre-conditions, and post-conditions from Dafny 
programs.

## Dafny Syntax Elements to Parse

### 1. Method Declarations
```dafny
method MethodName(param1: int, param2: int) returns (result: int)
  requires param1 >= 0
  ensures result >= 0
{
  // method body
}
```

### 2. Loop Constructs
```dafny
// While loop
while (condition)
  invariant invariant_expression
{
  // loop body
}

// For loop
for i := 0 to n
  invariant invariant_expression
{
  // loop body
}
```

### 3. Assertions and Specifications
```dafny
requires condition    // Pre-condition
ensures condition     // Post-condition
invariant condition   // Loop invariant
assert condition      // Assertion
```

## Implementation Approach

### Option 1: AST-based Parsing
- Use a Dafny parser library if available
- Parse to Abstract Syntax Tree (AST)
- Traverse AST to extract required information

### Option 2: Regex-based Parsing
- Use regular expressions to identify patterns
- Simpler but less robust
- Good for initial implementation

### Option 3: Custom Parser
- Implement a recursive descent parser
- More control but more complex
- Best for learning parsing concepts

## Key Components to Extract

### Loop Variables
- Variables modified within loop body
- Loop counter variables
- Variables used in loop condition

### Pre-conditions
- `requires` clauses in method signatures
- Initial variable values
- Input constraints

### Post-conditions
- `ensures` clauses in method signatures
- Final variable values
- Output constraints

## Implementation Steps

1. **Tokenization**: Break input into tokens
2. **Parsing**: Build parse tree or AST
3. **Extraction**: Traverse tree to find required elements
4. **Output**: Format extracted information

## Resources

- Dafny Language Reference: https://dafny.org/dafny/
- Parsing Techniques: Recursive Descent Parsing
- AST Traversal: Visitor Pattern
