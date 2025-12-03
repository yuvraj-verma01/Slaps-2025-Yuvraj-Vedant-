# Week 7: Automated Correctness Checking

## Overview
This week focuses on automating the correctness checking process. The goal is 
to build a pipeline that can automatically insert synthesized invariants into 
Dafny programs and verify their correctness using Dafny's built-in verification
engine.

## Verification Pipeline

### Step 1: Parse Original Program
- Extract loop information
- Identify insertion points
- Preserve program structure

### Step 2: Insert Synthesized Invariants
- Add invariant clauses to loops
- Maintain proper syntax
- Handle multiple invariants

### Step 3: Generate Verification Code
- Create complete Dafny program
- Include all necessary imports
- Ensure proper formatting

### Step 4: Run Dafny Verification
- Execute Dafny verification
- Parse verification results
- Report success/failure

## Implementation Requirements

### Invariant Insertion
Your tool should be able to:
1. **Parse Dafny programs**: Handle method declarations and loop constructs
2. **Insert invariants**: Add invariant clauses to appropriate loops
3. **Maintain syntax**: Ensure proper Dafny syntax and formatting
4. **Handle multiple invariants**: Support multiple invariant clauses per loop

### Verification Pipeline
Your pipeline should:
1. **Automate the process**: No manual intervention required
2. **Handle errors gracefully**: Report verification failures clearly
3. **Provide feedback**: Show which invariants work and which don't
4. **Support batch processing**: Handle multiple programs

## Example Workflow

### Input: Original Program
```dafny
method Sum(n: int) returns (result: int)
  requires n >= 0
{
  var i := 0;
  var sum := 0;
  
  while (i <= n)
  {
    sum := sum + i;
    i := i + 1;
  }
  
  result := sum;
}
```

### Input: Synthesized Invariants
```json
{
  "invariants": [
    "0 <= i <= n + 1",
    "sum == i * (i - 1) / 2"
  ]
}
```

### Output: Program with Invariants
```dafny
method Sum(n: int) returns (result: int)
  requires n >= 0
{
  var i := 0;
  var sum := 0;
  
  while (i <= n)
    invariant 0 <= i <= n + 1
    invariant sum == i * (i - 1) / 2
  {
    sum := sum + i;
    i := i + 1;
  }
  
  result := sum;
}
```

### Verification Result
```
Dafny program verifier finished with 0 verified, 0 errors
```