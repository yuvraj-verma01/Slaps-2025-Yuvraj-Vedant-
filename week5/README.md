# Week 5: Parsing and Extraction

## Overview
This week focuses on implementing parsing and extraction capabilities for Dafny 
programs. The goal is to build a tool that can analyze Dafny code and extract 
key components needed for invariant synthesis.

## Deliverables
- Implement parsing and extraction: Given a Dafny program, the tool should 
output:
  - Loop variables
  - Pre-conditions
  - Post-conditions
- Submit: Working parser with test cases

## Materials

### 1. Parser Implementation Guide
The `parser_guide.md` file provides instructions for implementing the parser.

### 2. Example Dafny Programs
Use the examples from previous weeks to test your parser.

## Implementation Requirements

### Parser Features
Your parser should be able to:
1. **Parse Dafny syntax**: Handle method declarations, loop constructs, and assertions
2. **Extract loop information**: Identify loop variables and their types
3. **Extract pre-conditions**: Find `requires` clauses and initial conditions
4. **Extract post-conditions**: Find `ensures` clauses and final conditions

### Output Format
The parser should output structured data (JSON, XML, or similar) containing:
```json
{
  "loops": [
    {
      "variables": ["i", "j"],
      "loop_type": "while",
      "condition": "i < n"
    }
  ],
  "preconditions": ["n >= 0"],
  "postconditions": ["result == sum"]
}
```