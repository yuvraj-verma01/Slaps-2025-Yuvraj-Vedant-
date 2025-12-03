# Week 6: Linear Invariant Synthesis

## Overview
This week focuses on implementing linear invariant synthesis. The goal is to 
build a tool that can automatically generate linear invariants of the form 
`ax + by <= c` for given Dafny programs.

## Deliverables
- Restrict invariants to linear forms: ax + by <= c
- Submit: Linear invariant synthesis tool

## Linear Invariant Forms

### Basic Linear Inequalities
- `x <= c` (unary constraints)
- `x + y <= c` (binary constraints)
- `ax + by <= c` (general linear constraints)

### Multiple Constraints
- `x <= 10 ∧ y <= 20` (conjunction)
- `x + y <= 30` (combined constraint)

## Implementation Approach

### 1. Constraint Generation
- Extract loop variables and their relationships
- Generate linear constraints based on loop body
- Create constraint system for Z3

### 2. Invariant Synthesis
- Use Z3 to find satisfying assignments
- Generate candidate invariants
- Validate invariants with Dafny

### 3. Invariant Selection
- Rank invariants by strength
- Select most useful invariants
- Handle multiple candidate invariants