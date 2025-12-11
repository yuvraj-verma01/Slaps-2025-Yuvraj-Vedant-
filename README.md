# Invariant Synthesis Course Project

**Course**: CS-5310 Symbolic Logic and Applications

## Project Overview
This semester-long project is designed as a continuous, research-oriented exercise in program verification and automated reasoning. Students will progressively build a tool for invariant synthesis. You may work in groups of 2 for this project.

**Total Marks: 40**

## Learning Objectives
- Understand the fundamentals of program verification and invariant synthesis
- Gain hands-on experience with formal verification tools (Dafny, Z3)
- Develop skills in automated reasoning and constraint solving
- Build a practical tool for program analysis

## Prerequisites
- Basic programming knowledge (Python, OCaml, or similar)
- Understanding of logic and mathematical reasoning
- Familiarity with loop invariants and proofs of correctness

## Tools and Technologies
- **Dafny**: Microsoft's verification-aware programming language ([https://dafny.org](https://dafny.org))
  - **Textbook**: [Program Proofs](https://mitpress.mit.edu/9780262046402/program-proofs/) by K. Rustan M. Leino
- **Z3**: Microsoft's theorem prover ([https://github.com/Z3Prover/z3](https://github.com/Z3Prover/z3))
  - **Textbook**: [The Calculus of Computation](https://link.springer.com/book/10.1007/978-3-540-74113-8) by Bradley and Manna
- **Python/OCaml**: For implementing the synthesis tool
- **Git**: For version control and collaboration

## Weekly Breakdown

### Week 1: Setup and Environment Installation
**Deliverables:**
- Install Dafny, Z3, and related tools
- Create a GitHub repository and give access to the course instructor and teaching assistant:
  - **Instructor**: [aalok-thakkar](https://github.com/aalok-thakkar)  
  - **Teaching Assistant**: [smayanagarwal](https://github.com/smayanagarwal)
- Test Dafny on 3 example programs to familiarize themselves with the workflow
- Submit: Repository link and test results

### Week 2: Manual Loop Invariant Writing
**Deliverables:**
- Write loop invariants by hand for 5 given problems
- Provide a summary/explanation of loop invariants provided in class
- Start reading CSUR14 survey paper ("Loop invariants: analysis, classification, and examples")
- Submit: Solutions with detailed explanations

### Week 3: Benchmark Creation and Analysis
**Deliverables:**
- Contribute 8 benchmark problems of your own design
- Problems should be difficult enough that standard tools/LLMs cannot trivially solve them
- Write invariants for these problems and validate them with Dafny verification
- Complete reading the CSUR14 survey paper
- Submit: Benchmark problems with solutions

### Week 4: Z3 Problem Solving
**Deliverables:**
- Solve 3 small problems using Z3 theorem prover
- Practice constraint solving and satisfiability checking
- Submit: Solutions to Z3 problems with explanations

### Week 5: Parsing and Extraction
**Deliverables:**
- Implement parsing and extraction: Given a Dafny program, the tool should output:
  - Loop variables
  - Pre-conditions
  - Post-conditions
- Submit: Working parser with test cases

### Week 6: Linear Invariant Synthesis
**Deliverables:**
- Restrict invariants to linear forms: ax + by <= c
- Submit: Linear invariant synthesis tool

### Week 7: Automated Correctness Checking
**Deliverables:**
- Automating correctness checking: The synthesized invariant should be inserted into the original program
- Dafny should automatically verify the correctness
- Submit: Automated verification pipeline

### Week 8: Research Survey and Positioning
**Deliverables:**
- Read the research papers provided and identify how to situate your work within the larger invariant synthesis landscape

### Week 9: Boolean Combination of Invariants
**Deliverables:**
- Extend the synthesis tool to generate boolean combinations of linear invariants
- Support invariants of the form: (ax + by ≤ c) ∧ (dx + ey ≤ f) ∨ (gx + hy ≤ i)
- Test against benchmark problems requiring boolean combinations
- Submit: Extended synthesis tool with boolean invariant support

### Week 10: Disjunctive Invariant Synthesis
**Deliverables:**
- Implement disjunctive invariant synthesis for programs with multiple execution paths
- Handle cases where different loop iterations require different invariants
- Test with programs that have conditional statements within loops
- Submit: Disjunctive invariant synthesis tool with test cases

### Week 11: Non-linear Invariants - Quadratic Forms
**Deliverables:**
- Extend synthesis to quadratic invariants: ax² + by² + cxy + dx + ey + f ≤ 0
- Implement constraint solving for non-linear forms using Z3
- Test against problems requiring quadratic relationships
- Submit: Quadratic invariant synthesis tool

### Week 12-13: Creative Extensions and Final Presentation
**Deliverables:**
- Creative extensions of their invariant synthesis tool. Options include:
  - Extending to lists and arrays
  - Extending from integers to floats
  - Handling nested loops
  - Translating programs written in Python/OCaml/C → Dafny (LLM-aided)
  - Exploring learning-based invariant generation approaches
  - Implementing invariant ranking and selection mechanisms
  - Adding support for temporal properties and liveness invariants
- Submit: Extended tool with documentation and final presentation

## Evaluation Criteria
- **Technical Implementation (30 marks)**: Quality and functionality of the synthesis tool
- **Benchmark Quality (5 marks)**: Difficulty and relevance of created benchmarks
- **Performance on Benchmarks (20 marks)**: Quality and functionality of the synthesis tool
- **Research Understanding (15 marks)**: Comprehension of related work
- **Documentation and Presentation (10 marks)**: Clarity and completeness of documentation

## Submission Guidelines
- All code must be well-documented and commented
- Include test cases for all functionality
- Provide clear installation and usage instructions
- Use version control (Git) throughout the project

## Academic Integrity
- Collaboration within your group is encouraged
- Sharing of benchmark problems between groups is allowed
- Code sharing between groups is not permitted
- All work must be original or properly cited

Good luck with your invariant synthesis project!
