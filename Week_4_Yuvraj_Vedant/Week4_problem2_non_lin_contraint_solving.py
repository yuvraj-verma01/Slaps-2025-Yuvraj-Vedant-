from z3 import *

def solve_nonlinear_system():
    print("\n" + "=" * 60)
    
    x = Int('x')
    y = Int('y')
    
    s = Solver()
    
    # Add constraints
    s.add(x * x + y * y == 25)  # x² + y² = 25
    s.add(x + y == 7)            # x + y = 7
    s.add(x > 0)                 # x > 0
    s.add(y > 0)                 # y > 0
    
    # Find all solutions
    solutions = []
    
    print("Searching for solutions")
    print("-" * 60)
    
    while s.check() == sat:
        m = s.model()
        x_val = m[x].as_long()
        y_val = m[y].as_long()
        
        solutions.append((x_val, y_val))
        
        print(f"\nSolution found: x = {x_val}, y = {y_val}")
        print(f"  Verification:")
        print(f"    x² + y² = {x_val}² + {y_val}² = {x_val**2} + {y_val**2} = {x_val**2 + y_val**2}")
        print(f"    x + y = {x_val} + {y_val} = {x_val + y_val}")
        print(f"    x > 0: {x_val} > 0")
        print(f"    y > 0: {y_val} > 0")
        
        # Block this solution to find others
        s.add(Or(x != x_val, y != y_val))
    
    print("\n" + "=" * 60)
    print("Results:")
    print("=" * 60)
    
    if solutions:
        print(f"\nTotal solutions found: {len(solutions)}")
        print("\nAll integer solutions:")
        for i, (x_val, y_val) in enumerate(solutions, 1):
            print(f"  Solution {i}: (x={x_val}, y={y_val})")
    else:
        print("\nNo integer solutions exist for this system.")
    

    
    return solutions


solutions = solve_nonlinear_system()