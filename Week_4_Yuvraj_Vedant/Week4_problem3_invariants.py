from z3 import *

def synthesize_loop_invariant():

    print("=" * 70)
    print("Loop Invariant Synthesis")
    print("=" * 70)

    
    # Coefficients
    a = Int('a')
    b = Int('b')
    c = Int('c')
    
    # Variables
    i = Int('i')
    sum_var = Int('sum')
    i_next = Int('i_next')
    sum_next = Int('sum_next')
    n = Int('n')
    
    s = Solver()
    
    # Constraint 1: Initial state satisfies invariant
    s.add(c <= 0)

    
    # Constraint 2: Invariant is preserved

    # Define the transition
    s.add(i_next == i + 1)
    s.add(sum_next == sum_var + i)
    
    # Implication: (invariant before and loop condition) => invariant after
    invariant_before = a * i + b * sum_var + c <= 0
    loop_condition = i < n
    invariant_after = a * i_next + b * sum_next + c <= 0
    
    # For all states, if invariant holds before, it holds after
    # We need: invariant_before and loop_condition => invariant_after


    # Constraints for specific test cases
    
    # no non-trivial invariant
    s.add(Or(a != 0, b != 0))
    
    # Bound the coefficients for practical solutions
    s.add(a >= -10, a <= 10)
    s.add(b >= -10, b <= 10)
    s.add(c >= -100, c <= 100)
    print("    Bounding coefficients: -10 <= a,b <= 10, -100 <= c <= 100")
    

    # For multiple concrete values
    for test_i in range(5):
        test_sum = sum(range(test_i))  # sum = 0+1+2+...+(i-1)
        test_i_next = test_i + 1
        test_sum_next = test_sum + test_i
        
        # If we're in the loop (i < n), n = 10
        test_n = 10
        if test_i < test_n:
            # Invariant before
            inv_before = a * test_i + b * test_sum + c <= 0
            # Invariant after
            inv_after = a * test_i_next + b * test_sum_next + c <= 0
            # Add implication
            s.add(Implies(inv_before, inv_after))
    
    print("-" * 70)
    
    # Find solution
    if s.check() == sat:
        m = s.model()
        a_val = m[a].as_long()
        b_val = m[b].as_long()
        c_val = m[c].as_long()
        
        print(f"\n invariants found - ")
        print(f"  Invariant: {a_val}*i + {b_val}*sum + {c_val} <= 0")
        
        terms = []
        if a_val != 0:
            terms.append(f"{a_val}*i" if a_val != 1 else "i")
        if b_val != 0:
            terms.append(f"{b_val}*sum" if b_val != 1 else "sum")
        if c_val != 0:
            terms.append(str(c_val))
        
        inv_str = " + ".join(terms).replace("+ -", "- ")
        print(f"  Simplified: {inv_str} <= 0")
        
        # Verify the invariant
        print("\n" + "=" * 70)
        print("Verification")
        print("=" * 70)
        verify_invariant(a_val, b_val, c_val)
        
        return (a_val, b_val, c_val)
    else:
        print("\n No invariant found")
        print("  Trying alternative approach")
        
        # Try simpler invariants
        simple_invariants = [
            (-1, 0, 0, "-i <= 0 (i.e., i >= 0)"),
            (0, -1, 0, "-sum <= 0 (i.e., sum >= 0)"),
            (1, 0, 0, "i <= 0 (trivial, fails)"),
        ]
        
        for a_val, b_val, c_val, desc in simple_invariants:
            print(f"\n  Testing: {desc}")
            if verify_invariant(a_val, b_val, c_val, verbose=False):
                print(f"     This works.")
                return (a_val, b_val, c_val)
        
        return None


def verify_invariant(a, b, c, n_vals=[5, 10, 20], verbose=True):
    """
    Verify that the invariant a*i + b*sum + c <= 0 holds throughout loop execution
    """
    
    if verbose:
        print(f"\nVerifying invariant: {a}*i + {b}*sum + {c} <= 0")
        print("-" * 70)
    
    all_valid = True
    
    for n in n_vals:
        if verbose:
            print(f"\nTest with n = {n}:")
            print(f"{'Iter':<6} {'i':<6} {'sum':<8} {'Invariant':<20} {'Holds?':<8}")
            print("-" * 50)
        
        i = 0
        sum_var = 0
        iteration = 0
        
        # Check initial state
        inv_val = a * i + b * sum_var + c
        holds = inv_val <= 0
        if verbose:
            print(f"{'Init':<6} {i:<6} {sum_var:<8} {inv_val:<20} {'✓' if holds else '✗':<8}")
        all_valid = all_valid and holds
        
        # Execute loop
        while i < n:
            sum_var = sum_var + i
            i = i + 1
            iteration += 1
            
            inv_val = a * i + b * sum_var + c
            holds = inv_val <= 0
            if verbose:
                print(f"{iteration:<6} {i:<6} {sum_var:<8} {inv_val:<20} {'✓' if holds else '✗':<8}")
            all_valid = all_valid and holds
            
            if not holds:
                if verbose:
                    print(f"  invariant violated.")
                break
        
        if verbose and holds:
            print(f" Invariant holds for all iterations with n={n}")
    
    if verbose:
        print("\n" + "=" * 70)
        if all_valid:
            print("Invariant is valid.")
        else:
            print("Invariant is violated.")
        print("=" * 70)
    
    return all_valid


result = synthesize_loop_invariant()
