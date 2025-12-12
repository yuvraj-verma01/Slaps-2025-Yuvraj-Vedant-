from z3 import *

def solve_game_of_21():
    
    s = Solver()
    
    # Create boolean variables for each position (0 to 21)
    # Winning[i] = True means position i is a winning position for player whose turn it is
    Winning = [Bool(f'W_{i}') for i in range(22)]
    
    # Base case: Position 0 is LOSING (no objects left, previous player took the last object and won)
    s.add(Not(Winning[0]))
    
    # For each position i > 0:
    # Position i is WINNING if there EXISTS at least one move to a LOSING position
    # (if you can move to a losing position, opponent will be in losing state)
    for i in range(1, 22):
        possible_moves = []
        
        # Try move of 1
        if i >= 1:
            possible_moves.append(Not(Winning[i - 1]))
        
        # Try move of 2
        if i >= 2:
            possible_moves.append(Not(Winning[i - 2]))
        
        # Try move of 3
        if i >= 3:
            possible_moves.append(Not(Winning[i - 3]))
        
        # Position is winning if ANY move leads to losing position
        s.add(Winning[i] == Or(possible_moves))
    
    # Solve
    if s.check() == sat:
        m = s.model()
        
        print("=" * 60)
        print("GAME OF 21 - ANALYSIS")
        print("=" * 60)
        
        # Display winning/losing positions
        print("\nPosition Analysis (W=Winning, L=Losing):")
        print("-" * 60)
        for i in range(22):
            is_winning = m.evaluate(Winning[i])
            status = "WINNING" if is_winning else "LOSING"
            print(f"Position {i:2d}: {status:8s}", end="")
            
            # Show optimal moves for winning positions
            if is_winning and i > 0:
                optimal_moves = []
                for move in [1, 2, 3]:
                    if i >= move and not m.evaluate(Winning[i - move]):
                        optimal_moves.append(move)
                if optimal_moves:
                    print(f"  → Optimal moves: {optimal_moves}")
                else:
                    print()
            else:
                print()
        
        print("\n" + "=" * 60)
        print("RESULTS:")
        print("=" * 60)
        
        first_player_wins = m.evaluate(Winning[21])
        
        if first_player_wins:
            print("✓ First player can always win from position 21.")
            print("\nWINNING STRATEGY:")
            
            # Find the optimal first move
            for move in [1, 2, 3]:
                if not m.evaluate(Winning[21 - move]):
                    print(f"  1. First player should remove {move} object.")
                    print(f"     This leaves opponent at position {21 - move} (LOSING position)")
                    break
            
            print("\n  2. Strategy: Always leave opponent at a multiple of 4")
            print("     Losing positions are: 0, 4, 8, 12, 16, 20")
            print("     After opponent's move, counter to return to multiple of 4")
            
        else:
            print("✗ First player CANNOT guarantee a win from position 21")
            print("  Second player has a winning strategy")
        
        print("=" * 60)
        
        return first_player_wins
    else:
        print("No solution found (shouldn't happen)")
        return None

solve_game_of_21()