// Three-mode automaton with a distinct affine relation per mode.
// Disjunctive invariant: (mode == 0 && y == x) || (mode == 1 && y == x + 1) || (mode == 2 && y == x + 2).
method ThreeModeCounter(n: int) returns (x: int, y: int, mode: int)
{
  var i := 0;
  x := 0;
  y := 0;
  mode := 0;

  while (i < n)
  {
    if mode == 0 {
      y := x + 1; // transition to mode 1 with y = x + 1
      mode := 1;
    } else if mode == 1 {
      x := x + 1;
      y := y + 2; // maintains y = x + 2 as we move into mode 2
      mode := 2;
    } else {
      x := x + 2; // entering with y = x + 2, so y stays aligned after the bump
      mode := 0;
    }
    i := i + 1;
  }
}
