// Small loop with two alternating modes.
// State space alternates between (mode == 0 && y == x) and (mode == 1 && y == x + 1),
// which is convenient for exercising disjunctive invariants.
method DisjunctiveToggle(n: int) returns (x: int, y: int, mode: int)
{
  var i := 0;
  x := 0;
  y := 0;
  mode := 0;

  while (i < n)
  {
    if mode == 0 {
      y := y + 1;
      mode := 1;
    } else {
      x := x + 1;
      mode := 0;
    }
    i := i + 1;
  }
}
