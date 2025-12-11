// Two-phase loop that alternates between b == a and b == a + 2.
// This exercises a genuine disjunctive invariant: (flag == 0 && b == a) || (flag == 1 && b == a + 2).
method OffsetToggle(n: int) returns (a: int, b: int, flag: int)
{
  var i := 0;
  a := 0;
  b := 0;
  flag := 0;

  while i < n
  {
    if flag == 0 {
      a := a + 1;
      b := a + 2; // uses updated a, leaving state in the flag==1 branch shape
      flag := 1;
    } else {
      a := a + 2;
      b := a; // uses updated a, returning to the flag==0 branch shape
      flag := 0;
    }
    i := i + 1;
  }
}
