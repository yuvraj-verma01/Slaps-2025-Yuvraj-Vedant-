method ToggleEvenOdd(n: int) returns (i: int, pos: int, neg: int)
{
  i := 0;
  pos := 0;
  neg := 0;

  while i < n
  {
    if i % 2 == 0 {
      pos := pos + 1;
    } else {
      neg := neg + 1;
    }
    i := i + 1;
  }
}
