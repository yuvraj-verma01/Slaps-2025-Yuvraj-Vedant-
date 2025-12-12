method SumOfSquares(n: int) returns (i: int, s: int)
  requires n >= 0
  ensures s == n * n
{
  i := 0;
  s := 0;
  while i < n
  {
    s := s + 2 * i + 1;
    i := i + 1;
  }
}
