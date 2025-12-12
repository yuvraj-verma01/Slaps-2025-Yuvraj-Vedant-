method TriangularSum(n: int) returns (k: int, sum: int)
  requires n >= 0
  ensures sum == n * (n - 1) / 2
{
  k := 0;
  sum := 0;

  while k < n
  {
    sum := sum + k;
    k := k + 1;
  }
}
