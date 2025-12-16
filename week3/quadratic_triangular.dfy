method TriangularSum(n: int) returns (k: int, sum: int)
  requires n >= 0
  ensures sum == n * (n - 1) / 2
{
  k := 0;
  sum := 0;

  while k < n
  // manually added invariants
    invariant 0 <= k <= n
    invariant sum == k * (k - 1) / 2
  {
    sum := sum + k;
    k := k + 1;
  }
}
