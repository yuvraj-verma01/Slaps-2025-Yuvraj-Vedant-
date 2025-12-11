// Simple linear counter to keep a fast baseline benchmark.
method LinearCounter(n: int) returns (k: int)
{
  k := 0;
  while (k < n)
  {
    k := k + 1;
  }
}
