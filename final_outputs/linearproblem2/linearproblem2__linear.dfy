method DoubleIncrement(n: int) returns (i: int, j: int)
{
  i := 0;
  j := 0;
  while (i < n && j < 2*n)
  
    invariant i - j <= 0
    invariant 2*i - 2*j <= 9
    invariant 2*i - j <= 0
    invariant 3*i - 3*j <= 1
    invariant 3*i - 2*j <= 0{
    i := i + 1;
    j := j + 2;
  }
}