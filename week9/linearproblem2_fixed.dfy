method DoubleIncrement(n: int) returns (i: int, j: int)
{
  i := 0;
  j := 0;
  while (i < n && j < 2*n)
  
    invariant (-i <= 0 && -j <= 0 && -i - j <= 0){
    i := i + 1;
    j := j + 2;
  }
}