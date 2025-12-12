method Counter(n: int) returns (i: int)
{
  i := 0;
  while (i < n)
  
    invariant (-i <= 0 && -i <= 1){
    i := i + 1;
  }
}