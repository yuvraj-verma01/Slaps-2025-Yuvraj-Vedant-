method ToggleEvenOdd(n: int) returns (i: int, pos: int, neg: int)
{
  i := 0;
  pos := 0;
  neg := 0;

  while i < n
  
    invariant (i - pos <= 0 && 3*i - 2*neg - pos <= 10) || (3*i - neg - 3*pos <= 0 && 3*i - neg - 2*pos <= 0 && 3*i - 3*pos <= 1){
    if i % 2 == 0 {
      pos := pos + 1;
    } else {
      neg := neg + 1;
    }
    i := i + 1;
  }
}
