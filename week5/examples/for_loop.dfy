method Factorial(n: int) returns (result: int)
  requires n >= 0
  ensures result >= 1
{
  result := 1;
  
  for i := 1 to n
    invariant 1 <= i <= n + 1
    invariant result >= 1
  {
    result := result * i;
  }
}
