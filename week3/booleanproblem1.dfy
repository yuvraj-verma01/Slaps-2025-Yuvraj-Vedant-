method ToggleY() returns (y:int)
{
  y := 0;
  var i := 0;

  while i < 4
    invariant 0 <= i <= 4
    invariant y == 0 || y == 1
    decreases 4 - i
  {
    y := 1 - y;
    i := i + 1;
  }
}
