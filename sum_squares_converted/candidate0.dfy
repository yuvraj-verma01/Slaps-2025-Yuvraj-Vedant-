module sum_squares
{
  method sum_squares(n: int) returns (ret: int)
    decreases *  // @method_dec_star_if_needed
    requires n >= 0
    ensures ret == n * n
  {
    var i: int:= 0;
    var s: int:= 0;
    while ((i < n))
    // @loop_id:0
    invariant s == i * i
    invariant 0 <= i && i <= n
    decreases n - i;
    {
      s := ((s + (2 * i)) + 1);
      i := (i + 1);
    }
    ret := s;
    return;
  }

}