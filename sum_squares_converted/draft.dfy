module sum_squares
{
  method sum_squares(n: int) returns (ret: int)
    decreases *  // @method_dec_star_if_needed
    // @requires_placeholder
    // @ensures_placeholder
  {
    var i: int := 0;
    var s: int := 0;
    while ((i < n))
    // @loop_id:0
    invariant true // @inv_placeholder:0
    decreases * // @dec_placeholder:0;
    {
      s := ((s + (2 * i)) + 1);
      i := (i + 1);
    }
    ret := s;
    return;
  }

}