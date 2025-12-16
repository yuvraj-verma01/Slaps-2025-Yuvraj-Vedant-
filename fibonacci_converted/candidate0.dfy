  method nth_fibonacci(n: int) returns (ret: int)
    decreases *  // @method_dec_star_if_needed
    requires n >= 0
    ensures ret >= 0
    ensures n <= 1 ==> ret == n
  {
    if ((n <= 1))
    {
      ret := n;
      return;
    }
    var curr: int := 0;
    var prev1: int := 1;
    var prev2: int := 0;
    var i: int := 2;
    while (i < (n + 1))
    // @loop_id:0
    invariant i <= n + 1
    decreases n - i;
    {
      curr := (prev1 + prev2);
      prev2 := prev1;
      prev1 := curr;
      i := i + (1);
    }
    ret := curr;
    return;
  }
