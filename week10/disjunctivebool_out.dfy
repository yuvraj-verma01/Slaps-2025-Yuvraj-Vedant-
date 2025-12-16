method Toggle()
    {
        var i := 0;
        var x := 0;
        var y := 0;
        var flip := 0;
        while (i < 4) 
        invariant flip + i <= 5 || 2*flip + i <= 10{
            if (flip == 0) {
                x := x + 1;
                y := y + 2;
                flip := 1;
            } else {
                x := x + 2;
                y := y + 1;
                flip := 0;
            }
            i := i + 1;
        }
    }

/* Terminal Output

[week10 auto-verify] Synthesized invariants:
    (-flip <= 0 && -i <= 0 && -x <= 0) || (-flip <= 0 && -i <= 0 && -x <= 0)
[week10 auto-verify] Wrote instrumented file to week10\disjunctivebool_out.dfy
[week10 auto-verify] Running: dafny week10\disjunctivebool_out.dfy
Warning: this way of using the CLI is deprecated. Use 'dafny --help' to see help for the new Dafny CLI format

Dafny program verifier finished with 1 verified, 0 errors
*/