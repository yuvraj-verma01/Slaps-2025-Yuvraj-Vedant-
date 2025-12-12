method Toggle()
    {
        var i := 0;
        var x := 0;
        var y := 0;
        var flip := 0;
        while (i < 4) 
        
          invariant (flip <= 1 && flip + i <= 5) || (2*flip + i <= 10 && 3*flip <= 4 && 3*flip + i <= 7){
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