method Toggle()
    {
        var i := 0;
        var x := 0;
        var y := 0;
        var flip := 0;
        while (i < 4) 
        
          invariant (-flip <= 0 && -i <= 0 && -x <= 0){
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