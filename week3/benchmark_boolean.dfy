method ForcedGoodExample(n: int) returns (a: int, b: int, flag: int)
{
    var i := 0;
    a := 0;
    b := 10;
    flag := 0;

    while i < n
    {
        if flag == 0 {
            a := a + 1;
            b := b - 1;
            flag := 1;
        } else {
            a := a + 2;
            b := b + 3;
            flag := 0;
        }
        i := i + 1;
    }
}


