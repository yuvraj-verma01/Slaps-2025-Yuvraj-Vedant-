method ToggleBooleanExample() returns (x: int, z: int)
{
    var i := 0;
    x := 2;
    z := 0;

    while i < 4
        decreases 4 - i
    {
        x := -x;
        z := 1 - z;
        i := i + 1;
    }
}