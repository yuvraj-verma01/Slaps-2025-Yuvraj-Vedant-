// Problem 5: Reversing a Number
// Write loop invariant(s) for this method

method ReverseNumber(n: int) returns (rev: int)
    requires n >= 0
    ensures rev == ReverseDigits(n)
{
    rev := 0;
    var num := n;
    
    while num > 0
        // TODO: Write loop invariant(s)
        decreases num
    {
        var digit := num % 10;
        rev := rev * 10 + digit;
        num := num / 10;
    }
}

// Helper function to define what "reversed" means
function ReverseDigits(n: int): int
    requires n >= 0
{
    if n < 10 then n else (n % 10) * Power(10, NumDigits(n) - 1) + ReverseDigits(n / 10)
}

// Helper function to count digits
function NumDigits(n: int): int
    requires n >= 0
{
    if n < 10 then 1 else 1 + NumDigits(n / 10)
}

// Helper function for power (needed for ReverseDigits)
function Power(base: int, exp: int): int
    requires exp >= 0
{
    if exp == 0 then 1 else base * Power(base, exp - 1)
}
