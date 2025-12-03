
// Problem 5: Reversing a Number
// Write loop invariant(s) for this method

method ReverseNumber(n: int) returns (rev: int)
    requires n >= 0
    ensures rev == ReverseDigits(n)
{
    rev := 0;
    var num := n;
    while num > 0
        invariant rev >= 0
        invariant num >= 0
        invariant NumDigits(num) > 0
        invariant ReverseDigits(n) == rev * Power(10, NumDigits(num)) + ReverseDigits(num)
        decreases num
    {
        if num >= 10{
            assert ReverseDigits(num) == (num % 10) * Power(10, NumDigits(num) - 1) + ReverseDigits(num/10) by {Reverse_Digits_Logic(num);}
        }
        var digit := num % 10; // unit
        rev := rev * 10 + digit; // push up
        num := num / 10; // remove unit
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
    ensures NumDigits(n) >= 1 // I added this to prevent an error in line: 27 Power(10, NumDigits(n) - 1) (exp >= 0)
{
    if n < 10 then 1 else 1 + NumDigits(n / 10)
}

// Helper function for power (needed for ReverseDigits)
function Power(base: int, exp: int): int
    requires exp >= 0
{
    if exp == 0 then 1 else base * Power(base, exp - 1)
}

lemma {:auto} NumDigits_Update(num: int)
    requires num >= 10
    ensures NumDigits(num) == 1 + NumDigits(num/10)
{}

lemma {:auto} Reverse_Digits_Logic(n: int)
    requires n >= 10
    ensures ReverseDigits(n) == (n % 10) * Power(10, NumDigits(n) - 1) + ReverseDigits(n / 10)
{}

// Problems I came across:
//  - invariant ReverseDigits(n) == rev * Power(10, NumDigits(num)) + ReverseDigits(num)
//  - ensures rev == ReverseDigits(n)
