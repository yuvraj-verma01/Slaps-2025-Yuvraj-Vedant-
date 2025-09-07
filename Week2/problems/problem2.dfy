// Problem 2: Integer Division (Quotient & Remainder)
// Write loop invariant(s) for this method

method IntegerDivision(dividend: int, divisor: int) returns (quotient: int, remainder: int)
    requires divisor > 0
    requires dividend >= 0 // to avoid negative remainders and invariant 3 holds
    ensures dividend == divisor * quotient + remainder
    ensures 0 <= remainder < divisor
{
    quotient := 0;
    remainder := dividend;
    
    while remainder >= divisor
        invariant dividend == divisor * quotient + remainder
        invariant 0 <= quotient
        invariant 0 <= remainder 
        decreases remainder
    {
        quotient := quotient + 1;
        remainder := remainder - divisor;
    }
}
 