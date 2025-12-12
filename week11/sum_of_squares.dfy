method SumOfSquares(n: int) returns (i: int, s: int)
  requires n >= 0
  ensures s == n * n
{
  i := 0;
  s := 0;
  while i < n

    // manually added invariants
    invariant 0 <= i <= n
    invariant s == i * i

    // synthesized invariants
    invariant -1*i*i + 1*s <= 0
    invariant 1*i*i - 1*s <= 0
    invariant -1*i*i + 1*s - 1 <= 0
    invariant 1*i*i - 1*s - 1 <= 0
    invariant -1*i*i + 1*s - 2 <= 0
    invariant 1*i*i - 1*s - 2 <= 0


  {
    s := s + 2 * i + 1;
    i := i + 1;
  }
}

/*
Terminal output:
{  
  "file": "week3\\quadratic_sum_of_squares.dfy",
  "methods": [                                                                 
    {
      "method_name": "SumOfSquares",
      "preconditions": [
        "n >= 0"
      ],
      "postconditions": [
        "s == n * n"
      ],
      "parameters": [
        {
          "name": "n",
          "type": "int"
        }
      ],
      "returns": [
        {
          "name": "i",
          "type": "int"
        },
        {
          "name": "s",
          "type": "int"
        }
      ],
      "loops": [
        {
          "condition": "i < n",
          "variables": [
            "i",
            "s"
          ],
          "template_variables": [
            "i",
            "s"
          ],
          "quadratic_invariants": [
            "-1*i*i + 1*s <= 0",
            "1*i*i - 1*s <= 0",
            "-1*i*i + 1*s - 1 <= 0",
            "1*i*i - 1*s - 1 <= 0",
            "-1*i*i + 1*s - 2 <= 0",
            "1*i*i - 1*s - 2 <= 0"
          ],
          "template": "a*x^2 + b*y^2 + c*x*y + d*x + e*y + f <= 0"
        }
      ]
    }
  ]
}*/