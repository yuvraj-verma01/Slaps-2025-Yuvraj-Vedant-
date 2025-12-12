method TriangularSum(n: int) returns (k: int, sum: int)
  requires n >= 0
  ensures sum == n * (n - 1) / 2
{
  k := 0;
  sum := 0;

  while k < n
    // manually added invariants
    invariant 0 <= k <= n
    invariant sum == k * (k - 1) / 2
    // synthesized invariants:
    invariant -1*k*k + 2*sum <= 0
    invariant -1*k*k + 2*sum - 1 <= 0
    invariant -1*k*k + 2*sum - 2 <= 0
    invariant -1*k*k + 2*sum - 5 <= 0


    decreases n - k
  {
    sum := sum + k;
    k := k + 1;
  }
}

/*
Terminal Output:

{
  "file": "week3\\quadratic_triangular.dfy",
  "methods": [
    {
      "method_name": "TriangularSum",
      "preconditions": [
        "n >= 0"
      ],
      "postconditions": [
        "sum == n * (n - 1) / 2"
      ],
      "parameters": [
        {
          "name": "n",
          "type": "int"
        }
      ],
      "returns": [
        {
          "name": "k",
          "type": "int"
        },
        {
          "name": "sum",
          "type": "int"
        }
      ],
      "loops": [
        {
          "condition": "k < n",
          "variables": [
            "k",
            "sum"
          ],
          "template_variables": [
            "k",
            "sum"
          ],
          "quadratic_invariants": [
            "-1*k*k + 2*sum <= 0",
            "-1*k*k + 2*sum - 1 <= 0",
            "-1*k*k + 2*sum - 2 <= 0",
            "-1*k*k + 2*sum - 3 <= 0",
            "-1*k*k + 2*sum - 5 <= 0"
          ],
          "template": "a*x^2 + b*y^2 + c*x*y + d*x + e*y + f <= 0"
        }
      ]
    }
  ]
}*/