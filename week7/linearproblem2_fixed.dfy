method DoubleIncrement(n: int) returns (i: int, j: int)
{
  i := 0;
  j := 0;
  while (i < n && j < 2*n)
    invariant -2*i - j <= 0
    invariant -2*i + j <= 0
    invariant -i - 2*j <= 0
    invariant -i - j <= 0
    invariant -i <= 0
  {
    i := i + 1;
    j := j + 2;
  }
}

/*

Terminal output after verification:

{
  "method_name": "DoubleIncrement",
  "loop_condition": "i < n && j < 2*n",
  "inserted_invariants": [
    "-2*i - j <= 0",
    "-2*i + j <= 0",
    "-i - 2*j <= 0",
    "-i - j <= 0",
    "-i <= 0"
  ],
  "output_path": "week7\\linearproblem2_fixed.dfy",
  "verification": {
    "ok": "true",
    "raw_output": "Warning: this way of using the CLI is deprecated. Use 'dafny --help' to see help for the new Dafny CLI format\n\nDafny program verifier finished with 1 verified, 0 errors"
  }
}

*/