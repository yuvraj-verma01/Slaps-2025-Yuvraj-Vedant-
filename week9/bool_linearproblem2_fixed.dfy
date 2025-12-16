method DoubleIncrement(n: int) returns (i: int, j: int)
{
  i := 0;
  j := 0;
  while (i < n && j < 2*n)
  
    invariant (-i <= 0 && -j <= 0){
    i := i + 1;
    j := j + 2;
  }
}

/* 

Terminal Output:
{
  "file": "week3\\linearproblem2.dfy",
  "used_boolean": true,
  "invariants": [
    "(-i <= 0 && -j <= 0 && -i - j <= 0)"
  ],
  "out_file": "week9\\linearproblem2_fixed.dfy",
  "ran_dafny": true,
  "dafny": {
    "command": [
      "dafny",
      "week9\\linearproblem2_fixed.dfy"
    ],
    "returncode": 0,
    "output": "Warning: this way of using the CLI is deprecated. Use 'dafny --help' to see help for the new Dafny CLI format\n\nDafny program verifier finished with 1 verified, 0 errors\nCompiled assembly into linearproblem2_fixed.dll\n"
  }
} */