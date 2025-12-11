method ForcedGoodExample(n: int) returns (a: int, b: int, flag: int)
{
    var i := 0;
    a := 0;
    b := 10;
    flag := 0;

    while i < n
    
      invariant (-a <= 0 && -flag <= 0){
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

/*
Terminal output:
{
  "file": "week3\\benchmark_boolean.dfy",
  "used_boolean": true,
  "invariants": [
    "(-a <= 0 && -flag <= 0)"
  ],
  "out_file": "benchmark_boolean.dfy",
  "ran_dafny": true,
  "dafny": {
    "command": [
      "dafny",
      "benchmark_boolean.dfy"
    ],
    "returncode": 0,
    "output": "Warning: this way of using the CLI is deprecated. Use 'dafny --help' to see help for the new Dafny CLI format\n\nDafny program verifier finished with 1 verified, 0 errors\nCompiled assembly into w10_output.dll\n"
  }
}
 */