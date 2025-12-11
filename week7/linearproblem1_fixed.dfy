method Counter(n: int) returns (i: int)
{
  i := 0;
  while (i < n)
    invariant -i <= 0
  {
    i := i + 1;
  }
}

/*
Terminal output after verification:

{
  "method_name": "Counter",
  "loop_condition": "i < n",
  "inserted_invariants": [
    "-i <= 0"
  ],
  "output_path": "week7\\linearproblem1_fixed.dfy",
  "verification": {
    "ok": "true",
    "raw_output": "Warning: this way of using the CLI is deprecated. Use 'dafny --help' to see help for the new Dafny CLI format\n\nDafny program verifier finished with 1 verified, 0 errors"
  }
  */