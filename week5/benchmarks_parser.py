import json
from pathlib import Path

from parser import run_parser 


def main() -> None:
    repo_root = Path(__file__).resolve().parents[1]
    bench_dir = repo_root / "week3"

    if not bench_dir.exists():
        print(f"[ERROR] Benchmark directory not found: {bench_dir}")
        return

    dfy_files = sorted(bench_dir.glob("*.dfy"))
    if not dfy_files:
        print(f"[WARN] No .dfy files found in {bench_dir}")
        return

    print(f"Found {len(dfy_files)} benchmark(s) in {bench_dir}\n")

    for f in dfy_files:
        print("=" * 80)
        print(f"Benchmark: {f.relative_to(repo_root)}")

        summary = run_parser(str(f))

        methods = summary.get("methods", [])
        print(f"  #methods: {len(methods)}")
        for m in methods:
            print(
                f"    - {m['method_name']}: "
                f"{len(m['parameters'])} params, "
                f"{len(m['loops'])} loops, "
                f"{len(m['preconditions'])} requires, "
                f"{len(m['postconditions'])} ensures"
            )

        print("\n  Full summary JSON:")
        print(json.dumps(summary, indent=2))
        print()

    print("=" * 80)
    print("Done.")


if __name__ == "__main__":
    main()
