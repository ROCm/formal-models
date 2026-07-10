#!/usr/bin/env python3
import argparse
import subprocess
import sys
from datetime import datetime
from pathlib import Path
import shutil


def main():
    scriptdir = Path(__file__).resolve().parent
    default_benchdir = scriptdir / "runs"
    default_testsuite = "llvm/test"

    p = argparse.ArgumentParser(
        description="Run benchmark suite and write results to a CSV file.",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    p.add_argument(
        "-n",
        "--reps",
        type=int,
        default=3,
        help="number of repetitions per test case",
    )
    p.add_argument(
        "-d",
        "--benchdir",
        default=str(default_benchdir),
        help="directory to store benchmark results",
    )
    p.add_argument(
        "-t", "--testsuite", default=default_testsuite, help="testsuite to benchmark"
    )
    p.add_argument(
        "-i",
        "--id",
        dest="runid",
        default="bench",
        help="run identifier, used in naming the benchmark file",
    )
    p.add_argument(
        "-s",
        "--solver",
        default="default",
        help="SAT solver to use in the Alloy analyzer, or 'default' to use the default solver",
    )
    args = p.parse_args()

    # Validate reps
    if args.reps <= 0:
        print("Error: reps must be a positive integer", file=sys.stderr)
        sys.exit(1)

    # Check if llvm-lit is available
    if not shutil.which("llvm-lit"):
        print("Error: llvm-lit not found in PATH", file=sys.stderr)
        sys.exit(1)

    reps = args.reps
    testsuite = args.testsuite
    runid = args.runid
    solver = args.solver
    benchdir = Path(args.benchdir)

    testsuite_path = Path(testsuite).resolve()
    if not testsuite_path.exists():
        print(
            f"Error: testsuite path does not exist: {testsuite_path}", file=sys.stderr
        )
        sys.exit(1)

    solvers = []

    if solver == "all":
        # TODO query from alloy binary instead of hardcoding
        solvers = [
            "sat4j",
            "glucose",
            "minisat",
            "minisat.prover",
            "sat4j.light",
            "sat4j.pmax",
            # "lingeling.parallel",
        ]
    else:
        solvers.append(solver)

    failed_runs = 0
    result_files = []
    for x, s in enumerate(solvers):
        benchid = f"{runid}_{s}_{datetime.now().strftime('%Y%m%dT%H%M%S')}"

        benchdir.mkdir(parents=True, exist_ok=True)

        benchdir = benchdir.resolve()
        benchfile = benchdir / f"run_{benchid}.csv"

        print(f"Benchmark configuration {x+1}/{len(solvers)}:")
        print(f"  Testsuite: {testsuite}")
        print(f"  Solver: {s}")
        print(f"  Repetitions: {reps}")
        print(f"  Results file: {benchfile}")
        print(f"\nStarting benchmark run...")

        # It's necessary to run the benchmarks sequentially with -j1 since all of
        # them append their result to the same csv file. There are obviously ways to
        # work around this, but running them sequentially makes sense anyway to get
        # more reliable performance numbers.
        cmd = [
            "llvm-lit",
            "-j1",
            "-v",
            "--param",
            f"benchmark={benchfile}",
            "--param",
            f"benchreps={reps}",
        ]
        if s != "default":
            cmd.extend(["--param", f"solver={s}"])
        cmd.append(testsuite)

        try:
            subprocess.run(cmd, cwd=scriptdir.parent, check=True)
            print(f"\nBenchmark completed successfully.")
        except subprocess.CalledProcessError as e:
            print(f"llvm-lit failed with exit code {e.returncode}", file=sys.stderr)
            failed_runs += 1
        print(f"Results saved to: {benchfile}")
        result_files.append(benchfile)

    print("\nAll result files:")
    for f in result_files:
        print(f"  {f}")

    if failed_runs > 0:
        print(f"\n{failed_runs} benchmark runs failed.", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
