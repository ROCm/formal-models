"""Wrappers around the Alloy analyzer jar."""

import argparse
import csv
from dataclasses import dataclass
import json
from pathlib import Path
import re
import subprocess
import textwrap
import time
from typing import *


class AlloyError(Exception):
    pass


default_alloy_path = "<root>/build/org.alloytools.alloy.dist.jar"
default_output_dir = "<root>/build/temp/"


@dataclass
class AlloyConfig:
    solver: str = "sat4j"
    java_cmd: str = "java"
    alloy_path: Optional[Path] = None
    output_dir: Optional[Path] = None
    expected_solutions: int = 1
    more_solutions_allowed: bool = True
    raw_output_type: str = "none"
    timeout_secs: int = -1
    quiet: bool = True  # currently not exposed via CLI

    enable_benchmarks: bool = False
    benchmark_file: Optional[Path] = None
    benchmark_repetitions: int = 3


def _make_path(path: str, root: Optional[Path]) -> Path:
    placeholder = "<root>/"
    if root is None:
        return Path(path).resolve()
    if path.startswith(placeholder):
        path = path[len(placeholder) :]
        return (root / path).resolve()
    return Path(path).resolve()


def add_cli_args(parser: argparse.ArgumentParser, root: Optional[Path] = None) -> None:
    """Add command line arguments to configure how the Alloy analyzer is run to
    the provided argparser.

    The `root` argument needs to be provided either here (if the root directory
    is not determined by other command line flags) or, otherwise, in
    `extract_args`.
    """
    default_config = AlloyConfig()
    group = parser.add_argument_group("Alloy analyzer configuration")
    group.add_argument(
        "--solver",
        metavar="<solver>",
        type=str,
        default=default_config.solver,
        help="SAT solver that the Alloy analyzer should use",
    )

    default_alloy_path_shown = default_alloy_path
    default_output_dir_shown = default_output_dir
    if root is not None:
        default_alloy_path_shown = str(_make_path(default_alloy_path, root))
        default_output_dir_shown = str(_make_path(default_output_dir, root))
    group.add_argument(
        "--alloy-path",
        metavar="<alloy.jar>",
        type=str,
        default=default_alloy_path_shown,
        help="path of the jar distribution file of the Alloy analyzer",
    )
    group.add_argument(
        "--java-cmd",
        metavar="<java>",
        type=str,
        default=default_config.java_cmd,
        help="path to the Java executable to use for running the Alloy analyzer",
    )
    group.add_argument(
        "-t",
        "--alloy-output-dir",
        metavar="<dir>",
        type=str,
        default=default_output_dir_shown,
        help="directory where the Alloy analyzer's outputs are stored; concurrent invocations must provide different output directories",
    )
    default_expect_val = "{}{}".format(
        default_config.expected_solutions,
        "+" if default_config.more_solutions_allowed else "",
    )
    group.add_argument(
        "--expect",
        metavar="<N>[+]",
        default=default_expect_val,
        type=str,
        help="number of solutions expected for satisfiability checks. If there is a + at the end, allow more solutions than the requested amount",
    )
    group.add_argument(
        "--alloy-output-type",
        metavar="<type>",
        default=default_config.raw_output_type,
        type=str,
        choices=["none", "text", "table", "json", "xml"],
        help="how the Alloy CLI outputs each instance produced to the alloy-output-dir",
    )
    group.add_argument(
        "--timeout",
        default=default_config.timeout_secs,
        type=int,
        help="timeout in seconds for individual calls to the Alloy analyzer. Use -1 for no timeout.",
    )
    group.add_argument(
        "--benchmark",
        metavar="<output file>",
        type=str,
        default=None,
        help="if provided, the Alloy analyzer is run <benchreps> times, the duration of each call is recorded, and the results are written as lines in csv format to the provided file",
    )
    group.add_argument(
        "--benchreps",
        metavar="<n>",
        type=int,
        default=default_config.benchmark_repetitions,
        help="number of Alloy analyzer runs for benchmarking, only effective if --benchmark is provided",
    )


def extract_args(args, root: Optional[Path] = None) -> AlloyConfig:
    """Extract an AlloyConfig from the arguments parsed from an argparser.
    The argparser must have had `add_cli_args()` called before it was invoked.

    The `root` argument needs to be provided either here (if the root directory
    is determined by other command line flags) or, otherwise, in `add_cli_args`.
    """

    config = AlloyConfig()
    config.solver = args.solver

    alloy_path = _make_path(args.alloy_path, root)
    if not alloy_path.is_file():
        raise AlloyError(f"no alloy jar file found at {alloy_path}")
    config.alloy_path = alloy_path

    config.java_cmd = args.java_cmd

    output_dir = _make_path(args.alloy_output_dir, root)
    if output_dir.is_file():
        raise AlloyError(f"provided output directory {output_dir} is a file")
    config.output_dir = output_dir

    expect_str = args.expect
    allow_extra = False
    try:
        if expect_str.endswith("+"):
            allow_extra = True
            expect_n = int(expect_str[:-1])
        else:
            expect_n = int(expect_str)
    except ValueError:
        raise AlloyError(
            "value for --expect is not a positive integer with optional trailing '+'"
        )
    if expect_n < 1:
        raise AlloyError(
            "value for --expect is not a positive integer with optional trailing '+'"
        )
    config.expected_solutions = expect_n
    config.more_solutions_allowed = allow_extra

    config.raw_output_type = args.alloy_output_type

    config.timeout_secs = args.timeout

    if args.benchmark is not None:
        config.enable_benchmarks = True
        config.benchmark_file = Path(args.benchmark)

    config.benchmark_repetitions = args.benchreps
    if config.benchmark_repetitions < 1:
        raise AlloyError("at least 1 benchmark repetition is required")

    return config


@dataclass
class CheckResult:
    success: bool
    label: str
    msg: str

    @property
    def success_str(self) -> str:
        return "SUCCESS" if self.success else "FAILURE"

    def __str__(self) -> str:
        return f"{self.success_str}: {self.label}: {self.msg}"


def _run_single(
    config: AlloyConfig, filepath: Path, output_suffix: str = ""
) -> tuple[bool, list[CheckResult], float]:
    """Run the Alloy analyzer with the given config on the Alloy module at the
    provided filepath.
    """
    if not filepath.is_file():
        raise AlloyError(f"input file '{filepath}' does not exist")

    solutions_to_find = config.expected_solutions

    if not config.more_solutions_allowed:
        # Try to find an additional solution and report an error if it is found.
        solutions_to_find += 1

    assert config.alloy_path is not None
    assert config.output_dir is not None

    output_dir = config.output_dir / ("alloy_output" + output_suffix)

    command: list[str | Path] = [config.java_cmd, "-jar", config.alloy_path, "exec"]

    # -f: deletes the output directory if it contains any files.
    command += ["-f"]

    command += ["-o", output_dir]

    # -s: solver to use
    command += ["-s", config.solver]

    # -t: type of file to create for each instance
    command += ["-t", config.raw_output_type]

    # -r: repeat/find N solutions
    command += ["-r", str(solutions_to_find)]

    # -q: quiet mode
    if config.quiet:
        command.append("-q")

    command.append(filepath)

    start_time = time.monotonic()

    timeout_val = None
    if config.timeout_secs >= 0:
        timeout_val = config.timeout_secs
    try:
        ret = subprocess.run(
            command, timeout=timeout_val, capture_output=True, encoding="utf-8"
        )
    except subprocess.TimeoutExpired:
        print(
            f"TIMEOUT: Alloy analyzer call took longer than {timeout_val} seconds. Increase this timeout with `--timeout <N>` or use `--timeout -1` to run without a timeout."
        )
        duration_secs = time.monotonic() - start_time
        return False, [], duration_secs

    if ret.returncode != 0 and not is_unexpected_result_error(ret):
        msg = f"Alloy CLI failed (return code {ret.returncode})"
        has_stdout = False
        if len(ret.stdout) > 0:
            msg += "\n  stdout:\n" + textwrap.indent(ret.stdout, "    ")
            has_stdout = True
        if len(ret.stderr) > 0:
            if has_stdout:
                msg += "\n  stderr:\n" + textwrap.indent(ret.stderr, "    ")
            else:
                msg += "\n" + ret.stderr
        raise AlloyError(msg)

    duration_secs = time.monotonic() - start_time

    try:
        with open(output_dir / "receipt.json", "r") as file:
            receipt = json.loads(file.read())
    except FileNotFoundError as e:
        raise AlloyError(
            f"no receipt.json from the Alloy analyzer found in {output_dir}"
        )

    success = True
    results = []
    for cmd in receipt["commands"].values():
        cmd_type = cmd["type"]
        label = cmd["name"]

        if cmd_type == "run":
            num_solutions = len(cmd["solution"]) if "solution" in cmd else 0
            expects_sat = (int(cmd["expects"]) == 1) if "expects" in cmd else False
            num_expected_solutions = config.expected_solutions if expects_sat else 0
            if config.more_solutions_allowed and expects_sat:
                if num_solutions >= num_expected_solutions:
                    result = CheckResult(
                        True,
                        label,
                        f"at least {num_solutions} solution(s) found, as expected",
                    )
                else:
                    result = CheckResult(
                        False,
                        label,
                        f"{num_solutions} solution(s) found, expected at least {num_expected_solutions}",
                    )
                    success = False
            else:
                if num_solutions == num_expected_solutions:
                    result = CheckResult(
                        True,
                        label,
                        f"exactly {num_solutions} solution(s) found, as expected",
                    )
                else:
                    result = CheckResult(
                        False,
                        label,
                        f"{num_solutions} solution(s) found, expected exactly {num_expected_solutions}",
                    )
                    success = False
        elif cmd_type == "check":  # assertions
            expect_n = int(cmd["expects"])
            assert expect_n == -1  # all that we need right now
            if "solution" in cmd:
                result = CheckResult(
                    False, label, f"assertion has at least one counterexample"
                )
                success = False
            else:
                result = CheckResult(True, label, f"no counterexamples for assertion")
        results.append(result)

    return success, results, duration_secs


def is_unexpected_result_error(ret) -> bool:
    """Check if the result of the Alloy analyzer has reported an error because
    check lines were not (un)satisfiable as expected.

    The purpose of this function is to determine when an Alloy error indicates
    that the input was broken vs when a run/check line just didn't execute as
    expected. In the latter case, we can produce more helpful output.
    """
    if ret.returncode == 0:
        return False

    # At the end of the Alloy analyzer's diagnostic is usually a section
    # starting with "Error" or "Errors" followed by numbered lines enumerating
    # the encountered errors.
    # If that's the case, we can check if all listed errors are just unexpected
    # satisfiability results.
    stderr_lines = ret.stderr.split("\n")
    error_lines = None
    for idx in range(len(stderr_lines) - 1, -1, -1):
        if stderr_lines[idx].strip() == "Error" or stderr_lines[idx] == "Errors":
            error_lines = stderr_lines[idx + 1 :]

    if not error_lines:
        return False
    pat = re.compile(r"\d+\. '.*' was (not )?satisfied against expectation")
    for l in error_lines:
        l = l.strip()
        if len(l) == 0:
            continue
        if not pat.fullmatch(l):
            return False
    return True


def run(config: AlloyConfig, filepath: Path) -> tuple[bool, list[CheckResult]]:
    """Run the Alloy analyzer with the given config on the Alloy module at the
    provided filepath.
    """
    assert config.output_dir is not None
    config.output_dir.mkdir(parents=True, exist_ok=True)

    success = True
    results: list[CheckResult] = []

    if config.enable_benchmarks:
        assert config.benchmark_file is not None
        with open(config.benchmark_file, "a") as bf:
            fieldnames = [
                "alloy_file",
                "solver",
                "success",
                "duration_secs",
                "repetition",
            ]
            writer = csv.DictWriter(bf, fieldnames=fieldnames)
            if bf.tell() == 0:
                writer.writeheader()
            for i in range(1, config.benchmark_repetitions + 1):
                output_suffix = f"_rep{i}"
                run_success, results, duration_secs = _run_single(
                    config, filepath, output_suffix=output_suffix
                )
                bench_result = {
                    "alloy_file": filepath,
                    "solver": config.solver,
                    "success": run_success,
                    "duration_secs": duration_secs,
                    "repetition": i,
                }
                writer.writerow(bench_result)
                success = success and run_success
    else:
        success, results, duration_secs = _run_single(
            config, filepath, output_suffix=""
        )

    # In the benchmarking case, this returns only the last results produced.
    # If no timeouts occur, the results of individual benchmark runs should
    # always be the same.
    return success, results
