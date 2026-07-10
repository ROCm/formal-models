"""Alloy checker entry point.

Runs the Alloy CLI on a given Alloy model file, collects the solutions, and
checks if the number of solutions matches the expected number.
"""

import argparse
from pathlib import Path
import sys

import gentest.alloy_wrapper as alloy_wrapper


def main() -> bool:
    script_dir = Path(__file__).resolve().parent
    root_path = script_dir.parent

    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.ArgumentDefaultsHelpFormatter
    )

    parser.add_argument(
        "input", type=str, metavar="<file>", help="input Alloy model file"
    )

    alloy_wrapper.add_cli_args(parser, root_path)

    args = parser.parse_args()

    input_file = Path(args.input).resolve()
    if not input_file.is_file():
        raise alloy_wrapper.AlloyError(f"input file '{input_file}' not found")

    alloy_config = alloy_wrapper.extract_args(args)

    success, results = alloy_wrapper.run(alloy_config, input_file)
    for r in results:
        print(str(r))
    return success


if __name__ == "__main__":
    try:
        if main():
            sys.exit(0)
    except alloy_wrapper.AlloyError as e:
        print(f"error: {e}", file=sys.stderr)
    sys.exit(1)
