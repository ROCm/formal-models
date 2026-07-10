"""Test generator for Alloy memory models

This script generates Alloy modules that test various memory consistency
models based on input test descriptions. It supports multiple memory model
flavors, each implemented as a separate test class.
"""

import argparse
from pathlib import Path
import re
import sys

from gentest.core import *
import gentest.alloy_wrapper as alloy_wrapper

root_name = "memory_consistency"


def register_models(subparsers) -> None:
    """Register available memory model test classes with the argument parser.

    Each memory model test class needs to implement a class method
    `register_arg_subparser(subparsers)` that adds a subparser for that model.
    """
    from gentest.llvm import LLVMIRTest
    from gentest.llvm_amdgpu import AMDGPULLVMIRTest

    model_test_classes: list[type[ModelTest]] = [
        LLVMIRTest,
        AMDGPULLVMIRTest,
    ]

    for tc in model_test_classes:
        tc.register_arg_subparser(subparsers)


def alloy_sanitize_module_path(path: str) -> str:
    """Sanitize a module path for Alloy.

    This removes the .als extension, replaces path separators with '/', and
    replaces '-' and '.' with '_'.
    """
    original_path = path
    # Remove .als extension
    if path.endswith(".als"):
        path = path[:-4]

    # Handle windows path separators
    path = path.replace("\\", "/")

    path = path.replace("-", "_")
    path = path.replace(".", "_")

    test_regex = re.compile(r"[\w\d_/]+")
    if not test_regex.fullmatch(path):
        raise ParseError(
            f"Couldn't transform '{original_path}' into a valid Alloy module name."
        )

    return path


def main() -> int:
    script_dir = Path(__file__).resolve().parent
    default_root = str(script_dir.parent)

    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.ArgumentDefaultsHelpFormatter
    )

    subparsers = parser.add_subparsers(
        title="Memory model flavor to generate a test for", dest="mode", required=True
    )

    register_models(subparsers)

    parser.add_argument(
        "input", type=str, help="path to the input test description file"
    )
    parser.add_argument(
        "-m",
        "--alloy-module",
        type=str,
        default=None,
        help="destination file path for the generated Alloy module, must be in a subdirectory of the root directory; required if invoked with '--no-analyze' or if the 'alloy-output-dir' is not a subdirectory of 'root'",
    )
    parser.add_argument(
        "--root",
        type=str,
        default=default_root,
        help="path to the project directory, which serves as the root of all Alloy modules",
    )
    parser.add_argument(
        "--push",
        action="append",
        dest="additional_predicates",
        metavar="PREDICATE",
        default=[],
        help="additional Alloy predicate to be pushed on the stack for checks; can be used multiple times to push multiple predicates",
    )
    parser.add_argument(
        "-q",
        "--quiet",
        action="store_true",
        help="reduce command line output",
    )
    parser.add_argument(
        "--analyze",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="run the Alloy analyzer on the generated module",
    )

    alloy_wrapper.add_cli_args(parser)

    args = parser.parse_args()

    quiet_mode = args.quiet

    root_path = Path(args.root).resolve()
    if not root_path.is_dir():
        print(
            f"error: specified root path '{root_path}' is not a directory",
            file=sys.stderr,
        )
        return 1

    input_file = Path(args.input).resolve()
    if not input_file.is_file():
        print(
            f"error: input file '{input_file}' not found",
            file=sys.stderr,
        )
        return 1

    alloy_config = None
    test_file_path = None

    if args.alloy_module is not None:
        test_file_path = Path(args.alloy_module).resolve()

    if args.analyze:
        try:
            alloy_config = alloy_wrapper.extract_args(args, root_path)
        except alloy_wrapper.AlloyError as err:
            print("error: " + str(err), file=sys.stderr)
            return 1

        if test_file_path is None:
            assert alloy_config.output_dir is not None
            temp_dir_path = alloy_config.output_dir.resolve()
            try:
                temp_dir_path.relative_to(root_path)
            except ValueError:
                print(
                    f"error: the output dir '{temp_dir_path}' must be located within the root directory '{root_path}' if no output file path for the Alloy module is provided via '--alloy-module <file.als>'",
                    file=sys.stderr,
                )
                return 1
            temp_dir_path.mkdir(parents=True, exist_ok=True)

            test_file_path = temp_dir_path / (input_file.name + ".als")

    # The generated Alloy module will contain imports relative to the root
    # directory, so it must be placed within the root directory.
    if not test_file_path:
        print(
            f"error: no output file path for the Alloy module provided; provide one within the root directory '{root_path}' via '--alloy-module <file.als>'",
            file=sys.stderr,
        )
        return 1
    try:
        rel_path = str(test_file_path.relative_to(root_path))
    except ValueError:
        print(
            f"error: the output file path '{test_file_path}' for the generated Alloy module is not located within the root directory '{root_path}'",
            file=sys.stderr,
        )
        return 1

    model_test_class = args.model_test_cls

    try:
        module_path = alloy_sanitize_module_path(rel_path)

        test = model_test_class(args)

        test.push_predicates(args.additional_predicates)

        with open(args.input) as input:
            for line in input.readlines():
                test.parse_line(line)

        alloy = test.to_alloy(root_name, module_path)
        with open(test_file_path, "w") as f:
            f.write(alloy)
    except ParseError as err:
        print("parsing error: " + str(err), file=sys.stderr)
        return 1
    except Topology.TopologyError as err:
        print("topology parsing error: " + str(err), file=sys.stderr)
        return 1
    except InvalidInstError as err:
        print("invalid instruction: " + str(err), file=sys.stderr)
        return 1
    except SemanticError as err:
        print("semantic error: " + str(err), file=sys.stderr)
        return 1

    if alloy_config is not None:
        if not quiet_mode:
            print(f"Generated Alloy module: {test_file_path}")
        try:
            success, results = alloy_wrapper.run(alloy_config, test_file_path)
            for r in results:
                if quiet_mode:
                    print(str(r))
                else:
                    print("\n" + test.format_check_result(r))
            if not success:
                return 1
        except alloy_wrapper.AlloyError as err:
            print("alloy error: " + str(err), file=sys.stderr)
            return 1

    return 0
