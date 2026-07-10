# Alloy Memory Consistency Models

This repository contains experimental [Alloy](https://alloytools.org/) formalizations of memory consistency models and execution models.
This is an experimental academic project, the formal models are **not** official or authoritative LLVM- or AMD-approved specifications.
They are merely informational interpretations of how programs may execute on AMDGPU hardware.

Currently included models:
- `llvm`: A memory model for [LLVM](https://github.com/llvm/llvm-project) IR, in variants with and without AMDGPU-specific extensions.
  See [its README](./llvm/README.md) for more information.


## Setup and Requirements

Create a `build` subdirectory in the root of the repo, download the [Alloy analyzer jar](https://github.com/AlloyTools/org.alloytools.alloy/releases/) `org.alloytools.alloy.dist.jar`, and place it under this name in the `build` directory.
The `./setup.sh` script automates these steps.

The models here have been tested with Alloy release 6.2.0.

Additional requirements:
- Java, for running the Alloy analyzer
- Python 3, for using the domain-specific language for litmus test. The usage instructions below assume that `python` points to a Python 3 installation.
- [llvm-lit](https://llvm.org/docs/CommandGuide/lit.html) (optional, part of LLVM), for running the provided test suite, not required for analyzing individual tests
- GNU Make (optional), for convenience `make` commands

## How to Use

There are two ways to interact with the Alloy models:
By analyzing a concrete test case in a domain-specific language or by directly running Alloy commands that are independent of concrete tests.
The following subsections describe each of these ways.

### Analyzing a Concrete Test Case

This project provides a domain-specific language to specify concrete test cases for analysis under Alloy models.
A test case specifies static aspects of multi-threaded program executions (which operations are executed, how they are arranged in threads, how the threads are arranged in the scopes) and checks if executions exist that satisfy these static aspects and additional properties.
The included [gentest](./gentest) python package converts a test case in this domain-specific language into an Alloy module that encodes the static aspects and contains commands for the Alloy analyzer that correspond to the checks in the test case.
The test syntax is described in [docs/tests.md](./docs/tests.md).

For an annotated example test case for the LLVM IR memory model, consider [llvm/test/example.test](./llvm/test/example.test).
This test can be analyzed with this command from the root directory of the repo:

```
python -m gentest llvm ./llvm/test/example.test
```

This command prints where the generated Alloy module can be found[^1] and that the Alloy analyzer has validated all the checks.

The gentest package provides model-independent and model-specific command line parameters to change its behavior.
Use `--help` without a specified model to find out which models are supported (like `llvm` in the above command) and which model-independent parameters exist:

```
python -m gentest --help
```

Use `<model> --help` to find out about model-specific command line parameters:

```
python -m gentest <model> --help
```

Invoke the package as follows:

```
python -m gentest [model-independent parameters] <model> [model-specific parameters] ./path/to/testcase.test
```

### Running Independent Alloy Commands

For reasoning about properties of the models that don't involve a concrete test program, you can use Alloy modules that interact with the model directly (see the [Alloy language specification](https://alloytools.org/spec.html) and the [Practical Alloy](https://practicalalloy.github.io/) online book for details on the language).

For an annotated example for the LLVM IR memory model, consider [llvm/test/general-properties/example.als](./llvm/test/general-properties/example.als).[^1]
It challenges the Alloy analyzer to show that
- there are executions in the LLVM memory model with up to 4 Events (i.e., load, store, rmw, or fence operations) and *2 threads* where a read participates in a data race and that
- there are no executions in the LLVM memory model with at most 4 Events in a *single thread* where a read participates in a data race.

You can analyze such an Alloy module directly with the Alloy analyzer CLI or GUI (see next section) or with the Alloy wrapper provided in the `gentest` package via the `gentest.check_alloy` entry point:

```
python -m gentest.check_alloy llvm/test/general-properties/example.als
```

This entry point runs the Alloy analyzer CLI, checks the results, and prints a summary.
Use the following command to explore available command line parameters:
```
python -m gentest.check_alloy --help
```

### Checking Instances via GUI

To view Alloy instances using the Alloy GUI (which offers a tree and graph view, as well as an expression evaluator), run the following:

`java -jar build/org.alloytools.alloy.dist.jar`

The Alloy GUI will open.
You can then choose to open a `.als` file[^1] (either written manually or generated via `gentest` as described in the previous section).
Click the "Execute" button in the top bar to run the Alloy analyzer.
If an instance is found, a window with a visualization of the instance opens.
You can use "Theme -> Load Theme..." in the top menu bar of the visualization window to load the `.thm` file provided in the model directory (e.g., [llvm.thm](./llvm/llvm.thm)) to apply the recommended display settings for the model.

[^1]: Note that the location of the `.als` files relative to the root of the repository matters: The Alloy modules contain relative imports that can break if files are moved.

### Running the Test Suites

Running the test suites requires LLVM's [llvm-lit tool](https://llvm.org/docs/CommandGuide/lit.html).
Simply run `llvm-lit <model>/test` (or `make check-<model>`).
The `llvm-lit` tool will invoke the `gentest` python module to translate the tests into Alloy files and check them with the Alloy analyzer.
The Alloy files generated by `gentest` will be contained in `build/test`.

All the tests (including python tests for the `gentest` package) can be run at once via `make check`.

## Development

You can install the development dependencies by running this command:
```
make install-dev
```

Python code in this project is formatted using [black](https://github.com/psf/black) (installed with the development dependencies).
To format the code, run:
```
make format
```

To run the [mypy](https://mypy-lang.org/) static type checker, run:
```
make mypy
```

The gentest test generation script has its own unit tests.
Run them with:
```
make check-gentest
```

### Advanced: Benchmarking

You can benchmark the running time of the Alloy analyzer on (a subset of) a test suite as follows:
```
python benchmarks/perform_benchmark.py [--reps <N>] --testsuite <model>/test[/subdirs] --id <benchmark_id> [--solver <solver_name>] [--benchdir <bench_dir>]
```
This will create a timestamped csv file in `<benchdir>` (default: `benchmarks/runs`) with the results of the benchmark run.
The benchmark id will be included in the csv file name to identify different runs.
The benchmarks are run sequentially, and each test is repeated `N` times (default: 3) to account for variable running times.

You can then compare different benchmark runs with:
```
python benchmarks/compare_runs.py --baseline <path_to_baseline_csv> <path_to_contender_csv> [--epsilon <relative_epsilon>]
```

---

Licensed under Apache 2.0 with LLVM Exceptions — see [LICENSE.txt](./LICENSE.txt)
