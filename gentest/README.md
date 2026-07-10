# Tooling for Testing the Alloy Models: gentest

This directory implements the `gentest` python package.
It implements a domain-specific language for analyzing the behavior of concrete programs with the memory models.
See the [general README](../README.md) for usage instructions and the [test guide](../docs/tests.md) for more details on the domain-specific language.

There are two different entry points for this package:
- `python -m gentest` takes an input in the domain-specific language, translates it into an Alloy module, (optionally) runs the Alloy analyzer CLI on it, and presents the results.
- `python -m gentest.check_alloy` takes an Alloy module as its input, runs the Alloy analyzer CLI on it, and presents the results.

`gentest` supports different test flavors for the different Alloy models.
For instance, there is an `llvm` flavor for tests of the LLVM IR memory model that models LLVM IR instructions and a derived `llvm-amdgpu` flavor that additionally covers AMDGPU-specific extensions to the memory model.
Each flavor is implemented as a subclass of `ModelTest` (defined in [core.py](./core.py), together with general model-independent helpers), for example the `LLVMIRTest` subclass in [llvm.py](./llvm.py) and the `AMDGPULLVMIRTest` subclass in [llvm_amdgpu.py](./llvm_amdgpu.py).

The `test*.py` modules contain pytest unit tests for individual components of `gentest`.
The code is formatted with `black`.
