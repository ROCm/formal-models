"""LLVM IR memory model with AMDGPU extensions and specializations.

This module implements a ModelTest subclass for handling tests specific to
the LLVM IR memory model with AMDGPU extensions and specializations.
"""

from typing import *

from gentest.core import *
from gentest.llvm import *


class AMDGPULLVMIRTest(LLVMIRTest):
    """LLVM IR memory model with AMDGPU extensions and specializations."""

    def __init__(self, parsed_args=None) -> None:
        super().__init__(parsed_args=parsed_args)

    @classmethod
    def register_arg_subparser(cls, subparsers):
        amdgpu_parser = subparsers.add_parser(
            "llvm-amdgpu",
            help="LLVM IR memory model with AMDGPU extensions and specializations.",
        )
        amdgpu_parser.add_argument(
            "--scope-encoding",
            type=lambda s: ScopeEncoding(s),
            choices=list(ScopeEncoding),
            default=ScopeEncoding.FULL,
            help='Strategy for encoding scope hierarchy: "full" (complete hierarchy), '
            '"optimized" (omit scopes that are not needed).',
        )
        amdgpu_parser.set_defaults(model_test_cls=AMDGPULLVMIRTest)

    def get_scope_hierarchy(self) -> list[str]:
        return ["system", "agent", "cluster", "workgroup", "wave", "thread"]

    def get_syncscope_mapping(self) -> dict[str, str]:
        return {
            "system": "system",
            "agent": "agent",
            "ag": "agent",
            "cluster": "cluster",
            "cl": "cluster",
            "workgroup": "workgroup",
            "wg": "workgroup",
            "wavefront": "wave",
            "wave": "wave",
            "wf": "wave",
            "singlethread": "thread",
            "thread": "thread",
            "st": "thread",
        }
