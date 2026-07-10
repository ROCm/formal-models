"""LLVM IR memory model.

This module implements a ModelTest subclass for handling tests specific to
the LLVM IR memory model.
"""

from enum import Enum
from typing import *

from gentest.core import *


class ScopeEncoding(Enum):
    """Strategy for encoding the scope hierarchy in Alloy."""

    FULL = "full"
    OPTIMIZED = "optimized"

    def __str__(self) -> str:
        return self.value


class LLVMIRTest(ModelTest):
    """LLVM IR memory model."""

    def __init__(self, parsed_args=None) -> None:
        super().__init__()
        self.scope_encoding = ScopeEncoding.FULL
        if parsed_args is not None:
            self.scope_encoding = parsed_args.scope_encoding

    @classmethod
    def register_arg_subparser(cls, subparsers) -> None:
        llvm_parser = subparsers.add_parser(
            "llvm",
            help="LLVM IR memory model.",
        )
        llvm_parser.add_argument(
            "--scope-encoding",
            type=lambda s: ScopeEncoding(s),
            choices=list(ScopeEncoding),
            default=ScopeEncoding.FULL,
            help='Strategy for encoding scope hierarchy: "full" (complete hierarchy), '
            '"optimized" (omit scopes that are not needed).',
        )
        llvm_parser.set_defaults(model_test_cls=LLVMIRTest)

    def get_scope_hierarchy(self) -> list[str]:
        return ["system", "thread"]

    def get_syncscope_mapping(self) -> dict[str, str]:
        return {
            "system": "system",
            "singlethread": "thread",
            "thread": "thread",
            "st": "thread",
        }

    legal_opcodes = {
        "load",
        "store",
        "rmw",
        "fence",
    }

    legal_ordering_constraints = {
        "unordered",
        "monotonic",
        "acquire",
        "release",
        "acq_rel",
        "seq_cst",
    }

    def parse_instruction(
        self, line: str, var: Optional[str], scope: Topology.ScopeInstance
    ) -> Instruction:
        tokens = line.split()
        if len(tokens) == 0:
            raise self._parse_error("empty instruction")

        args = tokens[1:]
        opcode_modifier_seq = tokens[0].split(".")
        opcode = opcode_modifier_seq[0]
        modifiers = opcode_modifier_seq[1:]

        if opcode not in self.legal_opcodes:
            raise self._parse_error(f'unknown opcode "{opcode}"')

        syncscope_mapping = self.get_syncscope_mapping()

        ordering = None
        syncscope = None
        for mod in modifiers:
            if mod in self.legal_ordering_constraints:
                if ordering is not None:
                    raise self._parse_error(f"more than one ordering constraint")
                ordering = mod
            elif mod.startswith("ss="):
                if syncscope is not None:
                    raise self._parse_error(f"more than one syncscope")
                mod = mod[3:]
                if mat := syncscope_mapping.get(mod):
                    syncscope = mat
                else:
                    raise self._parse_error(f'unknown syncscope "{mod}"')
            else:
                raise self._parse_error(f'unknown modifier "{mod}"')

        addr = None
        if opcode == "fence":
            if len(args) > 0:
                raise self._parse_error(f"unexpected arguments for fence")
        else:
            if len(args) == 0:
                raise self._parse_error(f"missing address argument")
            if len(args) > 1:
                raise self._parse_error(f"superfluous arguments")
            addr = args[0]

        if ordering is None and syncscope is not None:
            raise self._parse_error(f"non-atomic operation with a syncscope")

        if syncscope is None and ordering is not None:
            syncscope = "system"  # default syncscope

        alloy_id = self._create_instruction_id(var, opcode)
        parsed_inst = Instruction(alloy_id, opcode, scope, addr, var, line)
        if ordering is not None:
            parsed_inst.additional_data["ordering"] = ordering
        if syncscope is not None:
            parsed_inst.additional_data["syncscope"] = syncscope

        return parsed_inst

    def to_alloy(self, root_name: str, module_path: str) -> str:
        self._verify()
        b = AlloyBuilder()

        b.add(f"module {root_name}/{module_path}")
        b.add(f"open {root_name}/llvm/all_predicates")
        b.add()

        self._encode_program(b)

        b.add()

        self._encode_all_checks(b)

        return str(b)

    def _encode_program(self, b: AlloyBuilder) -> None:
        opcode_to_sig = {
            "load": "SimpleRead",
            "store": "SimpleWrite",
            "rmw": "RMW",
            "fence": "Fence",
        }
        po = list()
        for tid, insts in self.program_order.items():
            b.add(f"// Events for thread {tid}:")
            predecessor = None
            for inst in insts:
                sig = opcode_to_sig.get(inst.opcode)
                assert sig is not None, f"unknown opcode {inst.opcode}"
                b.add(f"one sig {inst.alloy_id} extends {sig} {{}}")
                if predecessor is not None:
                    po.append(f"({predecessor.alloy_id} -> {inst.alloy_id})")
                predecessor = inst
            b.add()

        all_addrs = {
            e.addr: f"Init_{e.addr}" for e in self.all_insts if e.addr is not None
        }

        b.add(f"// Init Writes:")
        for addr, init_id in all_addrs.items():
            b.add(f"one sig {init_id} extends Init {{}}")
        b.add()

        with b.block("fact"):
            b.add(
                "Event = {}".format(
                    " + ".join(
                        list(map(lambda x: x.alloy_id, self.all_insts))
                        + list(all_addrs.values())
                    )
                )
            )
            b.add()

            b.add(f"// program order:")
            if len(po) == 0:
                b.add("no po_imm")
            else:
                b.add("po_imm = {}".format(" + ".join(po)))
            b.add()

            b.add(f"// Event properties:")
            for e in self.all_insts:
                match e.additional_data.get("ordering"):
                    case None:
                        b.add(f"{e.alloy_id} not in Atomic")
                    case "unordered":
                        b.add(f"{e.alloy_id} in Atomic")
                        b.add(f"{e.alloy_id} not in Monotonic")
                    case "monotonic":
                        b.add(f"{e.alloy_id} in Monotonic")
                        b.add(f"{e.alloy_id} not in Acquire + Release")
                    case "release":
                        b.add(f"{e.alloy_id} in Release")
                        b.add(f"{e.alloy_id} not in Acquire")
                    case "acquire":
                        b.add(f"{e.alloy_id} in Acquire")
                        b.add(f"{e.alloy_id} not in Release")
                    case "acq_rel":
                        b.add(f"{e.alloy_id} in Acquire & Release")
                        b.add(f"{e.alloy_id} not in SeqCst")
                    case "seq_cst":
                        b.add(f"{e.alloy_id} in SeqCst")
            b.add()

            b.add(f"// Aliasing addresses:")
            for e in self.all_insts:
                if e.addr is not None:
                    init_id = all_addrs[e.addr]
                    b.add(f"({init_id} -> {e.alloy_id}) in same_location")

        b.add()
        self._encode_scope_hierarchy(b)

    def _get_scope_instance_sig(self, scope_instance: Topology.ScopeInstance) -> str:
        if scope_instance.level == "system":
            return "System"
        id_str = scope_instance.id
        return "_scope_{}_{}".format(scope_instance.level, id_str)

    def _encode_scope_hierarchy(self, b: AlloyBuilder) -> None:
        scope_encoding = self.scope_encoding
        b.add("// syncscope constraints:")
        with b.block("fact"):
            referenced_scope_instances = set()
            for e in self.all_insts:
                syncscope = e.additional_data.get("syncscope")
                if e.additional_data.get("ordering") is None:
                    continue
                assert syncscope is not None
                syncscope_instance = e.execscope_instance.get_ancestor_at(syncscope)
                b.add(
                    f"{e.alloy_id}.syncscope_instance = {self._get_scope_instance_sig(syncscope_instance)}"
                )
                referenced_scope_instances.add(syncscope_instance)

        representative_scope_instance = {
            self.topology.root_scope_instance: self.topology.root_scope_instance
        }
        b.add("// Scope hierarchy:")
        for level in self.get_scope_hierarchy():
            if level == "system":
                continue
            scope_instances = self.topology.get_scope_instances(level)
            sig = "ScopeInstance"
            for scope_instance in scope_instances:
                # If the scope instance only has at most one child scope
                # instance, we can skip it and directly connect its child to the
                # next relevant parent scope instance, to reduce the number of
                # scope instances we need to represent explicitly. That means
                # that thread scope instances are omitted unless they are
                # explicitly referenced via syncscope.
                skip_scope_instance = (
                    scope_encoding == ScopeEncoding.OPTIMIZED
                    and len(scope_instance.children) <= 1
                    and scope_instance not in referenced_scope_instances
                )
                assert scope_instance.parent is not None
                represented_parent = representative_scope_instance[
                    scope_instance.parent
                ]
                if skip_scope_instance:
                    representative_scope_instance[scope_instance] = represented_parent
                    continue

                representative_scope_instance[scope_instance] = scope_instance
                b.add(
                    f"one sig {self._get_scope_instance_sig(scope_instance)} extends {sig} {{}}"
                )
                b.add(
                    "fact { "
                    + f"{self._get_scope_instance_sig(scope_instance)}.parent = {self._get_scope_instance_sig(represented_parent)}"
                    + " }"
                )

        b.add()
        with b.block("fact"):
            for thread in self.topology.get_scope_instances("thread"):
                representative = representative_scope_instance[thread]
                b.add(
                    f"// thread {thread.id} executes in scope {self._get_scope_instance_sig(representative)}"
                )
                for inst in self.program_order[thread.id]:
                    b.add(
                        f"{inst.alloy_id}.execscope_instance = {self._get_scope_instance_sig(representative)}"
                    )
