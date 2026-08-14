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
        self.legal_opcodes: set[str] = {"load", "store", "rmw", "fence"}
        self.legal_ordering_constraints = {
            "unordered",
            "monotonic",
            "acquire",
            "release",
            "acq_rel",
            "seq_cst",
        }

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

    def validate_instruction(self, inst: Instruction) -> bool:
        """Validate semantic constraints on the provided instruction.

        Raises ParseError if an error is found, returns True if validation is
        successful, returns False if the instruction was not checked.
        """

        def error_if(cond, errmsg):
            if cond:
                raise self._parse_error(errmsg)

        ordering = inst.additional_data.get("ordering")
        syncscope = inst.additional_data.get("syncscope")

        def access_checks():
            error_if(
                len(inst.operands) > 1,
                f"too many address arguments for {inst.opcode}",
            )
            error_if(inst.addr is None, f"missing address argument for {inst.opcode}")
            error_if(
                syncscope is not None and ordering is None,
                "superfluous scope on a non-atomic operation",
            )

        match inst.opcode:
            case "load":
                access_checks()
                error_if(
                    ordering in ("release", "acq_rel"),
                    "load cannot release",
                )
                return True
            case "store":
                access_checks()
                error_if(
                    ordering in ("acquire", "acq_rel"),
                    "store cannot acquire",
                )
                return True
            case "rmw":
                access_checks()
                error_if(
                    ordering in (None, "unordered"),
                    "rmw must be at least monotonic",
                )
                return True
            case "fence":
                error_if(
                    len(inst.operands) > 0, "superfluous address argument for fence"
                )
                error_if(
                    ordering not in ("release", "acquire", "acq_rel", "seq_cst"),
                    "fences must have an ordering that is stricter than monotonic",
                )
                return True
        return False

    def parse_modifier(self, dest: dict[str, Any], modifier: str) -> bool:
        """Parse the provided modifier and store relevant data to the dest
        dictionary. Dest contains information from previous calls and is added
        to the instructions additional_data once the instruction is parsed
        completely.

        Raises ParseError if an error is found, returns True if parsing is
        successful, returns False if the modifier is not recognized.
        """
        if modifier in self.legal_ordering_constraints:
            if dest.get("ordering") is not None:
                raise self._parse_error(f"more than one ordering constraint")
            dest["ordering"] = modifier
            return True
        elif modifier.startswith("ss="):
            if dest.get("syncscope") is not None:
                raise self._parse_error(f"more than one syncscope")
            modifier = modifier[3:]
            if mat := self.get_syncscope_mapping().get(modifier):
                dest["syncscope"] = mat
                return True
            raise self._parse_error(f'unknown syncscope "{modifier}"')
        return False

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

        modifier_data: dict[str, Any] = dict()
        for mod in modifiers:
            if not self.parse_modifier(modifier_data, mod):
                raise self._parse_error(f'unknown modifier "{mod}"')

        operands = list(args)

        if (
            modifier_data.get("syncscope") is None
            and modifier_data.get("ordering") is not None
        ):
            modifier_data["syncscope"] = "system"  # default syncscope

        alloy_id = self._create_instruction_id(var, opcode)
        parsed_inst = Instruction(alloy_id, opcode, scope, operands, var)
        parsed_inst.additional_data.update(modifier_data)
        self.validate_instruction(parsed_inst)

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

    opcode_to_sig = {
        "load": "SimpleRead",
        "store": "SimpleWrite",
        "rmw": "RMW",
        "fence": "Fence",
    }

    def _encode_instruction(
        self,
        b: AlloyBuilder,
        inst: Instruction,
        used_addrs: set[str],
        used_scope_instances: set[Topology.ScopeInstance],
        additional_po: list[str],
    ) -> None:
        maybe_sig = self.opcode_to_sig.get(inst.opcode)
        assert maybe_sig is not None, f"unknown opcode {inst.opcode}"
        sig = maybe_sig
        b.add(f"one sig {inst.alloy_id} extends {sig} {{}}")

        with b.block(f"fact {inst.alloy_id}_properties"):
            ordering = inst.additional_data.get("ordering")
            match ordering:
                case None:
                    b.add(f"{inst.alloy_id} not in Atomic")
                case "unordered":
                    b.add(f"{inst.alloy_id} in Atomic - Monotonic")
                case "monotonic":
                    b.add(f"{inst.alloy_id} in Monotonic - (Acquire + Release)")
                case "release":
                    b.add(f"{inst.alloy_id} in Release - (Acquire + SeqCst)")
                case "acquire":
                    b.add(f"{inst.alloy_id} in Acquire - (Release + SeqCst)")
                case "acq_rel":
                    b.add(f"{inst.alloy_id} in (Acquire & Release) - SeqCst")
                case "seq_cst":
                    b.add(f"{inst.alloy_id} in SeqCst")

            if ordering is not None:
                syncscope = inst.additional_data.get("syncscope")
                assert syncscope is not None
                syncscope_instance = inst.execscope_instance.get_ancestor_at(syncscope)
                b.add(
                    f"{inst.alloy_id}.syncscope_instance = {self._get_scope_instance_sig(syncscope_instance)}"
                )
                used_scope_instances.add(syncscope_instance)

            if inst.addr is not None:
                init_id = self._get_init_sig(inst.addr)
                b.add(f"{inst.alloy_id} -> {init_id} in same_location")
                used_addrs.add(inst.addr)

    def _get_init_sig(self, addr: str) -> str:
        return f"_Init_{addr}"

    def _get_scope_instance_sig(self, scope_instance: Topology.ScopeInstance) -> str:
        if scope_instance.level == "system":
            return "System"
        id_str = scope_instance.id
        return "_scope_{}_{}".format(scope_instance.level, id_str)

    def _encode_program(self, b: AlloyBuilder) -> None:
        po = list()
        all_addrs: set[str] = set()
        used_scope_instances: set[Topology.ScopeInstance] = set()
        for tid, insts in self.program_order.items():
            b.add(f"// Events for thread {tid}:")
            predecessor = None
            for inst in insts:
                additional_po: list[str] = []
                self._encode_instruction(
                    b,
                    inst,
                    used_addrs=all_addrs,
                    used_scope_instances=used_scope_instances,
                    additional_po=additional_po,
                )
                if predecessor is not None:
                    po.append(f"({predecessor.alloy_id} -> {inst.alloy_id})")
                po.extend(additional_po)
                predecessor = inst
                b.add()

        b.add(f"// Init Writes:")
        for addr in all_addrs:
            init_id = self._get_init_sig(addr)
            b.add(f"one sig {init_id} extends Init {{}}")
        b.add()

        with b.block("fact"):
            b.add(f"// program order:")
            if len(po) == 0:
                b.add("no po_imm")
            else:
                b.add("po_imm = {}".format(" + ".join(po)))
        b.add()

        self._encode_scope_hierarchy(b, used_scope_instances)

    def _encode_scope_hierarchy(
        self, b: AlloyBuilder, used_scope_instances: set[Topology.ScopeInstance]
    ) -> None:
        scope_encoding = self.scope_encoding
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
                    and scope_instance not in used_scope_instances
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
