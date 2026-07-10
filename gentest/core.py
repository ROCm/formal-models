"""Helpers and base classes for memory consistency model test generation."""

from abc import ABC, abstractmethod
from collections import defaultdict
import re
from typing import *

from gentest.alloy_wrapper import CheckResult


class ParseError(Exception):
    """Error parsing an input test description."""

    pass


class InvalidInstError(Exception):
    def __init__(self, inst: "Instruction", message: str) -> None:
        message = "invalid instruction '{}' ('{}'): {}".format(
            inst.var, inst.opcode, message
        )
        super().__init__(message)


class SemanticError(Exception):
    pass


class AlloyBuilder:
    """Helper class to build Alloy code with proper indentation."""

    class AlloyBlock:
        def __init__(self, builder: "AlloyBuilder", end_char: str) -> None:
            self.builder = builder
            self.end_char = end_char

        def __enter__(self) -> None:
            self.builder.indent += 2

        def __exit__(
            self, exception_type, exception_value, exception_traceback
        ) -> None:
            self.builder.indent -= 2
            self.builder.add(self.end_char)

    def __init__(self) -> None:
        self.alloy = ""
        self.indent = 0

    def add(self, code: Optional[str] = None) -> None:
        """Add a line of Alloy code with automatic indentation.

        Adds a newline at the end. If `code` is None, adds an empty line.
        """
        if code is None:
            self.alloy += "\n"
        else:
            self.alloy += (" " * self.indent) + code + "\n"

    def block(self, title: Optional[str] = None) -> AlloyBlock:
        """Add a block with automatic indentation with the following form:
        ```
        <title> {
            ...
        }
        ```
        This function returns a context manager. While the context is open,
        lines added to the builder are inserted into the block and indented
        accordingly.
        """
        if title is None:
            self.add("{")
        else:
            self.add(str(title) + " {")
        return self.AlloyBlock(self, "}")

    def __str__(self) -> str:
        return self.alloy


class AlloyQuery:
    """A query for Alloy's SAT solver.

    Alloy is expected to return satisfiable or unsatisfiable (`is_sat`). The
    predicate is a string (optionally with instruction name placeholders) to be
    instantiated and inserted into the Alloy code. If no predicate is provided,
    the query concerns the satisfiability without additional constraints.

    Additional predicates are a list of strings (optionally with instruction
    name placeholders) that are ANDed to the main predicate.

    Multiplicities is a list of (count, sig_name) tuples that specify the Alloy
    scope (i.e., the number of atoms per signature) for the query.
    """

    def __init__(
        self,
        label: Optional[str],
        is_sat: bool,
        predicate: Optional[str],
        additional_predicates: list[str],
        multiplicities: list[tuple[int, str]],
    ) -> None:
        self.label = label
        self.is_sat = is_sat
        self.predicate = predicate
        self.additional_predicates = additional_predicates
        self.multiplicities = multiplicities


class Topology:
    """ A tree of scope instances that are arranged in a fixed hierarchy of
    levels.

    For example, with a level hierarchy of [system, workgroup, wave, thread],
    this could be a Topology:

    ```
    system (root):    ()
                    /    \\
    workgroups:  wg1      wg2
                  |      /   \\
    waves:      wave1 wave2 wave3
                /  |    |   / |  \\
    threads:   t1  t2  t3  t4 t5 t6
    ```

    Each scope instance has an `id`, they are unique per level. There can only
    be a single (root) scope instance at the widest level, it is implicitly
    constructed.

    The Topology is constructed by a sequence of calls to open_scope; the
    Topology keeps track of a currently open scope instance relative to which
    new ones are inserted.
    """

    class TopologyError(Exception):
        pass

    class ScopeInstance:
        """An instance of a scope in the Topology hierarchy."""

        def __init__(
            self,
            topo: "Topology",
            level_idx: int,
            id: str,
            parent: Optional["Topology.ScopeInstance"],
        ) -> None:
            self.topo = topo
            self.level_idx = level_idx
            self.id = id
            self.parent = parent
            self.children: list[Topology.ScopeInstance] = []
            if parent is not None:
                parent.children.append(self)

        def __eq__(self, other: Any) -> bool:
            if self is other:
                return True
            if not isinstance(other, Topology.ScopeInstance):
                return NotImplemented
            return self.level_idx == other.level_idx and self.id == other.id

        def __hash__(self) -> int:
            return hash((self.level_idx, self.id))

        @property
        def level(self) -> str:
            return self.topo._idx2level[self.level_idx]

        def is_bottom(self) -> bool:
            """Return True if the scope instance is at the bottom hierarchy
            level (usually: thread scope)."""
            return self.level_idx == self.topo._bottom_idx

        def is_at_most(self, level: str) -> bool:
            """Return True if the scope instance is at the given hierarchy level
            or a narrower one (i.e., farther away from the root).
            """
            return self.level_idx >= self.topo._level2idx[level]

        def get_ancestor_at(self, level: str) -> "Topology.ScopeInstance":
            """Return the ancestor of this scope instance that is at the given
            hierarchy level. Raises an exception if this scope instance is not
            at or below the given level.
            """
            target_idx = self.topo._level2idx[level]
            if self.level_idx < target_idx:
                raise Topology.TopologyError(
                    f"scope instance {self} is not at or below level {level}"
                )
            scope_instance = self
            while scope_instance.level_idx > target_idx:
                assert scope_instance.parent is not None
                scope_instance = scope_instance.parent
            return scope_instance

    implicit_scope_instance_id = "_implicit"

    def __init__(self, levels: list[str]) -> None:
        self.root_scope_instance = Topology.ScopeInstance(
            self, 0, self.implicit_scope_instance_id, None
        )
        self.current_scope_instance = self.root_scope_instance
        self.scope_instances_per_level: dict[int, dict[str, Topology.ScopeInstance]] = (
            dict()
        )

        self._level2idx = {l: x for x, l in enumerate(levels)}
        self._idx2level = {x: l for x, l in enumerate(levels)}
        self._bottom_idx = len(levels) - 1

        for idx in self._idx2level.keys():
            self.scope_instances_per_level[idx] = dict()
        self.scope_instances_per_level[0] = {
            self.implicit_scope_instance_id: self.root_scope_instance
        }

    def open_scope_instance(self, level: str, id: str) -> None:
        """Create a new scope instance in the hierarchy based on
        current_scope_instance.

        The new scope instance is inserted as child of the scope instance in the
        current_scope_instance's parent chain (including itself) whose level is
        immediately above the specified level. The new scope instance is set as
        the new current_scope_instance.

        If levels between current_scope_instance and the specified level are
        missing, implicit scope instances with the same ID as their parent are
        created at those levels and inserted into the hierarchy. This allows
        that a prefix of the level hierarchy can be omitted.

        Raises a TopologyError if
        - no suitable parent scope instance could be found or created or
        - a scope instance with this level and id has already been opened
          before.
        """
        assert not id.startswith(
            "_"
        ), "IDs starting with an underscore are reserved for internal use"

        level_idx = self._level2idx[level]
        assert level_idx > 0, "cannot create new root scope"

        if id in self.scope_instances_per_level[level_idx]:
            raise Topology.TopologyError(f"duplicate '{level}' scope instance '{id}'")

        # For convenience, fill all skipped scope levels with implicit scope
        # instances with the same ID as their parent.
        for idx in range(self.current_scope_instance.level_idx + 1, level_idx):
            parent_id = self.current_scope_instance.id
            new_scope_instance = Topology.ScopeInstance(
                self, idx, parent_id, self.current_scope_instance
            )
            if parent_id in self.scope_instances_per_level[idx]:
                raise Topology.TopologyError(
                    f"failed to construct implicit '{self._idx2level[idx]}' scope instance above '{level}' scope instance '{id}': duplicate ID '{parent_id}'"
                )
            self.scope_instances_per_level[idx][parent_id] = new_scope_instance
            self.current_scope_instance = new_scope_instance

        assert (
            level_idx <= self.current_scope_instance.level_idx + 1
        ), "missing intermediate scope levels should have been filled with implicit scope instances"

        # Pop scope instances below the target parent scope instance from the
        # stack.
        while self.current_scope_instance.level_idx >= level_idx:
            assert self.current_scope_instance.parent is not None
            self.current_scope_instance = self.current_scope_instance.parent

        # Insert the new scope instance.
        new_scope_instance = Topology.ScopeInstance(
            self, level_idx, id, self.current_scope_instance
        )
        self.scope_instances_per_level[level_idx][id] = new_scope_instance
        self.current_scope_instance = new_scope_instance

    def get_scope_instances(self, level: str) -> list[ScopeInstance]:
        """Get a list of all scope instances with the specified level."""
        return [
            v for k, v in self.scope_instances_per_level[self._level2idx[level]].items()
        ]

    def get_scope_instance(self, level: str, id: str) -> Optional[ScopeInstance]:
        """Get the scope instance with the specified level and id or None if it
        does not exist in the Topology."""
        return self.scope_instances_per_level[self._level2idx[level]].get(id)

    def get_common_scope_instance(
        self, a: ScopeInstance, b: ScopeInstance
    ) -> ScopeInstance:
        """Get the narrowest scope instance that contains both given scope
        instances."""
        while a.level_idx < b.level_idx:
            assert b.parent is not None
            b = b.parent
        while b.level_idx < a.level_idx:
            assert a.parent is not None
            a = a.parent

        assert a.level_idx == b.level_idx

        while a.id != b.id:
            assert a.parent is not None and b.parent is not None
            a = a.parent
            b = b.parent

        return a


class Instruction:
    """A parsed instruction.

    The constructor specifies fields that are common between ModelTest
    implementations. Additional model-specific fields may be added after the
    Instruction is created.
    """

    def __init__(
        self,
        alloy_id: str,
        opcode: str,
        execscope_instance: Topology.ScopeInstance,
        addr: Optional[str],
        var: Optional[str],
        src_line: str,
    ) -> None:
        self.alloy_id: str = alloy_id
        """Identifier used to represent the instruction in the Alloy formulas."""
        self.opcode: str = opcode
        """Opcode of the instruction, for improved printing."""
        self.execscope_instance: Topology.ScopeInstance = execscope_instance
        """ScopeInstance in which the instruction is executed."""
        self.addr: Optional[str] = addr
        """Address operand of the instruction, if applicable."""
        self.var: Optional[str] = var
        """Identifier declared in the input to refer to this instruction in predicates."""
        self.src: str = src_line
        """Input line defining this instruction, for printing."""
        self.additional_data: dict[str, str] = dict()
        """Additional, model-specific data for this instruction."""


class ModelTest(ABC):
    """Abstract base class with shared functionality for test generation.

    When a new test flavor needs to be supported, a new implementation of the
    ABC with suitable implementations of the abstract functions should be added.

    New test classes need to be added to the register_models function in cli.py.
    """

    @classmethod
    @abstractmethod
    def register_arg_subparser(cls, subparsers) -> None:
        """Register an argument subparser.

        This class method is called to add a subparser for the model test
        class to the argument parser. The subclass should add any model-specific
        arguments to the parser.
        """
        pass

    @abstractmethod
    def get_scope_hierarchy(self) -> list[str]:
        """Return the hierarchy of scopes of concurrent computation.

        This must to be ordered from the widest to the narrowest scopes,
        starting with the level of the root scope (typically "system").
        """
        pass

    @abstractmethod
    def parse_instruction(
        self, line: str, var: Optional[str], scope: Topology.ScopeInstance
    ) -> Instruction:
        """Parse an instruction line.

        The optional leading identifier to refer to the instruction is already
        removed from the line and passed as `var`. `scope` is the scope instance
        in which the instruction lives (it is guaranteed to be a scope instance
        on the lowest level of the scope hierarchy).
        Raises ParseError if the line does not represent a valid instruction.
        """
        pass

    @abstractmethod
    def to_alloy(self, root_name: str, module_path: str) -> str:
        """Generate an Alloy module that contains the test."""
        pass

    def parse_custom_directive(
        self, line: str, directive: str, args: list[str]
    ) -> bool:
        """Parse a model-specific additional directive.

        Returns `True` if the directive has been parsed and `False` if it hasn't
        been matched. Raises `ParseError` if it matches but cannot be parsed.
        Overriding this is optional for subclasses.
        """
        # By default: nothing to parse.
        return False

    def __init__(self) -> None:
        # for error reporting
        self.current_line: Optional[str] = None
        self.current_line_number: int = 0

        # Maps opcodes to the next id number for that opcode.
        self._next_inst_ids: dict[str, int] = defaultdict(int)

        self.substitutions: dict[str, str] = dict()
        self.program_order: dict[str, list[Instruction]] = defaultdict(list)
        """Mapping from bottom-level scope instance ID to the list of Instructions that is executed there."""
        self.all_insts: list[Instruction] = list()

        self.topology = Topology(self.get_scope_hierarchy())
        self.scope_levels = set(self.get_scope_hierarchy())

        self.checks: list[AlloyQuery] = list()
        """List of all registered Alloy check queries in the user-specified order."""
        self.check_for_label: dict[str, AlloyQuery] = dict()
        """Mapping from labels to registered Alloy check queries."""
        self.checkline_for_label: dict[str, Optional[str]] = dict()
        """Mapping from labels to the check directive lines in the input (for printing)."""

        self.predicate_stack: list[str] = list()
        """Stack of additional predicates that are automatically added to declared checks."""

    def _create_instruction_id(self, var: Optional[str], opcode: Optional[str]) -> str:
        if var is not None:
            id = var
        else:
            assert (
                opcode is not None
            ), "opcode must be provided if no variable is declared for the instruction"
            id = f"_{opcode}_{self._next_inst_ids[opcode]}"
            self._next_inst_ids[opcode] += 1
        return id

    def _substitute_variables(self, alloy_pred: str) -> str:
        """Substitute the registered placeholders in Alloy formulas for the
        Alloy identifiers.
        """
        res = alloy_pred
        # Sort substitutions by length of the placeholder in descending order to
        # avoid partial replacement of placeholders that are substrings of other
        # placeholders. For example, if we have placeholders $A and $A1, we want
        # to replace $A1 before $A.
        substitutions_sorted = sorted(
            self.substitutions.items(), key=lambda x: len(x[0]), reverse=True
        )
        for key, value in substitutions_sorted:
            res = res.replace("$" + key, value)
        return res

    name_regex = re.compile(r"^\$([A-Za-z][A-Za-z0-9_]*):")

    def parse_line(self, line: str) -> None:
        """Parse a single line of the input test description.

        Raises ParseError on syntax errors.
        """
        self.current_line = line
        self.current_line_number += 1

        line = line.strip()
        if not line:
            return

        # handle whole line comments
        if line.startswith("//"):
            return

        # handle end of line comments
        if line.count("//") != 0:
            line = line.split("//")[0]

        if line.startswith("#"):
            self._parse_directive(line)
            return

        # We are looking at an instruction.

        # Instructions can only occur at the bottom-most level of the scope
        # hierarchy.
        scope_instance = self.topology.current_scope_instance
        if not scope_instance.is_bottom():
            raise self._parse_error(
                f"missing #{self.get_scope_hierarchy()[-1]} directive"
            )

        # Try parsing an optional identifier for the instruction.
        var = None
        if match := self.name_regex.match(line):
            var = match[1]
            line = line[match.end() :]
            if var.startswith("_"):
                raise self._parse_error(
                    "invalid instruction identifier: cannot start with underscore"
                )

        parsed_inst = self.parse_instruction(line, var, scope_instance)

        self._register_instruction(parsed_inst)

    def _register_instruction(self, inst: Instruction) -> None:
        """Register a parsed instruction in the test.

        This adds the instruction to the program order and registers any
        variable substitutions.
        """
        # Register the instruction in the program order.
        self.program_order[inst.execscope_instance.id].append(inst)
        self.all_insts.append(inst)

        # Register the identifier for substitutions in check predicates.
        if inst.var is not None:
            if inst.var in self.substitutions:
                raise self._parse_error(f"duplicate instruction identifier: {inst.var}")
            self.substitutions[inst.var] = inst.alloy_id

    def _register_query(self, q: AlloyQuery, line: Optional[str]) -> None:
        """Register an Alloy query in the test.

        If q.label is None, a numbered default label is generated and set.
        """
        if q.label is None:
            q.label = f"check_{len(self.checks)}"
        if q.label in self.check_for_label:
            raise self._parse_error(f"duplicate check label '{q.label}'")
        self.checks.append(q)
        self.check_for_label[q.label] = q
        self.checkline_for_label[q.label] = None if line is None else line.strip()

    def push_predicates(self, predicates: list[str]) -> None:
        for predicate in predicates:
            self.predicate_stack.append(predicate)

    def _parse_error(self, msg: str) -> ParseError:
        """Convenience function to create a ParseError exception decorated with
        the current line number and line text."""
        fmt_msg = f"line {self.current_line_number}: {msg}: {self.current_line}"
        return ParseError(fmt_msg)

    scope_instance_id_regex = re.compile(r"^([A-Za-z0-9][A-Za-z0-9_]*)$")

    def _parse_directive(self, line: str) -> None:
        """Parse a directive line starting with '#'."""
        items = line[1:].split()
        if len(items) == 0:
            raise self._parse_error("broken # directive")

        directive = items[0]
        args = items[1:]

        if directive == "check" or directive == "assert":
            # #check (sat|unsat) [alloy..] [for [N1 S1 [N2 S2 ...]]]
            # #assert [alloy..] [for [N1 S1 [N2 S2 ...]]]
            if len(args) == 0:
                raise self._parse_error(f"ill-formed #{directive} directive")

            is_assert = directive == "assert"
            if is_assert:
                # "#assert X" is equivalent to "#check unsat not (X)"
                is_sat = False
            else:
                if args[0] == "sat":
                    is_sat = True
                elif args[0] == "unsat":
                    is_sat = False
                else:
                    raise self._parse_error(
                        'ill-formed #{} directive: expected "sat" or "unsat", got "{}"'.format(
                            directive, args[0]
                        )
                    )

                args = args[1:]

            # Parse predicate and multiplicities.
            predicate_parts = []
            multiplicities = []

            # Find the first "for" keyword. That shouldn't occur in an Alloy predicate.
            for_index = None
            for idx, arg in enumerate(args):
                if arg == "for":
                    for_index = idx
                    break

            if for_index is not None:
                # Predicate is everything between sat/unsat and "for"
                predicate_parts = args[:for_index]

                # Parse multiplicities after "for"
                mult_args = args[for_index + 1 :]
                if len(mult_args) % 2 != 0:
                    raise self._parse_error(
                        f"ill-formed multiplicities in #{directive} directive: expected pairs of <count> <sig>"
                    )

                for j in range(0, len(mult_args), 2):
                    try:
                        count = int(mult_args[j])
                    except ValueError:
                        raise self._parse_error(
                            f'ill-formed multiplicities in #{directive} directive: expected integer, got "{mult_args[j]}"'
                        )
                    sig_name = mult_args[j + 1]
                    multiplicities.append((count, sig_name))
            else:
                # No "for" keyword, everything is part of the predicate.
                predicate_parts = args

            predicate = " ".join(predicate_parts) if len(predicate_parts) > 0 else None

            if is_assert:
                if predicate is None:
                    raise self._parse_error(
                        f"ill-formed #{directive} directive: missing predicate"
                    )
                # An assertion is equivalent to checking unsatisfiability of the
                # negated predicate.
                predicate = f"not ({predicate})"

            label = None  # TODO allow specifying custom check labels?
            self._register_query(
                AlloyQuery(
                    label,
                    is_sat,
                    predicate,
                    additional_predicates=list(self.predicate_stack),
                    multiplicities=multiplicities,
                ),
                self.current_line,
            )
        elif directive == "push":
            # #push [alloy..]
            # Pushes the Alloy code to the stack of additional predicates that
            # are added to declared checks.
            if len(args) == 0:
                raise self._parse_error("missing predicate in #push directive")
            predicate = " ".join(args)
            self.predicate_stack.append(predicate)
        elif directive == "pop":
            # #pop [n]
            # pops n previously pushed and not yet popped predicates from the stack. n=1 if omitted.
            if len(args) > 1:
                raise self._parse_error("too many arguments in #pop directive")
            num = 1
            if len(args) == 1:
                try:
                    num = int(args[0])
                except:
                    raise self._parse_error(
                        "argument of #pop directive must be a positive integer"
                    )
            if num <= 0:
                raise self._parse_error(
                    "argument of #pop directive must be a positive integer"
                )
            if num > len(self.predicate_stack):
                raise self._parse_error(
                    "trying to #pop more predicates than are on the stack"
                )
            for x in range(num):
                self.predicate_stack.pop()
        elif directive in self.scope_levels:
            if len(args) != 1:
                raise self._parse_error(f"ill-formed #{directive} directive")
            id = args[0]
            if not self.scope_instance_id_regex.match(id):
                if id.startswith("_"):
                    raise self._parse_error(
                        f"invalid scope instance identifier in #{directive} directive: identifiers cannot start with an underscore"
                    )
                raise self._parse_error(
                    f"invalid scope instance identifier in #{directive} directive: '{id}'"
                )
            self.topology.open_scope_instance(directive, id)
        elif not self.parse_custom_directive(line, directive, args):
            raise self._parse_error("unknown # directive")

    def _verify(self) -> None:
        pass

    def _encode_all_checks(
        self, b: AlloyBuilder, allow_default_check: bool = True
    ) -> None:
        """Insert run lines for all registered checks with the provided builder.

        This is a helper that can be used in to_alloy. If allow_default_check is
        True, an implicit default '#check sat' line with the current state of the
        stack is added if no check line is present in the test.
        """
        if len(self.checks) == 0:
            if not allow_default_check:
                raise SemanticError('test is missing "#check sat" or "#check unsat"')
            self._register_query(
                AlloyQuery("check_default", True, None, list(self.predicate_stack), []),
                "#check sat",
            )

        b.add(f"// Checks:")
        for check in self.checks:
            self._encode_check(b, check)

    def _encode_check(self, b: AlloyBuilder, check: AlloyQuery) -> None:
        """Insert a run line for a single check with the provided builder."""
        with b.block(f"run {check.label}"):
            if check.predicate is not None:
                b.add(self._substitute_variables(check.predicate))
            for p in check.additional_predicates:
                b.add(self._substitute_variables(p))
        multiplicity_str = ""
        if len(check.multiplicities) > 0:
            mult_strs = [f"{count} {sig}" for count, sig in check.multiplicities]
            multiplicity_str = " but " + (" ".join(mult_strs))
        b.add(f"for 0{multiplicity_str} expect {int(check.is_sat)}")
        b.add()

    def format_check_result(self, check_result: CheckResult) -> str:
        """Format an alloy_wrapper.CheckResult for the Alloy module generated
        from this test instance.

        In contrast to the __str__ method of CheckResult, this can use any
        additional useful information that the user provided in the test but
        that is not present in the Alloy module, like what exactly the
        corresponding check line looks like.
        """
        check = self.check_for_label.get(check_result.label, None)
        assert check is not None, "trying to format result for unknown check"

        checkline = self.checkline_for_label.get(check_result.label, None)

        assuming_str = ""
        if len(check.additional_predicates) > 1:
            assuming_str = ", assuming " + " and ".join(
                map(lambda s: f"({s})", check.additional_predicates)
            )
        elif len(check.additional_predicates) == 1:
            assuming_str = f", assuming {check.additional_predicates[0]}"
        res = f"{check_result.label}{assuming_str}:\n"
        if checkline is not None:
            res += f"  {checkline}\n"
        res += f"  {check_result.success_str}: {check_result.msg}"
        return res
