#!/usr/bin/env pytest

"""Tests for the gentest test generator.

Running these tests requires pytest; but running them is only necessary when
working on gentest, not when using gentest to build Alloy tests.
"""

import pytest

import gentest.core as core
import gentest.llvm as llvm


class ModelOptions:
    def __init__(self, **kwargs) -> None:
        for k, v in kwargs.items():
            setattr(self, k, v)


def parseInput(model_type, text, options=None):
    model = model_type(options)
    lines = text.split("\n")
    for l in lines:
        model.parse_line(l)
    return model


def test_ir_alnum_scope_instances():
    test_input = """
      #thread 0
        store A

      #thread B
        store B

      #thread abc012
        store C
    """
    parseInput(llvm.LLVMIRTest, test_input)


def test_predicate_stack_small():
    test_input = """
      #push A
      #pop
    """
    m = parseInput(llvm.LLVMIRTest, test_input)
    assert len(m.predicate_stack) == 0


def test_predicate_stack_no_pop():
    test_input = """
      #push A
    """
    m = parseInput(llvm.LLVMIRTest, test_input)
    assert len(m.predicate_stack) == 1


def test_predicate_stack_deeper():
    test_input = """
      #push A
      #push B
      #push C
      #pop
      #pop
      #pop
    """
    m = parseInput(llvm.LLVMIRTest, test_input)
    assert len(m.predicate_stack) == 0


def test_predicate_stack_deeper_no_pop():
    test_input = """
      #push A
      #push B
      #push C
    """
    m = parseInput(llvm.LLVMIRTest, test_input)
    assert len(m.predicate_stack) == 3


def test_predicate_stack_multipop():
    test_input = """
      #push A
      #push B
      #push C
      #pop 3
    """
    m = parseInput(llvm.LLVMIRTest, test_input)
    assert len(m.predicate_stack) == 0


def test_predicate_stack_multipop_some():
    test_input = """
      #push A
      #push B
      #push C
      #pop 2
    """
    m = parseInput(llvm.LLVMIRTest, test_input)
    assert len(m.predicate_stack) == 1


def test_predicate_stack_broken_pop():
    test_input = """
      #pop
    """
    with pytest.raises(core.ParseError):
        parseInput(llvm.LLVMIRTest, test_input)


def test_predicate_stack_broken_more_pop_than_push():
    test_input = """
      #push A
      #pop
      #pop
    """
    with pytest.raises(core.ParseError):
        parseInput(llvm.LLVMIRTest, test_input)


def test_predicate_stack_broken_negative_pop():
    test_input = """
      #push A
      #pop -1
    """
    with pytest.raises(core.ParseError):
        parseInput(llvm.LLVMIRTest, test_input)


def test_predicate_stack_broken_pop_0():
    test_input = """
      #push A
      #pop 0
    """
    with pytest.raises(core.ParseError):
        parseInput(llvm.LLVMIRTest, test_input)


def test_predicate_stack_broken_pop_too_many():
    test_input = """
      #push A
      #pop 2
    """
    with pytest.raises(core.ParseError):
        parseInput(llvm.LLVMIRTest, test_input)


def test_predicate_stack_semantics():
    test_input = """
      #check sat test0
      #push A
      #check sat test1
      #check sat test2
      #push B
      #push C
      #check sat test3
      #check sat
      #pop 2
      #check sat test5
      #push D
      #check sat test6
      #pop
      #check sat test7
      #pop
      #check sat test8
      #check sat
    """
    m = parseInput(llvm.LLVMIRTest, test_input)
    assert len(m.checks) == 10

    def validate_check(idx, pred, additional_preds):
        check = m.checks[idx]
        assert check.predicate == pred
        assert set(check.additional_predicates) == set(additional_preds)

    validate_check(0, "test0", [])
    validate_check(1, "test1", ["A"])
    validate_check(2, "test2", ["A"])
    validate_check(3, "test3", ["A", "B", "C"])
    validate_check(4, None, ["A", "B", "C"])
    validate_check(5, "test5", ["A"])
    validate_check(6, "test6", ["A", "D"])
    validate_check(7, "test7", ["A"])
    validate_check(8, "test8", [])
    validate_check(9, None, [])


def test_ir_parse_ordering_constraints():
    test_input = """
      #thread 0
      store a
      store.unordered a
      store.monotonic a
      store.release a
      store.seq_cst a

      load a
      load.unordered a
      load.monotonic a
      load.acquire a
      load.seq_cst a

      rmw.monotonic a
      rmw.acquire a
      rmw.release a
      rmw.acq_rel a
      rmw.seq_cst a

      fence.acquire
      fence.release
      fence.acq_rel
      fence.seq_cst
    """
    instance = parseInput(llvm.LLVMIRTest, test_input)

    def instruction_matches(idx, expected_opc, expected_ordering):
        instr = instance.all_insts[idx]
        return (
            instr.opcode == expected_opc
            and instr.additional_data.get("ordering") == expected_ordering
        )

    assert len(instance.all_insts) == 19
    assert instruction_matches(0, "store", None)
    assert instruction_matches(1, "store", "unordered")
    assert instruction_matches(2, "store", "monotonic")
    assert instruction_matches(3, "store", "release")
    assert instruction_matches(4, "store", "seq_cst")

    assert instruction_matches(5, "load", None)
    assert instruction_matches(6, "load", "unordered")
    assert instruction_matches(7, "load", "monotonic")
    assert instruction_matches(8, "load", "acquire")
    assert instruction_matches(9, "load", "seq_cst")

    assert instruction_matches(10, "rmw", "monotonic")
    assert instruction_matches(11, "rmw", "acquire")
    assert instruction_matches(12, "rmw", "release")
    assert instruction_matches(13, "rmw", "acq_rel")
    assert instruction_matches(14, "rmw", "seq_cst")

    assert instruction_matches(15, "fence", "acquire")
    assert instruction_matches(16, "fence", "release")
    assert instruction_matches(17, "fence", "acq_rel")
    assert instruction_matches(18, "fence", "seq_cst")


def test_ir_parse_syncscope():
    test_input = """
      #thread 0
      store.release a
      store.release.ss=system a
      store.release.ss=singlethread a
      store.release.ss=thread a
      store.release.ss=st a
    """
    instance = parseInput(llvm.LLVMIRTest, test_input)

    def instruction_matches(idx, opc, expected_scope):
        instr = instance.all_insts[idx]
        return (
            instr.opcode == opc
            and instr.additional_data.get("syncscope") == expected_scope
        )

    assert len(instance.all_insts) == 5
    assert instruction_matches(0, "store", "system")
    assert instruction_matches(1, "store", "system")
    assert instruction_matches(2, "store", "thread")
    assert instruction_matches(3, "store", "thread")
    assert instruction_matches(4, "store", "thread")


def test_assert_valid():
    test_input = """
      #assert some_predicate
    """
    m = parseInput(llvm.LLVMIRTest, test_input)
    assert len(m.checks) == 1
    check = m.checks[0]
    assert check.is_sat is False
    # An assertion is represented as an unsat check of the negated predicate.
    assert check.predicate == "not (some_predicate)"


def test_assert_invalid_missing_predicate():
    test_input = """
      #assert
    """
    with pytest.raises(core.ParseError):
        parseInput(llvm.LLVMIRTest, test_input)


def test_assert_with_multiplicities():
    test_input = """
      #assert my_predicate for 3 SigA 7 SigB
    """
    m = parseInput(llvm.LLVMIRTest, test_input)
    assert len(m.checks) == 1
    check = m.checks[0]
    assert check.is_sat is False
    assert check.predicate == "not (my_predicate)"
    assert check.multiplicities == [(3, "SigA"), (7, "SigB")]


def test_assert_invalid_multiplicity():
    test_input = """
      #assert my_predicate for 3 SigA 2
    """
    with pytest.raises(core.ParseError):
        parseInput(llvm.LLVMIRTest, test_input)
