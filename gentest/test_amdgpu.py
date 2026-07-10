#!/usr/bin/env pytest

"""Tests for the gentest test generator.

Running these tests requires pytest; but running them is only necessary when
working on gentest, not when using gentest to build Alloy tests.
"""

import pytest

import gentest.core as core
import gentest.llvm_amdgpu as amdgpu


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


def test_ir_all_hierarchies_binary():
    test_input = """
      #agent 0
      #cluster 0
      #workgroup 0
      #wave 0
      #thread 0
        store A
      #thread 1
        store B
      #wave 1
      #thread 2
        store C
      #workgroup 1
      #wave 2
      #thread 3
        store D
      #cluster 1
      #workgroup 2
      #wave 3
      #thread 4
        store E
      #agent 1
      #cluster 2
      #workgroup 3
      #wave 4
      #thread 5
        store F
    """
    instance = parseInput(amdgpu.AMDGPULLVMIRTest, test_input)
    topo = instance.topology
    assert len(topo.get_scope_instances("agent")) == 2
    assert len(topo.get_scope_instances("cluster")) == 3
    assert len(topo.get_scope_instances("workgroup")) == 4
    assert len(topo.get_scope_instances("wave")) == 5
    assert len(topo.get_scope_instances("thread")) == 6

    def L(level, id):
        return topo.get_scope_instance(level, id)

    assert L("thread", "0").parent is L("wave", "0")
    assert L("thread", "1").parent is L("wave", "0")
    assert L("thread", "2").parent is L("wave", "1")
    assert L("thread", "3").parent is L("wave", "2")
    assert L("thread", "4").parent is L("wave", "3")
    assert L("thread", "5").parent is L("wave", "4")

    assert L("wave", "0").parent is L("workgroup", "0")
    assert L("wave", "1").parent is L("workgroup", "0")
    assert L("wave", "2").parent is L("workgroup", "1")
    assert L("wave", "3").parent is L("workgroup", "2")
    assert L("wave", "4").parent is L("workgroup", "3")

    assert L("workgroup", "0").parent is L("cluster", "0")
    assert L("workgroup", "1").parent is L("cluster", "0")
    assert L("workgroup", "2").parent is L("cluster", "1")
    assert L("workgroup", "3").parent is L("cluster", "2")

    assert L("cluster", "0").parent is L("agent", "0")
    assert L("cluster", "1").parent is L("agent", "0")
    assert L("cluster", "2").parent is L("agent", "1")


def test_ir_skip_hierarchy_prefix():
    test_input = """
      #wave 0
      #thread 0
        store A
      #wave 1
      #thread 1
        store B
    """
    instance = parseInput(amdgpu.AMDGPULLVMIRTest, test_input)
    topo = instance.topology
    assert len(topo.get_scope_instances("agent")) == 1
    assert len(topo.get_scope_instances("cluster")) == 1
    assert len(topo.get_scope_instances("workgroup")) == 1
    assert len(topo.get_scope_instances("wave")) == 2
    assert len(topo.get_scope_instances("thread")) == 2

    def L(level, id):
        return topo.get_scope_instance(level, id)

    assert L("thread", "0").parent is L("wave", "0")
    assert L("thread", "1").parent is L("wave", "1")
    assert L("wave", "0").parent is L("wave", "1").parent

    assert L("wave", "0").parent is L("workgroup", "_implicit")
    assert L("wave", "1").parent is L("workgroup", "_implicit")
    assert L("workgroup", "_implicit").parent is L("cluster", "_implicit")
    assert L("cluster", "_implicit").parent is L("agent", "_implicit")


def test_ir_unique_ids():
    test_input = """
      #wave 0
      #thread 0
        store A
      #wave 1
      #thread 0
        store B
    """
    with pytest.raises(core.Topology.TopologyError):
        parseInput(amdgpu.AMDGPULLVMIRTest, test_input)


def test_ir_reopen_scope_instance():
    test_input = """
      #agent 1
      #cluster 1
      #workgroup 1
      #wave 1
      #thread 1
        store A
      #workgroup 2
      #wave 2
      #thread 2
        store B
      #workgroup 1
      #wave 1
      #thread 3
        store C
    """
    with pytest.raises(core.Topology.TopologyError):
        parseInput(amdgpu.AMDGPULLVMIRTest, test_input)


def test_ir_alnum_scope_instances():
    test_input = """
      #workgroup wgp
      #wave wv0
      #thread 0
        store A

      #wave wv1
      #thread 1
        store B
    """
    parseInput(amdgpu.AMDGPULLVMIRTest, test_input)


def test_ir_skip_scope01():
    test_input = """
      #cluster 1
      #thread 1
        store A
    """
    instance = parseInput(amdgpu.AMDGPULLVMIRTest, test_input)
    topo = instance.topology
    assert len(topo.get_scope_instances("agent")) == 1
    assert len(topo.get_scope_instances("cluster")) == 1
    assert len(topo.get_scope_instances("workgroup")) == 1
    assert len(topo.get_scope_instances("wave")) == 1
    assert len(topo.get_scope_instances("thread")) == 1

    def L(level, id):
        return topo.get_scope_instance(level, id)

    assert L("thread", "1").parent is L("wave", "1")
    assert L("wave", "1").parent is L("workgroup", "1")
    assert L("workgroup", "1").parent is L("cluster", "1")
    assert L("cluster", "1").parent is L("agent", "_implicit")


def test_ir_skip_scope02():
    test_input = """
      #workgroup 1
      #thread 1
        store A
      #workgroup 2
      #thread 2
        store B
      #workgroup 3
      #thread 3
        store C
    """
    instance = parseInput(amdgpu.AMDGPULLVMIRTest, test_input)
    topo = instance.topology
    assert len(topo.get_scope_instances("agent")) == 1
    assert len(topo.get_scope_instances("cluster")) == 1
    assert len(topo.get_scope_instances("workgroup")) == 3
    assert len(topo.get_scope_instances("wave")) == 3
    assert len(topo.get_scope_instances("thread")) == 3

    def L(level, id):
        return topo.get_scope_instance(level, id)

    assert L("thread", "1").parent is L("wave", "1")
    assert L("thread", "2").parent is L("wave", "2")
    assert L("thread", "3").parent is L("wave", "3")
    assert L("wave", "1").parent is L("workgroup", "1")
    assert L("wave", "2").parent is L("workgroup", "2")
    assert L("wave", "3").parent is L("workgroup", "3")
    assert L("workgroup", "1").parent is L("cluster", "_implicit")
    assert L("workgroup", "2").parent is L("cluster", "_implicit")
    assert L("workgroup", "3").parent is L("cluster", "_implicit")
    assert L("cluster", "_implicit").parent is L("agent", "_implicit")


def test_ir_fail_to_skip_scope():
    test_input = """
      #agent 0
      #cluster 0
      #workgroup 0
      #wave 1
      #thread 1
        store A

      #cluster 1
      #thread 2
        store B
    """
    with pytest.raises(core.Topology.TopologyError):
        parseInput(amdgpu.AMDGPULLVMIRTest, test_input)


def test_scope_hierarchy_full_encoding():
    test_input = """
      #agent 0
      #cluster 0
      #workgroup 0
      #wave 0
      #thread 0
        store.release.ss=system A
      #thread 1
        store.release.ss=agent B
      #workgroup 1
      #wave 1
      #thread 2
        store.release.ss=workgroup C
      #check sat
    """
    instance = parseInput(
        amdgpu.AMDGPULLVMIRTest,
        test_input,
        ModelOptions(scope_encoding=amdgpu.ScopeEncoding.FULL),
    )
    alloy = instance.to_alloy("test", "test")

    # All scopes should be defined
    assert "_scope_agent_0" in alloy
    assert "_scope_cluster_0" in alloy
    assert "_scope_workgroup_0" in alloy
    assert "_scope_workgroup_1" in alloy
    assert "_scope_wave_0" in alloy
    assert "_scope_wave_1" in alloy
    assert "_scope_thread_0" in alloy
    assert "_scope_thread_1" in alloy
    assert "_scope_thread_2" in alloy

    # Check parent relationships
    assert "_scope_cluster_0.parent = _scope_agent_0" in alloy
    assert "_scope_workgroup_0.parent = _scope_cluster_0" in alloy
    assert "_scope_workgroup_1.parent = _scope_cluster_0" in alloy
    assert "_scope_wave_0.parent = _scope_workgroup_0" in alloy
    assert "_scope_wave_1.parent = _scope_workgroup_1" in alloy


def test_scope_hierarchy_optimized_encoding():
    test_input = """
      #agent 0
      #cluster 0
      #workgroup 0
      #wave 0
      #thread 0
        store.release.ss=system A
      #thread 1
        store.release.ss=system B
      #workgroup 1
      #wave 1
      #thread 2
        store.release.ss=workgroup C
      #check sat
    """
    instance = parseInput(
        amdgpu.AMDGPULLVMIRTest,
        test_input,
        ModelOptions(scope_encoding=amdgpu.ScopeEncoding.OPTIMIZED),
    )
    alloy = instance.to_alloy("test", "test")

    # These can be skipped since they only have a single child:
    assert "_scope_agent_0" not in alloy
    assert "_scope_workgroup_0" not in alloy
    assert "_scope_wave_1" not in alloy
    assert "_scope_thread_0" not in alloy
    assert "_scope_thread_1" not in alloy
    assert "_scope_thread_2" not in alloy

    # These should still be present:
    assert "_scope_cluster_0" in alloy
    assert "_scope_wave_0" in alloy
    assert "_scope_workgroup_1" in alloy  # This one is referenced by the last store.

    # The parent relationships should be preserved.
    assert "_scope_cluster_0.parent = System" in alloy
    assert "_scope_wave_0.parent = _scope_cluster_0" in alloy
    assert "_scope_workgroup_1.parent = _scope_cluster_0" in alloy


def test_scope_hierarchy_optimized_preserves_referenced_scopes():
    test_input = """
      #agent 0
      #cluster 0
      #workgroup 0
      #wave 0
      #thread 0
        store.release.ss=agent A
      #thread 1
        store.release.ss=cluster B
      #check sat
    """
    instance = parseInput(
        amdgpu.AMDGPULLVMIRTest,
        test_input,
        ModelOptions(scope_encoding=amdgpu.ScopeEncoding.OPTIMIZED),
    )
    alloy = instance.to_alloy("test", "test")

    # Agent and cluster should NOT be optimized away because they are referenced
    assert "_scope_agent_0" in alloy
    assert "_scope_cluster_0" in alloy
    assert "_scope_cluster_0.parent = _scope_agent_0" in alloy


def test_scope_hierarchy_optimized_preserves_referenced_threadscope():
    test_input = """
      #agent 0
      #cluster 0
      #workgroup 0
      #wave 0
      #thread 0
        store.release.ss=singlethread A
      #thread 1
        store.release.ss=singlethread B
      #check sat
    """
    instance = parseInput(
        amdgpu.AMDGPULLVMIRTest,
        test_input,
        ModelOptions(scope_encoding=amdgpu.ScopeEncoding.OPTIMIZED),
    )
    alloy = instance.to_alloy("test", "test")

    assert "scope_agent_0" not in alloy
    assert "scope_cluster_0" not in alloy
    assert "scope_workgroup_0" not in alloy

    assert "scope_wave_0" in alloy
    assert "scope_thread_0" in alloy
    assert "scope_thread_1" in alloy


def test_ir_parse_syncscope():
    test_input = """
      #thread 0
      store.release a
      store.release.ss=system a
      store.release.ss=agent a
      store.release.ss=ag a
      store.release.ss=cluster a
      store.release.ss=cl a
      store.release.ss=workgroup a
      store.release.ss=wg a
      store.release.ss=wavefront a
      store.release.ss=wf a
      store.release.ss=singlethread a
      store.release.ss=st a
    """
    instance = parseInput(amdgpu.AMDGPULLVMIRTest, test_input)

    def instruction_matches(idx, opc, expected_scope):
        instr = instance.all_insts[idx]
        return (
            instr.opcode == opc
            and instr.additional_data.get("syncscope") == expected_scope
        )

    assert len(instance.all_insts) == 12
    assert instruction_matches(0, "store", "system")
    assert instruction_matches(1, "store", "system")
    assert instruction_matches(2, "store", "agent")
    assert instruction_matches(3, "store", "agent")
    assert instruction_matches(4, "store", "cluster")
    assert instruction_matches(5, "store", "cluster")
    assert instruction_matches(6, "store", "workgroup")
    assert instruction_matches(7, "store", "workgroup")
    assert instruction_matches(8, "store", "wave")
    assert instruction_matches(9, "store", "wave")
    assert instruction_matches(10, "store", "thread")
    assert instruction_matches(11, "store", "thread")


def test_ir_parse_syncscope_errors_more_than_one():
    test_input = """
      #thread 0
      store.release.ss=system.ss=agent a
    """
    with pytest.raises(core.ParseError):
        parseInput(amdgpu.AMDGPULLVMIRTest, test_input)


def test_ir_parse_syncscope_errors_unknown():
    test_input = """
      #thread 0
      store.release.ss=unknownscope a
    """
    with pytest.raises(core.ParseError):
        parseInput(amdgpu.AMDGPULLVMIRTest, test_input)


def test_ir_parse_syncscope_errors_nonatomic():
    test_input = """
      #thread 0
      store.ss=system a
    """
    with pytest.raises(core.ParseError):
        parseInput(amdgpu.AMDGPULLVMIRTest, test_input)
