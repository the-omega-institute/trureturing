"""Compiled proof-term fixtures for the native structural reader."""

import json
import unittest

from native import build
from negative_fixtures import lean_env, name_key
from phases import write
from resources import run
from Structure.graph import analyse
from Structure.store import Store


def check_structure(repository, directory):
    # These subprocess fixtures need the canonical warm build, unlike the
    # Python-only tests discovered before cache ensure in the outer runner.
    from Structure.inspector_fixtures import StructureInspectorTests
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(StructureInspectorTests)
    if not unittest.TextTestRunner().run(suite).wasSuccessful():
        raise AssertionError("inspector dependency fixtures")
    folder = directory / "structure"
    folder.mkdir(parents=True, exist_ok=True)
    env = lean_env(repository)
    module = "LeanInformationAudit.Tests.Census.Structure.Terms"
    path = repository / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")
    manifest, raw = folder / "manifest.json", folder / "raw.jsonl"
    write(manifest, [[module, [str(path)]]])
    binary = build(repository, "structure.lean", env)
    run([str(binary), str(manifest), str(raw), "bodies"], folder, "native", cwd=repository, env=env)
    rows = [json.loads(line) for line in raw.read_text().splitlines()]
    declarations = {r["name"]: r for r in rows if "name" in r}
    prefix = "LeanInformationAudit.Tests.Census.Structure."
    named = lambda n: name_key(prefix + n)
    assert declarations[named("a")]["value"] == []
    expected = {"b": ["h"], "c": ["a"], "d": ["b", "c"], "g": ["b"]}
    for name, refs in expected.items():
        assert set(declarations[named(name)]["value"]) == {named(n) for n in refs}, name
    assert name_key("Eq.mpr") in declarations[named("suppliedEquality")]["value"]
    assert name_key("sorryAx") in declarations[named("usesSorry")]["value"]
    assert named("fixtureAxiom") in declarations[named("usesAxiom")]["value"]
    store = Store(folder / "raw.sqlite")
    try:
        store.module(module, [], "repository")
        for n in ["a", "h", "b", "c", "d", "g"]:
            row = declarations[named(n)]
            store.declaration(module, row["name"], row["kind"], row["value"], row["type"])
        keys = [(module, named(n), n) for n in "abcdg"]
        output = folder / "rows.jsonl"
        summary = analyse(store, keys, output, [], axioms={(k[1], k[2]): [] for k in keys})
        readings = {r["statement_id"]: r["readings"] for r in map(json.loads, output.read_text().splitlines())}
        assert (summary["direct_edges"], summary["folded_edges"]) == (4, 5)
        assert summary["direct_depths"] == dict(zip("abcdg", [0, 0, 1, 2, 1]))
        for n, depth, descendants in zip("abcdg", [0, 1, 1, 2, 2], [4, 2, 1, 0, 0]):
            assert readings[n]["frozen_dag_depth"] == depth
            assert readings[n]["descendant_subgraph_size"] == descendants
    finally:
        store.close()
    result = {"case": "native_proof_terms_and_exact_panel_graph", "status": "passed",
              "direct_edges": 4, "folded_edges": 5,
              "direct_depths": dict(zip("abcdg", [0, 0, 1, 2, 1])),
              "folded_depths": dict(zip("abcdg", [0, 1, 1, 2, 2])),
              "descendants": dict(zip("abcdg", [4, 2, 1, 0, 0]))}
    write(folder / "receipt.json", result)
    return result
