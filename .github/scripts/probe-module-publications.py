"""Transfer unfinished compiler work to a clean runner and finish the same release."""
import json
import shutil
import subprocess
import sys
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path.cwd() / "tools/scripts/worktree"))
import lean_module_cache as cache
import lean_module_dag as dag
from lean_artifact_inventory import Module, PROJECT_BUILD
from test_lean_module_cache import ModuleReleases

phase, shared = sys.argv[1], Path(sys.argv[2]).resolve()
shared.mkdir(parents=True, exist_ok=True)
fixture = ModuleReleases()
checkout = cache.compiler.checkout

def git(root, *args):
    return subprocess.check_output(["git", *args], cwd=root, text=True).strip()

def save_state(plan):
    (shared / "plan.json").write_text(json.dumps(plan))
    (shared / "rows.json").write_text(json.dumps(fixture.remote.rows))
    for (version, name), data in fixture.remote.assets.items():
        folder = shared / version
        folder.mkdir(exist_ok=True)
        (folder / name).write_bytes(data)

def produce():
    root = fixture.root
    (root / "D5/B.lean").write_text("import D5.A\ndef valueB := valueA+2\n")
    (root / "D5/D.lean").write_text("import D5.B\nimport D5.C\ndef valueD := valueB+valueC\n")
    fixture.modules["D5.D"] = Module("trureturing", Path("D5/D.lean"), Path("."))
    git(root, "init", "--quiet")
    git(root, "add", "D5", "Other", "lakefile.toml", "lake-manifest.json", "lean-toolchain")
    git(root, "-c", "user.name=Compiler fixture", "-c", "user.email=fixture@example.invalid",
        "commit", "-qm", "Build a diamond-shaped Lake project")
    fixture.source = checkout(root)
    git(root, "bundle", "create", str(shared / "source.bundle"), "HEAD")
    plan = fixture.dag_plan(workers=2)
    units = plan["compiler_dag"]["units"]
    fixture.remote.fail, = [k for k,row in units.items() if row["members"] == ["D5.D"]]
    try:
        cache.work(root, plan, 0, fixture.remote, root / "receipts")
    except InterruptedError as failure:
        assert failure.args == (fixture.remote.fail,)
    else:
        raise AssertionError("expected the final unit upload to be interrupted")
    assert sorted(n for row in fixture.remote.rows.values() for n in row["members"]) == ["D5.A","D5.B","D5.C"]
    save_state(plan)
    print(f"source={fixture.source} verified_checkpoints=3")

def consume():
    root = fixture.root
    shutil.rmtree(root)
    git(shared, "clone", "--quiet", "--no-checkout", str(shared / "source.bundle"), str(root))
    plan = json.loads((shared / "plan.json").read_bytes())
    git(root, "checkout", "--quiet", "--detach", plan["source"])
    assert checkout(root) == plan["source"] and not (root / PROJECT_BUILD).exists()
    fixture.source = plan["source"]
    fixture.remote.rows = json.loads((shared / "rows.json").read_bytes())
    for row in fixture.remote.rows.values():
        addr = row["version"], row["asset"]
        fixture.remote.assets[addr] = (shared / addr[0] / addr[1]).read_bytes()
    def rescan(*unused, **kwargs):
        raise AssertionError("worker attempted to re-analyze the graph")
    with patch.object(cache, "checkout_targets", side_effect=rescan), patch.object(dag, "TopologicalSorter", side_effect=rescan):
        lane, = [i for i, rows in enumerate(plan["lanes"]) if "D5" in rows]
        result = cache.work(root, plan, lane, fixture.remote, root / "receipts")
    assert result["compiled_modules"] == 1 and fixture.compiled == [["D5.D"]]
    index = cache.finish(plan, fixture.remote)
    fixture.modules["D5.D"] = Module("trureturing", Path("D5/D.lean"), Path("."))
    restored = cache.restore(root, index, ["D5.D"], fixture.remote, root / "restored", kind="compiler")
    assert restored["restored"] == 4 and len(index["shards"]) == 1
    print("fresh_runner_reused=3 compiled=1 restored_from_final_index=4")

try:
    fixture.setUp()
    {"produce": produce, "consume": consume}[phase]()
finally:
    fixture.doCleanups()
