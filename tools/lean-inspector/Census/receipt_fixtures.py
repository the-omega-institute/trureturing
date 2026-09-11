"""Receipt negatives reach the replay comparator after successful Lean reads."""

import copy
import json
import shutil

from phases import read, write
from resources import run
from streaming import hash_inputs, replay
from negative_fixtures import PREFIX, key, lean, lean_env


def check_receipts(repository, directory):
    folder = directory / "receipt-byte"
    folder.mkdir(parents=True, exist_ok=True)
    module = PREFIX + "StreamingTarget"
    original = repository / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")
    target_olean = folder / "Target.olean"
    shutil.copyfile(original, target_olean)
    target = key("StreamingTarget", "StreamingTarget.target")
    write(folder / "manifest.json", [[module, [str(target_olean)]]])
    write(folder / "request.json", {"keys": [target], "roots": [["Fixture.Root", [module]]],
        "assignment": {module: "Fixture.Root"}, "discovery_roots": [module],
        "external_graph": read(directory / "external.json")})
    env = lean_env(repository)
    completed_scans = 0
    def scan():
        nonlocal completed_scans
        lean(repository, folder, "scan.lean", [folder / "manifest.json", folder / "request.json",
             folder / "index.jsonl"], "reread", env)
        lean(repository, folder, "membership.lean", [folder / "index.jsonl", folder / "request.json",
             folder / "membership.json"], "recompute", env)
        membership = read(folder / "membership.json")
        assert not membership["errors"], "receiptFixtureLoadableInput"
        rows = [json.loads(line) for line in (folder / "membership.json.rows.jsonl").open()]
        completed_scans += 1
        return {"membership": membership, "rows": rows,
                "oleans": hash_inputs([(module, "base", str(target_olean))])}
    expected = scan()
    write(folder / "receipt.json", expected)
    assert replay(scan, expected) == "match", "streamReceiptReplayPositive"

    def rejected(expected, name):
        before = completed_scans
        try:
            replay(scan, expected)
        except ValueError as error:
            assert str(error) == "IE-C044 receipt replay mismatch", "streamReceiptReplayMismatch"
        else:
            raise AssertionError("streamReceiptReplayMismatch: comparison accepted " + name)
        assert completed_scans == before + 1, "streamReceiptReplayMismatch: scan did not complete"
        return {"name": name, "status": "passed", "check": "streamReceiptReplayMismatch",
                "reread": True, "fresh_index_required": True, "comparison_reached": True}

    # Replace the input with a different kernel-checked, fully loadable olean.
    source = folder / "Changed.lean"
    source.write_text("namespace " + module + "\ntheorem target : 2 + 4 = 6 := by rfl\nend " + module + "\n")
    run([shutil.which("lean", path=env["PATH"]), "-R", str(folder), "-o", str(target_olean), str(source)], folder,
        "loadable-change", cwd=repository, env=env, budget_gb=None)
    assert target_olean.read_bytes() != original.read_bytes(), "receiptFixtureChangedInput"
    changed = rejected(expected, "receipt_replay_changed_olean")
    shutil.copyfile(original, target_olean)

    altered_receipt = copy.deepcopy(expected)
    altered_receipt["oleans"][0][3] = "sha256:" + "0" * 64
    receipt_control = rejected(altered_receipt, "altered-receipt")
    altered_row = copy.deepcopy(expected)
    altered_row["rows"][0]["payload"]["query_completed"] = False
    row_control = rejected(altered_row, "altered-row")
    invented = copy.deepcopy(expected)
    root_name = "Fixture.Invented"
    root_wire = ["str", ["str", ["anonymous"], "Fixture"], "Invented"]
    owner_wire = invented["rows"][0]["payload"]["owning_module"]
    invented["membership"]["module_names"] = [module, root_name]
    invented["membership"]["scopes"] = [[root_name, [0, 1]]]
    invented["membership"]["assignment"] = {module: root_name}
    invented["rows"][0]["payload"].update(root=root_wire, query_completed=True,
        import_scope={"modules": [owner_wire, root_wire], "completed": True})
    invented_control = rejected(invented, "invented-consistent-scope-and-completion")
    changed["controls"] = [receipt_control, row_control, invented_control]
    write(folder / "result.json", changed)
    return [changed]
