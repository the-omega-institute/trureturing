"""Actions snapshot publication, material restoration, and rollback contracts."""
import builtins
import contextlib
import hashlib
import importlib
import io
import json
import os
import pathlib
import shutil
import signal
import subprocess
import sys
import unittest
from unittest import mock

from cache_fixture import CACHE, REPO, REV, CacheFixture


class SnapshotContracts(CacheFixture, unittest.TestCase):
    def native_seed(self, layer):
        owner = self.restore_owner()
        owner.dependency_restored_record(self.root).unlink(missing_ok=True)
        with mock.patch.dict(os.environ, self.env):
            keys = owner.actions_keys(self.root)
            target = self.root / keys[layer]["path"]
            target.mkdir(parents=True, exist_ok=True)
            (target / "module.olean").write_bytes(b"native build material")
            with contextlib.redirect_stdout(io.StringIO()) as result:
                owner.snapshot(self.root, keys, [layer])
            self.assertIn(layer + "_ready=true", result.getvalue())
        return owner, keys, target

    def test_native_restore_requires_success_and_the_selected_partition(self):
        for layer in ("dependency", "project"):
            for outcome, key_kind, accepted in (("success", "matching", True),
                    ("failure", "matching", False), ("cancelled", "matching", False),
                    ("success", "foreign", False), ("success", "legacy", False)):
                with self.subTest(layer=layer, outcome=outcome, key=key_kind):
                    owner, keys, target = self.native_seed(layer)
                    key = keys[layer]["key"]
                    if key_kind == "foreign": key = key.replace(REV, "b" * 40)
                    if key_kind == "legacy": key = key.replace("-v4-", "-v3-")
                    sibling = self.root / ".lake" / ("build" if layer == "dependency" else "packages")
                    sibling.mkdir(exist_ok=True)
                    (sibling / "keep").write_bytes(b"other accepted material")
                    with mock.patch.dict(os.environ, self.env), contextlib.redirect_stdout(io.StringIO()) as result:
                        owner.restore(self.root, keys, {layer: key}, [layer], outcomes={layer: outcome})
                    self.assertIn('"status": "restored"' if accepted else '"status": "miss"', result.getvalue())
                    self.assertEqual(accepted, target.exists())
                    self.assertEqual(b"other accepted material", (sibling / "keep").read_bytes())
                    if layer == "project":
                        self.assertIn("STRATALINT_ACTIONS_CACHE_SEEDED=" + str(int(accepted)), result.getvalue())

    def test_unexecuted_action_preserves_current_evidence_and_cannot_claim_a_seed(self):
        owner, keys, target = self.native_seed("project")
        for outcome, key in (("skipped", keys["project"]["key"]), ("", keys["project"]["key"])):
            with self.subTest(outcome=outcome), mock.patch.dict(os.environ, self.env), \
                    contextlib.redirect_stdout(io.StringIO()) as result:
                owner.restore(self.root, keys, {"project": key}, ["project"], outcomes={"project": outcome})
            self.assertIn("STRATALINT_ACTIONS_CACHE_SEEDED=0", result.getvalue())
            self.assertEqual(b"native build material", (target / "module.olean").read_bytes())

    def test_success_without_a_matched_key_discards_partial_action_extraction(self):
        owner, keys, target = self.native_seed("project")
        with mock.patch.dict(os.environ, self.env), contextlib.redirect_stdout(io.StringIO()) as result:
            owner.restore(self.root, keys, {"project": ""}, ["project"], outcomes={"project": "success"})
        self.assertIn("STRATALINT_ACTIONS_CACHE_SEEDED=0", result.getvalue())
        self.assertFalse(target.exists())

    def test_success_without_restored_directory_is_a_miss(self):
        owner = self.restore_owner()
        with mock.patch.dict(os.environ, self.env), contextlib.redirect_stdout(io.StringIO()) as result:
            keys = owner.actions_keys(self.root)
            owner.restore(self.root, keys, {"project": keys["project"]["key"]}, ["project"],
                          outcomes={"project": "success"})
        self.assertIn("STRATALINT_ACTIONS_CACHE_SEEDED=0", result.getvalue())

    def test_dependency_retention_uses_only_registered_small_inputs_after_successful_restore(self):
        owner, keys, target = self.native_seed("dependency")
        original_key = keys["dependency"]["key"]
        with mock.patch.dict(os.environ, self.env), contextlib.redirect_stdout(io.StringIO()):
            owner.restore(self.root, keys, {"dependency": original_key}, ["dependency"],
                          outcomes={"dependency": "success"})
        (self.root / "unrelated.lean").write_text("theorem changed := True.intro\n")
        with mock.patch.dict(os.environ, self.env), \
                mock.patch.object(pathlib.Path, "rglob", side_effect=AssertionError("native directory scan")), \
                contextlib.redirect_stdout(io.StringIO()) as result:
            owner.snapshot(self.root, keys, ["dependency"])
        self.assertIn("retained-restored-dependency", result.getvalue())
        self.assertIn("dependency_ready=false", result.getvalue())
        for file in ("lake-manifest.json", "lean-toolchain", "lakefile.toml"):
            path = self.root / file
            before = path.read_bytes()
            path.write_bytes(before + b"\n")
            with self.subTest(file=file), mock.patch.dict(os.environ, self.env), \
                    contextlib.redirect_stdout(io.StringIO()) as result:
                self.assertEqual(original_key, owner.actions_keys(self.root)["dependency"]["key"])
                owner.snapshot(self.root, keys, ["dependency"])
            self.assertIn("dependency_ready=true", result.getvalue())
            path.write_bytes(before)
        with mock.patch.dict(os.environ, dict(self.env, LEAN_OPTS="-DmaxRecDepth=1024")), \
                contextlib.redirect_stdout(io.StringIO()) as result:
            owner.snapshot(self.root, keys, ["dependency"])
        self.assertIn("dependency_ready=true", result.getvalue())

    def test_dependency_retention_requires_this_round_and_an_accepted_small_receipt(self):
        owner, keys, target = self.native_seed("dependency")
        marker = target / ".stratalint-actions-inputs.json"
        original = marker.read_bytes()
        for defect in ("missing", "invalid", "wrong-type", "stale-round"):
            with self.subTest(defect=defect), mock.patch.dict(os.environ, self.env):
                marker.write_bytes(original)
                if defect == "missing": marker.unlink()
                elif defect == "invalid": marker.write_text("broken")
                elif defect == "wrong-type": marker.write_text("[]")
                with contextlib.redirect_stdout(io.StringIO()) as restored:
                    owner.restore(self.root, keys, {"dependency": keys["dependency"]["key"]}, ["dependency"],
                                  outcomes={"dependency": "success"})
                self.assertIn('"status": "restored"', restored.getvalue())
                if defect == "stale-round":
                    changed = dict(keys, dependency=dict(keys["dependency"], key=keys["dependency"]["key"] + "0"))
                else: changed = keys
                with contextlib.redirect_stdout(io.StringIO()) as saved:
                    owner.snapshot(self.root, changed, ["dependency"])
                self.assertIn("dependency_ready=true", saved.getvalue())

    def test_project_updates_after_each_successful_production_even_with_an_unchanged_report(self):
        owner, keys, target = self.native_seed("project")
        with mock.patch.dict(os.environ, self.env), contextlib.redirect_stdout(io.StringIO()):
            owner.restore(self.root, keys, {"project": keys["project"]["key"]}, ["project"],
                          outcomes={"project": "success"})
        (target / "new.olean").write_bytes(b"newly compiled module")
        with mock.patch.dict(os.environ, self.env), contextlib.redirect_stdout(io.StringIO()) as saved:
            owner.snapshot(self.root, keys, ["project"])
        self.assertIn("project_ready=true", saved.getvalue())
        self.assertEqual(b"newly compiled module", (target / "new.olean").read_bytes())

    def test_bounded_snapshot_authorizes_only_inside_the_remaining_save_window(self):
        owner, keys, target = self.native_seed("project")
        from cache_deadline import CacheDeadline
        for cutoff in (None, 100, 164, 400):
            with self.subTest(cutoff=cutoff), mock.patch.dict(os.environ, self.env), \
                    contextlib.redirect_stdout(io.StringIO()) as result:
                owner.snapshot(self.root, keys, ["project"], deadline=CacheDeadline(cutoff,
                    reason="unavailable" if cutoff is None else "available", monotonic=lambda: 100))
            self.assertIn("project_ready=" + str(cutoff == 400).lower(), result.getvalue())
            self.assertEqual(b"native build material", (target / "module.olean").read_bytes())
        self.assertEqual([], list((self.root / "build").glob(".snapshot-*")))

    def test_native_metadata_save_failure_keeps_produced_material(self):
        owner, keys, target = self.native_seed("dependency")
        with mock.patch.dict(os.environ, self.env), \
                mock.patch.object(owner, "write_small_record", side_effect=OSError("save unavailable")), \
                contextlib.redirect_stdout(io.StringIO()) as result:
            owner.snapshot(self.root, keys, ["dependency"])
        self.assertIn("dependency_ready=false", result.getvalue())
        self.assertEqual(b"native build material", (target / "module.olean").read_bytes())

    def test_native_actions_paths_are_the_registered_build_directories(self):
        owner = self.restore_owner()
        with mock.patch.dict(os.environ, self.env):
            keys = owner.actions_keys(self.root)
        for layer, path in (("dependency", ".lake/packages"), ("project", ".lake/build")):
            self.assertEqual(path, keys[layer]["path"])
            self.assertIn("-v4-", keys[layer]["restore_prefix"])

    def test_native_project_authorization_preserves_outputs_without_directory_reads(self):
        owner = self.restore_owner()
        source = self.root / ".lake/build/lib/Module.olean"
        source.parent.mkdir(parents=True)
        source.write_bytes(b"new successful build")
        before = source.stat().st_ino
        with mock.patch.dict(os.environ, self.env), \
                mock.patch.object(pathlib.Path, "rglob", side_effect=AssertionError("native cache directory scan")), \
                contextlib.redirect_stdout(io.StringIO()) as receipts:
            owner.snapshot(self.root, owner.actions_keys(self.root), ["project"])
        self.assertIn("project_ready=true", receipts.getvalue())
        self.assertEqual(before, source.stat().st_ino)
        self.assertEqual(b"new successful build", source.read_bytes())
        self.assertFalse((self.root / "build/lean-cache/project/data").exists())

    def restore_owner(self):
        sys.path.insert(0, str(CACHE.parent))
        return importlib.import_module("lean_actions")

    def test_staged_restore_subset_cannot_expand_the_registered_cache_layers(self):
        owner = self.restore_owner()
        sys.path.insert(0, str(REPO / "tools/scripts/workflow"))
        plan = importlib.import_module("ci_plan")
        for layers, accepted in ((["dependency", "project"], True), (["current"], False), (["project", "project"], False)):
            with self.subTest(layers=layers):
                with mock.patch.dict(os.environ, dict(self.env, CANDIDATE_SHA=REV,
                        CI_PLAN_PATH="build/ci/plan.json", CI_CHANGES_PATH="build/ci/changes.json")), \
                     mock.patch.object(sys, "argv", [str(CACHE), "restore", "--repository", str(self.root),
                        "--stage", "current", "--layers", *layers]), \
                     mock.patch.object(plan, "git", return_value=(REV + "\n").encode()), \
                     mock.patch.object(plan, "validate_plan", return_value={}), \
                     mock.patch.object(plan, "stage_requirements", return_value={"cache_layers": ["dependency", "project"]}), \
                     mock.patch.object(owner, "restore") as restore, \
                     contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                    self.assertEqual(0 if accepted else 2, owner.main())
                self.assertEqual(int(accepted), restore.call_count)
                if accepted: self.assertEqual(layers, restore.call_args.args[3])

    def test_layer_filter_cannot_expand_registered_stage_scope(self):
        owner = self.restore_owner()
        sys.path.insert(0, str(REPO / "tools/scripts/workflow"))
        plan = importlib.import_module("ci_plan")
        for selected in (False, True):
            with self.subTest(selected=selected):
                argv = [str(CACHE), "snapshot", "--repository", str(self.root),
                        "--stage", "current", "--layer", "current", "--bounded-cache"]
                with mock.patch.dict(os.environ, dict(self.env, CANDIDATE_SHA=REV,
                        CI_PLAN_PATH="build/ci/plan.json", CI_CHANGES_PATH="build/ci/changes.json")), \
                     mock.patch.object(sys, "argv", argv), \
                     mock.patch.object(plan, "git", return_value=(REV + "\n").encode()), \
                     mock.patch.object(plan, "validate_plan", return_value={}), \
                     mock.patch.object(plan, "stage_requirements", return_value={
                         "cache_layers": ["current", "project"] if selected else ["project"]}), \
                     mock.patch.object(owner, "actions_keys", wraps=owner.actions_keys) as keys, \
                     mock.patch.object(owner, "snapshot", wraps=owner.snapshot) as snapshot, \
                     contextlib.redirect_stdout(io.StringIO()) as receipts:
                    self.assertEqual(0, owner.main())
                self.assertIn("current_ready=false", receipts.getvalue())
                self.assertIn("save_timeout_minutes=1", receipts.getvalue())
                if selected:
                    self.assertEqual(["current"], snapshot.call_args.args[2])
                    self.assertEqual(1, keys.call_count)
                else:
                    snapshot.assert_not_called()
                    keys.assert_not_called()
                self.assertFalse((self.root / "build/lean-cache").exists())

    def test_bounded_snapshot_cleans_descendants_after_worker_exits(self):
        owner = self.restore_owner()
        from cache_deadline import CacheDeadline
        hooks = self.root / "hooks"
        hooks.mkdir()
        channel = self.root / "descendant-ready"
        os.mkfifo(channel)
        (hooks / "sitecustomize.py").write_text('''
import os, pathlib, subprocess, sys
if pathlib.Path(sys.argv[0]).name == "lean_actions.py":
    subprocess.Popen([sys.executable, "-c", "import signal,sys; channel=open(sys.argv[1], 'wb', buffering=0); channel.write(b'x'); signal.pause()", os.environ["DESCENDANT_CHANNEL"]])
    os._exit(7)
''')
        launch = subprocess.Popen
        streams = []

        def exited_worker(command, **kwargs):
            process = launch(command, **kwargs)
            stream = channel.open("rb", buffering=0)
            streams.append(stream)
            self.assertEqual(b"x", stream.read(1))
            # The actual worker is gone; its descendant still holds the pipe.
            self.assertEqual(7, process.wait())
            return process

        with mock.patch.dict(os.environ, dict(self.env, PYTHONPATH=str(hooks), DESCENDANT_CHANNEL=str(channel))), \
             mock.patch.object(owner.subprocess, "Popen", side_effect=exited_worker), \
             contextlib.redirect_stdout(io.StringIO()) as receipts:
            owner.snapshot(self.root, owner.actions_keys(self.root), ["project"],
                           deadline=CacheDeadline(400, monotonic=lambda: 100))
        self.assertIn("project_ready=false", receipts.getvalue())
        for stream in streams:
            # EOF proves the surviving descendant was also killed. The native
            # test runner's hang guard handles a regression without timing the verdict.
            self.assertEqual(b"", stream.read())
            stream.close()

    def test_execution_snapshot_consumes_the_exporters_inventory(self):
        owner = self.restore_owner()
        for layer in ("engineering", "current"):
            with self.subTest(layer=layer):
                payload = b"already inventoried native transport material"
                inventory = [{"path": "material", "sha256": hashlib.sha256(payload).hexdigest(), "mode": 0o640}]

                def exported(root, selected, keys, destination):
                    self.assertEqual(layer, selected)
                    destination.mkdir()
                    (destination / "material").write_bytes(payload)
                    (destination / "material").chmod(0o640)
                    return inventory

                with mock.patch.dict(os.environ, self.env), \
                     mock.patch.object(owner, "snapshot_execution", side_effect=exported), \
                     mock.patch.object(owner, "files", side_effect=AssertionError("export material was read twice")), \
                     contextlib.redirect_stdout(io.StringIO()) as receipts:
                    owner.snapshot(self.root, owner.actions_keys(self.root), [layer])
                self.assertIn('"status": "snapshot"', receipts.getvalue())
                cached = self.root / "build/lean-cache" / layer
                self.assertEqual(inventory, json.loads((cached / "manifest.json").read_text())["files"])
                self.assertEqual(payload, (cached / "data/material").read_bytes())

    def test_judge_restore_rejects_late_changes_without_replacing_target(self):
        owner = self.restore_owner()
        with mock.patch.dict(os.environ, self.env):
            keys = owner.actions_keys(self.root)
        spec = keys["judge"]
        cached = self.root / spec["path"]
        target = self.root / spec["target"]
        target.mkdir()
        (target / "current-only").write_bytes(b"accepted candidate material")
        inventory = []
        for relative, data in (("a.dll", b"first material"), ("nested/z.dll", b"last material")):
            path = cached / "data" / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
            path.chmod(0o640)
            inventory.append({"path": relative, "sha256": hashlib.sha256(data).hexdigest(), "mode": 0o640})
        (cached / "manifest.json").write_text(json.dumps({"schema": "lean-actions-seed-v1",
            "partition": keys["partition"], "layer": "judge", "key": spec["key"], "files": inventory}))
        copy_metadata = shutil.copystat

        def change_next_source(source, destination, **kwargs):
            copy_metadata(source, destination, **kwargs)
            if pathlib.Path(source) == cached / "data/a.dll":
                (cached / "data/nested/z.dll").write_bytes(b"changed during staging")

        with mock.patch.dict(os.environ, self.env), \
             mock.patch.object(shutil, "copystat", side_effect=change_next_source), \
             contextlib.redirect_stdout(io.StringIO()) as receipts:
            owner.restore(self.root, keys, {"judge": spec["key"]}, ["judge"], registry={})
        self.assertIn('"status": "miss"', receipts.getvalue())
        self.assertIn("cache material integrity mismatch: nested/z.dll", receipts.getvalue())
        self.assertEqual(["current-only"], sorted(path.name for path in target.iterdir()))
        self.assertEqual(b"accepted candidate material", (target / "current-only").read_bytes())
        self.assertFalse(list(target.parent.glob(".actions-*")))


if __name__ == "__main__":
    unittest.main()
