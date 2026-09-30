"""Actions snapshot publication, material restoration, and rollback contracts."""
import contextlib
import importlib
import io
import os
import pathlib
import sys
import unittest
from unittest import mock

from cache_fixture import CACHE, REV, CacheFixture


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







if __name__ == "__main__":
    unittest.main()
