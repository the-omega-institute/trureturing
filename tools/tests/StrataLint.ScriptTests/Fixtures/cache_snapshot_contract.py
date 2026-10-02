"""Actions snapshot publication, material restoration, and rollback contracts."""
import contextlib
import importlib
import io
import json
import os
import pathlib
import sys
import subprocess
import unittest
from unittest import mock

from cache_fixture import CACHE, REV, CacheFixture


class SnapshotContracts(CacheFixture, unittest.TestCase):
    def work(self, report=1, programs=0, **changes):
        path = self.root / "build/lean-cache/build-work.json"
        path.parent.mkdir(parents=True, exist_ok=True)
        value = dict(schema_version=1, run_id="17", run_attempt="2",
                     repository=str(self.root.resolve()), report=report, programs=programs)
        value.update(changes)
        path.write_text(json.dumps(value))
        self.env["STRATALINT_LEAN_BUILD_WORK_FILE"] = str(path)
        return path

    def native_seed(self, layer):
        self.work()
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
                    if key_kind == "legacy":
                        key = (key.replace("lean-project-push-", "lean-project-v4-") if layer == "project"
                               else key.replace("-v4-", "-v3-"))
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
            self.assertTrue(keys[layer]["restore_prefix"].startswith(
                "lean-project-push-" if layer == "project" else "lean-dependency-v4-"))

    def test_native_project_authorization_preserves_outputs_without_directory_reads(self):
        self.work()
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

    def test_project_zero_report_and_program_work_skips_upload(self):
        self.native_seed("project")
        self.work(0, 0)
        ready, receipts = self.snapshot_result()
        self.assertEqual("false", ready["project_ready"])
        self.assertEqual("no-build-work", receipts["project"]["reason"])

    def test_project_report_and_program_only_work_are_publishable_on_push(self):
        self.native_seed("project")
        for report, programs in ((2, 0), (0, 3)):
            with self.subTest(report=report, programs=programs):
                self.work(report, programs)
                ready, receipts = self.snapshot_result()
                self.assertEqual("true", ready["project_ready"])
                self.assertEqual(report + programs, receipts["project"]["build_work"])

    def test_project_unknown_work_never_claims_zero_or_uploads(self):
        self.native_seed("project")
        for defect in ("missing", "malformed", "stale", "negative", "bool", "unknown", "foreign-root", "duplicate-field", "archived-path", "symlink"):
            with self.subTest(defect=defect):
                path = self.work()
                if defect == "missing": path.unlink()
                elif defect == "malformed": path.write_text("[]")
                elif defect == "stale": self.work(run_attempt="1")
                elif defect == "negative": self.work(-1)
                elif defect == "bool": self.work(True)
                elif defect == "unknown": self.work(None)
                elif defect == "foreign-root": self.work(repository="/other")
                elif defect == "duplicate-field": path.write_text(path.read_text().rstrip()[:-1] + ', "report": 0}')
                elif defect == "archived-path":
                    archived = self.root / ".lake/build/work.json"
                    archived.write_bytes(path.read_bytes())
                    self.env["STRATALINT_LEAN_BUILD_WORK_FILE"] = str(archived)
                elif defect == "symlink":
                    link = path.with_suffix(".link")
                    link.symlink_to(path)
                    self.env["STRATALINT_LEAN_BUILD_WORK_FILE"] = str(link)
                ready, receipts = self.snapshot_result()
                self.assertEqual("false", ready["project_ready"])
                self.assertEqual("build-work-unknown", receipts["project"]["reason"])

    def test_pull_requests_never_publish_project_seeds_even_with_build_work(self):
        self.native_seed("project")
        self.native_seed("dependency")
        self.env.update(GITHUB_EVENT_NAME="pull_request", GITHUB_REF="refs/pull/12/merge")
        for report, programs in ((2, 0), (0, 3), (0, 0), (None, None)):
            with self.subTest(report=report, programs=programs):
                self.work(report, programs)
                ready, receipts = self.snapshot_result()
                self.assertEqual("false", ready["project_ready"])
                self.assertEqual("pull-requests-do-not-publish-project-seeds", receipts["project"]["reason"])
                self.assertEqual("true", ready["dependency_ready"])

    def test_only_dev_and_integration_pushes_publish_project_seeds(self):
        self.native_seed("project")
        for ref, expected in (("refs/heads/dev", "true"),
                ("refs/heads/integration-ci-perf-tests", "true"), ("refs/heads/topic", "false")):
            with self.subTest(ref=ref):
                self.env["GITHUB_REF"] = ref
                ready, _ = self.snapshot_result()
                self.assertEqual(expected, ready["project_ready"])

    def test_project_save_authorization_and_dependency_policy_remain_independent(self):
        self.native_seed("project")
        self.native_seed("dependency")
        self.work(0, 0)
        ready, receipts = self.snapshot_result()
        self.assertEqual("true", ready["dependency_ready"])
        self.env["STRATALINT_CACHE_WRITES"] = "false"
        ready, receipts = self.snapshot_result()
        self.assertEqual("false", ready["project_ready"])
        self.assertEqual("false", ready["dependency_ready"])
        self.assertEqual("save-disabled", receipts["project"]["status"])

    def test_project_guard_requires_report_success_and_dependency_requires_check_success(self):
        self.native_seed("project")
        self.native_seed("dependency")
        for report, checked, project, dependency in (("true", "false", "true", "false"),
                ("false", "true", "false", "true"), (None, "true", "false", "true"),
                ("true", "true", "true", "true")):
            with self.subTest(report=report, checked=checked):
                self.env["STRATALINT_CHECK_SUCCEEDED"] = checked
                self.env.pop("STRATALINT_REPORT_SUCCEEDED", None)
                if report is not None: self.env["STRATALINT_REPORT_SUCCEEDED"] = report
                ready, _ = self.snapshot_result()
                self.assertEqual(project, ready["project_ready"])
                self.assertEqual(dependency, ready["dependency_ready"])

    def test_elan_inventory_lists_installed_toolchains_without_modifying_them(self):
        home = self.root / "elan cache with spaces"
        binary = home / "bin/elan"
        binary.parent.mkdir(parents=True)
        binary.write_text("#!/bin/bash\n[[ \"$*\" == 'toolchain list' ]] || exit 23\n"
                          "[[ \"${ELAN_HOME:-}\" == \"$EXPECTED_INVENTORY_HOME\" ]] || exit 24\n"
                          "printf '%s\\n' 'leanprover/lean4:v4.33.0 (default)' 'leanprover/lean4:v4.31.0'\n")
        binary.chmod(0o755)
        toolchains = home / "toolchains/stale"
        toolchains.mkdir(parents=True)
        material = toolchains / "keep"
        material.write_bytes(b"installed toolchain")
        result = subprocess.run(["bash", "--noprofile", "--norc",
            str(CACHE.parents[1] / "workflow/elan-cache-inventory.sh"), str(home)],
            cwd=self.root, env=dict(self.env, EXPECTED_INVENTORY_HOME=str(home)), capture_output=True, text=True)
        self.assertEqual(0, result.returncode, result.stderr)
        self.assertIn("ELAN_CACHE_TOOLCHAINS", result.stdout)
        self.assertIn("leanprover/lean4:v4.33.0 (default)", result.stdout)
        self.assertIn("leanprover/lean4:v4.31.0", result.stdout)
        self.assertEqual(b"installed toolchain", material.read_bytes())

    def restore_owner(self):
        sys.path.insert(0, str(CACHE.parent))
        return importlib.import_module("lean_actions")







if __name__ == "__main__":
    unittest.main()
