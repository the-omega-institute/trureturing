"""Native project cache and accepted current handoff behavior contracts."""
import hashlib
import importlib
import contextlib
import io
import json
import os
import pathlib
import shutil
import subprocess
import sys
import unittest
from unittest import mock

from ci_contract import CACHE, REPO, REV, CacheFixture

SUFFIXES = ("", ".sha256", ".input.attestation", ".provenance.json", ".materials.zip")
REPORT = ".lake/build/stratalint/raw-lean-report.json"
STEPS = ("lean-report", "scribe", "filemap", "check-current")


class SnapshotContracts(CacheFixture, unittest.TestCase):
    def owner(self):
        sys.path.insert(0, str(CACHE.parent))
        return importlib.import_module("lean_actions")

    def prepare_current(self):
        self.report = self.root / REPORT
        self.report.parent.mkdir(parents=True)
        # The exporter consumes a sealed producer handoff. Native producer
        # semantics are exercised by the real Lake/publication test suite.
        values = {"": b'{"modules":[]}\n', ".input.attestation": b"input binding\n",
                  ".provenance.json": b'{"mode":"cached","module_origins":[]}\n',
                  ".materials.zip": b"native material bytes\n"}
        values[".sha256"] = (hashlib.sha256(values[""]).hexdigest() + "  " + self.report.name + "\n").encode()
        for suffix, data in values.items():
            pathlib.Path(str(self.report) + suffix).write_bytes(data)
        for relative, data in {"lean-inspector/report.zip": b"native aggregate\n",
                "lean-inspector/modules/D5.A.zip": b"native module\n",
                "lean-inspector/inputs.json": b'{"registered":true}\n',
                "lean-inspector/producer/Inspector.olean": b"native inspector\n"}.items():
            path = self.root / ".lake/build" / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        (self.root / ".gitignore").write_text("*\n")
        for args in (("init", "-q"), ("add", "-f", ".gitignore", "lake-manifest.json", "lean-toolchain"),
                ("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "candidate")):
            subprocess.run(["git", "-C", str(self.root), *args], check=True, capture_output=True)
        commit = subprocess.check_output(["git", "-C", str(self.root), "rev-parse", "HEAD"], text=True).strip()
        self.env.update(CANDIDATE_SHA=commit, GITHUB_REPOSITORY="fixture/trureturing")
        self.env.pop("STRATALINT_LEAN_REPORT_PREPARATION", None)
        self.write_handoff()
        return {"execution": {"steps": list(STEPS)}}, commit

    def write_handoff(self, *, status="executed"):
        directory = self.root / "build/ci"
        directory.mkdir(parents=True, exist_ok=True)
        paths = [REPORT + suffix for suffix in SUFFIXES]
        candidate, round_id = "e" * 64, "fixture-current-round"
        (directory / "current-result.json").write_text(json.dumps({"stage": "current", "exit": 0,
            "candidate": candidate, "current_evidence": "build/ci/current.json", "report": REPORT}))
        def materials(names):
            return [{"path": name, "sha256": hashlib.sha256((self.root / name).read_bytes()).hexdigest()}
                    for name in sorted(names)]
        (directory / "current.json").write_text(json.dumps({"version": 2, "candidate": candidate,
            "round": round_id, "steps": [{"name": name, "raw_exit": 0, "exit": 0,
                "status": status if name == "lean-report" else "executed"} for name in STEPS],
            "materials": materials(paths)}))
        (directory / "current-transport.json").write_text(json.dumps({"version": 1, "stage": "current",
            "candidate": candidate, "round": round_id, "commit": self.env["CANDIDATE_SHA"],
            "run_id": int(self.env["GITHUB_RUN_ID"]), "run_attempt": int(self.env["GITHUB_RUN_ATTEMPT"]),
            "repository": self.env["GITHUB_REPOSITORY"], "materials": [dict(item,
                mode=(self.root / item["path"]).stat().st_mode & 0o777) for item in
                materials(paths + ["build/ci/current.json", "build/ci/current-result.json"])]}))

    def test_native_report_is_normal_project_material(self):
        self.prepare_current()
        readiness, receipts = self.snapshot_result()
        self.assertEqual({"dependency_ready": "false", "project_ready": "true"}, readiness, receipts)
        cache = self.root / "build/lean-cache/project"
        manifest = json.loads((cache / "manifest.json").read_text())
        expected = {p.relative_to(self.root / ".lake/build").as_posix(): p.read_bytes()
                    for p in (self.root / ".lake/build").rglob("*") if p.is_file()}
        self.assertIn("lean-inspector/report.zip", expected)
        self.assertFalse(any(path.endswith(".seed.json") for path in expected))
        self.assertEqual(expected, {p.relative_to(cache / "data").as_posix(): p.read_bytes()
                                   for p in (cache / "data").rglob("*") if p.is_file()})
        shutil.rmtree(self.root / ".lake/build")
        self.env.update(GITHUB_EVENT_NAME="pull_request_target", STRATALINT_CACHE_WRITES="false")
        restored = self.run_tool(CACHE, "restore", "--layers", "project", "--project-key", manifest["key"])
        self.assertEqual(0, restored.returncode, restored.stdout + restored.stderr)
        self.assertIn('"status": "restored"', restored.stdout)
        self.assertEqual(expected, {p.relative_to(self.root / ".lake/build").as_posix(): p.read_bytes()
                                   for p in (self.root / ".lake/build").rglob("*") if p.is_file()})
        self.assertFalse((self.root / ".lake/report-cache").exists())

    def test_current_handoff_accepts_native_five_members_without_preparation(self):
        plan, commit = self.prepare_current()
        owner = self.owner()
        with mock.patch.dict(os.environ, self.env, clear=True):
            self.assertIn(REPORT, owner.current_lean_materials(self.root, plan, commit))
            staged = self.root / "snapshot"
            staged.mkdir()
            metrics = owner.stage_snapshot(self.root, owner.actions_keys(self.root), "project", staged,
                                           current=(plan, commit))
        self.assertNotIn("save_disabled_reason", metrics)
        self.assertTrue((staged / "data/lean-inspector/report.zip").is_file())
        self.restore_current_project()
        material = self.root / ".lake/build/lean-inspector/report.zip"
        original_open, original_glob = pathlib.Path.open, pathlib.Path.rglob
        for changed in (False, True):
            with self.subTest(changed_other_material=changed):
                if changed: material.write_bytes(b"new native material after successful production\n")
                observed = {"material_reads": 0, "layer_walks": 0}

                def counted_open(path, mode="r", *args, **kwargs):
                    if path == material and mode == "rb": observed["material_reads"] += 1
                    return original_open(path, mode, *args, **kwargs)

                def counted_glob(path, *args, **kwargs):
                    if path == self.root / ".lake/build": observed["layer_walks"] += 1
                    return original_glob(path, *args, **kwargs)

                with mock.patch.dict(os.environ, self.env, clear=True), \
                        mock.patch.object(pathlib.Path, "open", counted_open), \
                        mock.patch.object(pathlib.Path, "rglob", counted_glob), \
                        contextlib.redirect_stdout(io.StringIO()) as receipts:
                    owner.snapshot(self.root, owner.actions_keys(self.root), ["project"], current=(plan, commit))
                self.assertEqual({"material_reads": 0, "layer_walks": 0}, observed)
                self.assertIn('"reason": "retained-restored-seed"', receipts.getvalue())
                self.assertNotIn('"reason": "unchanged"', receipts.getvalue())
                self.assertIn("project_ready=false", receipts.getvalue())
                self.assertFalse((self.root / "build/lean-cache/project/data").exists())

        for fault in ("no-restore", "failed-restore", "missing-attestation", "different-attestation",
                      "missing-record", "invalid-record", "stale-record", "changed-manifest"):
            with self.subTest(fallback=fault):
                self.restore_current_project(fault=fault)
                with mock.patch.dict(os.environ, self.env, clear=True), \
                        contextlib.redirect_stdout(io.StringIO()) as receipts:
                    owner.snapshot(self.root, owner.actions_keys(self.root), ["project"], current=(plan, commit))
                self.assertNotIn('"reason": "retained-restored-seed"', receipts.getvalue())
                self.assertIn('"status": "snapshot"', receipts.getvalue())
                self.assertIn("project_ready=true", receipts.getvalue())
                self.assertEqual(material.read_bytes(),
                    (self.root / "build/lean-cache/project/data/lean-inspector/report.zip").read_bytes())

    def restore_current_project(self, *, fault=None):
        cached = self.root / "build/lean-cache/project"
        shutil.rmtree(cached, ignore_errors=True)
        attestation = pathlib.Path(str(self.report) + ".input.attestation")
        current_bytes = attestation.read_bytes()
        if fault == "missing-attestation": attestation.unlink()
        elif fault == "different-attestation": attestation.write_bytes(b"older registered input\n")
        created = self.run_tool(CACHE, "snapshot", "--layers", "project")
        self.assertEqual(0, created.returncode, created.stdout + created.stderr)
        self.assertIn("project_ready=true", created.stdout)
        manifest = json.loads((cached / "manifest.json").read_text())
        if fault == "failed-restore":
            (cached / "data/lean-inspector/report.zip").write_bytes(b"corrupt seed")
        if fault != "no-restore":
            restored = self.run_tool(CACHE, "restore", "--layers", "project", "--project-key", manifest["key"])
            self.assertEqual(0, restored.returncode, restored.stdout + restored.stderr)
            self.assertIn('"status": "miss"' if fault == "failed-restore" else '"status": "restored"',
                          restored.stdout)
        if fault == "missing-record": (cached / "restored.json").unlink()
        elif fault == "invalid-record": (cached / "restored.json").write_text("invalid")
        elif fault == "stale-record":
            record = json.loads((cached / "restored.json").read_text())
            record["snapshot_key"] += "0"
            (cached / "restored.json").write_text(json.dumps(record))
        elif fault == "changed-manifest":
            manifest["key"] += "0"
            (cached / "manifest.json").write_text(json.dumps(manifest))
        # Model the accepted producer handoff after normal production, including
        # cases where its current attestation differs from the restored donor.
        attestation.write_bytes(current_bytes)
        self.write_handoff()

    def test_current_handoff_rejects_each_missing_or_damaged_member(self):
        plan, commit = self.prepare_current()
        self.restore_current_project()
        owner = self.owner()
        staged = self.root / "snapshot"
        staged.mkdir()
        for suffix in SUFFIXES:
            path = pathlib.Path(str(self.report) + suffix)
            data = path.read_bytes()
            for fault in ("missing", "corrupt"):
                with self.subTest(member=suffix, fault=fault), mock.patch.dict(os.environ, self.env, clear=True):
                    if fault == "missing": path.unlink()
                    else: path.write_bytes(b"damaged producer handoff")
                    try:
                        with self.assertRaises((ValueError, OSError, KeyError)):
                            owner.stage_snapshot(self.root, owner.actions_keys(self.root), "project", staged,
                                                 current=(plan, commit))
                    finally:
                        path.write_bytes(data)

    def test_current_handoff_rejects_wrong_execution_and_skipped_lean(self):
        plan, commit = self.prepare_current()
        self.restore_current_project()
        owner = self.owner()
        staged = self.root / "snapshot"
        staged.mkdir()

        def rejected():
            with self.assertRaises((ValueError, OSError)):
                owner.stage_snapshot(self.root, owner.actions_keys(self.root), "project", staged,
                                     current=(plan, commit))

        for key, value in {"CANDIDATE_SHA": "f" * 40, "GITHUB_RUN_ID": "99",
                           "GITHUB_RUN_ATTEMPT": "99", "GITHUB_REPOSITORY": "other/repository"}.items():
            with self.subTest(field=key), mock.patch.dict(os.environ, dict(self.env, **{key: value}), clear=True):
                rejected()
        transport = self.root / "build/ci/current-transport.json"
        original = transport.read_bytes()
        for key, value in (("candidate", "f" * 64), ("round", "different-round")):
            changed = json.loads(original)
            changed[key] = value
            transport.write_text(json.dumps(changed))
            try:
                with self.subTest(transport=key), mock.patch.dict(os.environ, self.env, clear=True): rejected()
            finally: transport.write_bytes(original)
        for status in ("reused", "skipped", "failed"):
            self.write_handoff(status=status)
            with self.subTest(status=status), mock.patch.dict(os.environ, self.env, clear=True):
                rejected()
        self.write_handoff()
        for name in ("current-result.json", "current.json", "current-transport.json"):
            path = self.root / "build/ci" / name
            original = path.read_bytes()
            path.unlink()
            try:
                with self.subTest(missing=name), mock.patch.dict(os.environ, self.env, clear=True):
                    rejected()
            finally: path.write_bytes(original)

    def test_invalid_dependency_links_disable_only_that_save_with_an_offending_path(self):
        self.prepare_current()
        source, _ = self.dependency_files()
        self.assertEqual({"dependency_ready": "true", "project_ready": "true"}, self.snapshot_result()[0])
        cached = self.root / "build/lean-cache/dependency/manifest.json"
        outside = self.root / "outside"
        outside.write_bytes(b"outside must stay private")
        link = source / "batteries/docs/bad-link"
        link.parent.mkdir()
        peer = link.with_name("cycle-peer")
        for name, target in {"escape": "../../../../outside", "absolute": str(outside), "broken": "missing",
                             "self-cycle": "bad-link", "chain-cycle": "cycle-peer", "directory": ".."}.items():
            before = cached.read_bytes()
            with self.subTest(link=name):
                link.symlink_to(target)
                if name == "chain-cycle": peer.symlink_to("bad-link")
                try:
                    readiness, receipts = self.snapshot_result()
                    self.assertEqual({"dependency_ready": "false", "project_ready": "true"}, readiness, receipts)
                    self.assertIn("batteries/docs/bad-link", receipts["dependency"]["reason"])
                    self.assertEqual(before, cached.read_bytes())
                    self.assertEqual(target, os.readlink(link))
                    self.assertEqual(b"outside must stay private", outside.read_bytes())
                finally:
                    link.unlink()
                    peer.unlink(missing_ok=True)

    def test_snapshot_readiness_and_material_follow_writer_permissions(self):
        self.prepare_current()
        self.dependency_files()
        for event, ref, writes, success, allowed in [
                ("push", "refs/heads/dev", "true", "true", True),
                ("push", "refs/heads/integration-ci-tests", "true", "true", True),
                ("push", "refs/heads/dev", "false", "true", False),
                ("push", "refs/heads/dev", "true", "false", False),
                ("push", "refs/heads/topic", "true", "true", False),
                ("pull_request_target", "refs/heads/dev", "true", "true", False),
                ("workflow_dispatch", "refs/heads/dev", "true", "true", False)]:
            with self.subTest(event=event, ref=ref, writes=writes, success=success):
                shutil.rmtree(self.root / "build/lean-cache", ignore_errors=True)
                self.env.update(GITHUB_EVENT_NAME=event, GITHUB_REF=ref, STRATALINT_CACHE_WRITES=writes,
                                STRATALINT_CHECK_SUCCEEDED=success)
                readiness, receipts = self.snapshot_result()
                self.assertEqual({layer + "_ready": str(allowed).lower() for layer in ("dependency", "project")}, readiness)
                self.assertEqual({layer: "snapshot" if allowed else "save-disabled" for layer in ("dependency", "project")},
                                 {layer: value["status"] for layer, value in receipts.items()})


if __name__ == "__main__":
    unittest.main()
