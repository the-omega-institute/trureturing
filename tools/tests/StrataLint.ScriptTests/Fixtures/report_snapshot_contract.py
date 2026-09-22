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

from cache_fixture import CACHE, REPO, REV, CacheFixture

SUFFIXES = ("", ".sha256", ".input.attestation", ".provenance.json", ".materials.zip")
REPORT = ".lake/build/stratalint/raw-lean-report.json"
STEPS = ("lean-report", "scribe", "filemap", "check-current")


class SnapshotContracts(CacheFixture, unittest.TestCase):
    def owner(self):
        sys.path.insert(0, str(CACHE.parent))
        return importlib.import_module("lean_actions")

    def test_report_route_uses_only_declared_complete_receipts_and_never_publishes(self):
        owner = self.owner()
        seed = self.root / "build/ci/current-check-seed"
        seed.mkdir(parents=True)
        report = "build/ci/check-material/" + "a" * 64 + "/" + "b" * 32 + "/" + "e" * 32 + "/report/raw-lean-report.json"
        declared = [report + suffix for suffix in (*SUFFIXES, ".reuse.json")]
        path = seed / report
        path.parent.mkdir(parents=True)
        for relative in declared:
            (seed / relative).write_text("producer-owned fixture material\n")
        unit = dict(report=report, materials=[dict(path=relative, sha256="a" * 64) for relative in declared])
        checks = dict(version=2, stage="current", candidate="c" * 64, round="d" * 32, units=[unit, unit])
        manifest = seed / "checks.json"
        manifest.write_text(json.dumps(checks))
        for defect in ("none", "legacy", "escape", "producer-miss"):
            with self.subTest(defect=defect):
                altered = json.loads(json.dumps(checks))
                if defect == "legacy":
                    for row in altered["units"]: row["materials"] = row["materials"][:-1]
                if defect == "escape":
                    for row in altered["units"]: row["report"] = "../outside/raw-lean-report.json"
                manifest.write_text(json.dumps(altered))
                result = subprocess.CompletedProcess([], 0, json.dumps(dict(needs_lake=defect == "producer-miss")), "")
                with mock.patch.object(owner.subprocess, "run", return_value=result) as probe:
                    selected = owner.report_seed(self.root)
                self.assertEqual(str(path) if defect == "none" else None, selected)
                self.assertEqual(1 if defect in ("none", "producer-miss") else 0, probe.call_count)
                if probe.called:
                    arguments = probe.call_args.args[0]
                    self.assertIn("probe", arguments)
                    self.assertIn(str(path), arguments)
                    self.assertNotIn("--lake", arguments)
                self.assertFalse((self.root / REPORT).exists())

    def test_report_route_missing_seed_does_not_invoke_a_producer_or_claim_success(self):
        owner = self.owner()
        with mock.patch.object(owner.subprocess, "run") as probe:
            self.assertIsNone(owner.report_seed(self.root))
        probe.assert_not_called()

    def test_report_preparation_restores_only_current_and_keeps_normal_producer_selected(self):
        owner = self.owner()
        sys.path.insert(0, str(REPO / "tools/scripts/workflow"))
        planner = importlib.import_module("ci_plan")
        for report_required, reusable in ((True, False), (True, True), (False, False)):
            with self.subTest(report_required=report_required, reusable=reusable):
                plan = {"execution": {"steps": ["lean-report"] if report_required else ["filemap"], "lean_targets": []}}
                requirements = dict(cache_layers=["current", "dependency", "project"] if report_required else ["current"],
                                    tools=["lake"] if report_required else [])
                selected = str(self.root / "build/ci/current-check-seed/report.json") if reusable else None
                with mock.patch.dict(os.environ, dict(self.env, CANDIDATE_SHA=REV,
                        CI_PLAN_PATH="build/ci/plan.json", CI_CHANGES_PATH="build/ci/changes.json")), \
                     mock.patch.object(sys, "argv", [str(CACHE), "prepare-report", "--repository", str(self.root),
                        "--stage", "current", "--current-key", "transported-seed"]), \
                     mock.patch.object(planner, "git", return_value=(REV + "\n").encode()), \
                     mock.patch.object(planner, "validate_plan", return_value=plan), \
                     mock.patch.object(planner, "stage_requirements", return_value=requirements), \
                     mock.patch.object(owner, "restore") as restore, \
                     mock.patch.object(owner, "report_seed", return_value=selected) as probe, \
                     contextlib.redirect_stdout(io.StringIO()) as result:
                    self.assertEqual(0, owner.main())
                self.assertEqual(["current"], restore.call_args.args[3])
                self.assertEqual(int(report_required), probe.call_count)
                self.assertIn("needs_lake=" + str(report_required and not reusable).lower(), result.getvalue())
                self.assertIn("STRATALINT_LEAN_REPORT_REUSE=" + (selected or ""), result.getvalue())
                self.assertEqual(["lean-report"] if report_required else ["filemap"], plan["execution"]["steps"])

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
        self.env.update(CANDIDATE_SHA=commit, GITHUB_SHA=commit, GITHUB_REPOSITORY="fixture/trureturing")
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
        expected = {p.relative_to(self.root / ".lake/build").as_posix(): p.read_bytes()
                    for p in (self.root / ".lake/build").rglob("*") if p.is_file()}
        readiness, receipts = self.snapshot_result()
        self.assertEqual({"dependency_ready": "false", "project_ready": "true"}, readiness, receipts)
        self.assertIn("lean-inspector/report.zip", expected)
        owner = self.owner()
        with mock.patch.dict(os.environ, self.env):
            spec = owner.actions_keys(self.root)["project"]
        self.assertEqual(".lake/build", spec["path"])
        self.env.update(GITHUB_EVENT_NAME="pull_request", STRATALINT_CACHE_WRITES="false")
        restored = self.run_tool(CACHE, "restore", "--layers", "project", "--project-key", spec["key"],
                                 "--project-outcome", "success")
        self.assertEqual(0, restored.returncode, restored.stdout + restored.stderr)
        self.assertIn('"status": "restored"', restored.stdout)
        self.assertEqual(expected, {p.relative_to(self.root / ".lake/build").as_posix(): p.read_bytes()
                                   for p in (self.root / ".lake/build").rglob("*") if p.is_file()})
        self.assertFalse((self.root / "build/lean-cache/project").exists())

    def test_current_handoff_accepts_native_five_members_without_directory_scans(self):
        plan, commit = self.prepare_current()
        owner = self.owner()
        material = self.root / ".lake/build/lean-inspector/report.zip"
        original_open = pathlib.Path.open
        def guarded_open(path, *args, **kwargs):
            if path == material: raise AssertionError("native directory material was read")
            return original_open(path, *args, **kwargs)
        with mock.patch.dict(os.environ, self.env, clear=True), \
                mock.patch.object(pathlib.Path, "open", guarded_open), \
                mock.patch.object(pathlib.Path, "rglob", side_effect=AssertionError("native directory scan")), \
                contextlib.redirect_stdout(io.StringIO()) as result:
            owner.snapshot(self.root, owner.actions_keys(self.root), ["project"], current=(plan, commit))
        self.assertIn("project_ready=true", result.getvalue())
        self.assertEqual(b"native aggregate\n", material.read_bytes())

    def test_current_handoff_rejects_each_missing_or_damaged_member(self):
        plan, commit = self.prepare_current()
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

    def test_snapshot_readiness_and_material_follow_writer_permissions(self):
        self.prepare_current()
        self.dependency_files()
        for event, ref, writes, success, allowed in [
                ("push", "refs/heads/dev", "true", "true", True),
                ("push", "refs/heads/integration-ci-tests", "true", "true", True),
                ("push", "refs/heads/dev", "false", "true", False),
                ("push", "refs/heads/dev", "true", "false", False),
                ("push", "refs/heads/topic", "true", "true", False),
                ("pull_request", "refs/pull/42/merge", "true", "true", True),
                ("pull_request", "refs/pull/42/merge", "false", "true", False),
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
                for layer in ("dependency", "project"):
                    self.assertFalse((self.root / "build/lean-cache" / layer / "manifest.json").exists())
                    path = self.root / (".lake/packages" if layer == "dependency" else ".lake/build")
                    self.assertTrue(path.is_dir())


if __name__ == "__main__":
    unittest.main()
