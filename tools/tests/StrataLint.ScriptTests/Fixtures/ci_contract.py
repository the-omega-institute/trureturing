"""Executable resolver and optional Actions seed contracts, with isolated Git/data."""
import hashlib
import json
import importlib
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

REPO = pathlib.Path(__file__).resolve().parents[4]
CI = REPO / "tools/scripts/workflow/ci.py"
CACHE = REPO / "tools/scripts/worktree/lean_actions.py"
REV = "a" * 40


class LegacyCallerTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="legacy-caller-")
        self.addCleanup(self.temp.cleanup)
        self.root = pathlib.Path(self.temp.name).resolve()
        self.bin = self.root / "bin"
        self.bin.mkdir()
        self.gate = REPO / ".github/scripts/harness-gate.sh"
        self.report = self.root / "report.json"
        self.report.write_text("{}")
        self.env = dict(os.environ, PATH=str(self.bin) + os.pathsep + os.environ["PATH"],
                        CALLS=str(self.root / "calls"))
        (self.bin / "make").write_text('#!/bin/sh\nprintf "make %s\\n" "$*" >> "$CALLS"\nexit "${BUILD_EXIT:-0}"\n')
        (self.bin / "dotnet").write_text('''#!/bin/sh
printf 'dotnet %s\\n' "$*" >> "$CALLS"
case "$2" in
  check) exit "${CHECK_EXIT:-0}" ;;
  filemap-conform) exit "${FILEMAP_EXIT:-0}" ;;
  *) exit 86 ;;
esac
''')
        for path in self.bin.iterdir():
            path.chmod(0o755)

    def gate_run(self, **env):
        self.assertTrue(self.gate.is_file(), str(self.gate))
        self.assertTrue(os.access(self.gate, os.X_OK), str(self.gate))
        return subprocess.run([str(self.gate), "--candidate", str(self.root), "--base", "a" * 40,
            "--candidate-lean-report", str(self.report),
            "--judge-dll", str(self.root / "optional-cache/StrataLint.dll")],
            capture_output=True, text=True, env=dict(self.env, **env))

    def test_gate_preserves_checks_and_annotation_with_candidate_runtime(self):
        for check_exit, filemap_exit, expected in [(0, 0, 0), (3, 0, 3), (1, 0, 1),
                                                  (2, 0, 2), (19, 0, 19), (0, 1, 1), (3, 2, 2)]:
            with self.subTest(check_exit=check_exit, filemap_exit=filemap_exit):
                result = self.gate_run(CHECK_EXIT=str(check_exit), FILEMAP_EXIT=str(filemap_exit))
                self.assertEqual(expected, result.returncode, result.stdout + result.stderr)
                calls = (self.root / "calls").read_text().splitlines()[-3:]
                dll = self.root / "tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll"
                self.assertEqual("make -C " + str(self.root / "tools") + " dotnet", calls[0])
                self.assertEqual(f"dotnet {dll} check --protected-base {'a' * 40} --candidate-lean-report {self.report}", calls[1])
                self.assertEqual(f"dotnet {dll} filemap-conform", calls[2])

    def test_gate_build_failure_stops_before_checks(self):
        result = self.gate_run(BUILD_EXIT="17")
        self.assertEqual(17, result.returncode, result.stdout + result.stderr)
        self.assertEqual(1, len((self.root / "calls").read_text().splitlines()))

    def test_judge_address_uses_real_pinned_runtime_and_source(self):
        script = REPO / "tools/scripts/workflow/judge-content-address.sh"
        first = subprocess.run(["bash", str(script), "a" * 64], cwd=REPO, capture_output=True, text=True)
        self.assertEqual(0, first.returncode, first.stderr)
        values = dict(line.split("=", 1) for line in first.stdout.splitlines())
        self.assertRegex(values["address"], r"^[0-9a-f]{64}$")
        self.assertTrue(values["runtime"])
        repeated = subprocess.run(["bash", str(script), "a" * 64], cwd=REPO, capture_output=True, text=True)
        self.assertEqual(first.stdout, repeated.stdout)
        changed = subprocess.run(["bash", str(script), "b" * 64], cwd=REPO, capture_output=True, text=True)
        self.assertEqual(0, changed.returncode, changed.stderr)
        self.assertNotEqual(first.stdout, changed.stdout)
        invalid = subprocess.run(["bash", str(script), "HEAD"], cwd=REPO, capture_output=True, text=True)
        self.assertEqual(2, invalid.returncode)
        self.assertEqual("", invalid.stdout)


class CacheFixture:
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="ci-contract-")
        self.root = pathlib.Path(self.temp.name)
        self.env = dict(os.environ, GITHUB_RUN_ID="17", GITHUB_RUN_ATTEMPT="2",
                        GITHUB_EVENT_NAME="push", GITHUB_REF="refs/heads/dev",
                        STRATALINT_CHECK_SUCCEEDED="true", STRATALINT_CACHE_WRITES="true",
                        HOME=str(self.root),
                        GITHUB_OUTPUT=str(self.root / "outputs"), GITHUB_ENV=str(self.root / "environment"))
        (self.root / "lake-manifest.json").write_text(json.dumps({"packages": [{"name": "mathlib", "rev": REV}]}))
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.33.0\n")

    def tearDown(self):
        self.temp.cleanup()

    def run_tool(self, script, *args, env=None):
        return subprocess.run([sys.executable, str(script), *args, "--repository", str(self.root)],
                              env=env or self.env, capture_output=True, text=True)

    def snapshot_result(self):
        (self.root / "outputs").unlink(missing_ok=True)
        result = self.run_tool(CACHE, "snapshot")
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        readiness = dict(line.split("=", 1) for line in (self.root / "outputs").read_text().splitlines())
        receipts = {entry["layer"]: entry for entry in (
            json.loads(line.removeprefix("LEAN_ACTIONS_CACHE "))
            for line in result.stdout.splitlines() if line.startswith("LEAN_ACTIONS_CACHE "))}
        return readiness, receipts

    def dependency_files(self):
        source = self.root / ".lake/packages"
        material = {
            "mathlib/scripts/bench/size/run": (b"#!/bin/sh\nprintf 'size\\n'\n", 0o755),
            "mathlib/scripts/bench/build/fake-root/bin/lean": (b"#!/bin/sh\nexit 0\n", 0o755),
            "batteries/README.md": (b"# Batteries\n\x00private bytes\xff\n", 0o640),
        }
        for relative, (data, mode) in material.items():
            path = source / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
            path.chmod(mode)
        return source, material


class Contracts(CacheFixture, unittest.TestCase):
    def git(self, *args):
        return subprocess.run(["git", "-C", str(self.root), *args], check=True,
                              capture_output=True, text=True).stdout.strip()

    def commit(self, message):
        self.git("add", "lake-manifest.json")
        self.git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", message)
        return self.git("rev-parse", "HEAD")

    def test_resolver_fixes_merge_and_first_parent_before_merge_ref_moves(self):
        self.git("init", "-q")
        base = self.commit("base")
        self.git("checkout", "-qb", "topic")
        (self.root / "lake-manifest.json").write_text("{}")
        head = self.commit("head")
        merge = self.git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                         "commit-tree", "HEAD^{tree}", "-p", base, "-p", head, "-m", "merge")
        self.git("checkout", "--detach", merge)
        result = self.run_tool(CI, "resolve", "--head", head,
                               env=dict(self.env, CI_WORKFLOW_CANDIDATE_SHA=merge,
                                        GITHUB_EVENT_NAME="pull_request_target"))
        self.assertEqual(0, result.returncode, result.stderr)
        outputs = dict(line.split("=", 1) for line in (self.root / "outputs").read_text().splitlines())
        self.assertEqual(merge, outputs["candidate_sha"])
        self.assertEqual(base, outputs["base_sha"])
        self.git("update-ref", "refs/pull/1/merge", head)
        result = self.run_tool(CI, "checkout", "--commit", outputs["candidate_sha"])
        self.assertEqual(0, result.returncode, result.stderr)
        self.assertEqual(merge, self.git("rev-parse", "HEAD"))

    def test_parentless_checkout_needs_no_base_or_remote(self):
        self.git("init", "-q")
        commit = self.commit("parentless")
        result = self.run_tool(CI, "checkout", "--commit", commit)
        self.assertEqual(0, result.returncode, result.stderr)
        self.assertNotEqual(0, self.run_tool(CI, "resolve", "--head", commit).returncode)
        self.assertNotEqual(0, self.run_tool(CI, "checkout", "--commit", "b" * 40).returncode)

    def test_reusable_input_cannot_fall_back_to_event_sha_when_empty(self):
        self.git("init", "-q")
        commit = self.commit("candidate")
        for candidate, expected in (("", 2), ("b" * 40, 2), (commit, 0)):
            result = self.run_tool(CI, "checkout", "--commit", commit, env=dict(self.env,
                CI_WORKFLOW_CANDIDATE_SHA=candidate, GITHUB_EVENT_NAME="pull_request_target"))
            self.assertEqual(expected, result.returncode, result.stderr)

    def seed(self):
        (self.root / ".lake/build/lib").mkdir(parents=True)
        (self.root / ".lake/build/lib/Module.olean").write_bytes(b"seed bytes")
        result = self.run_tool(CACHE, "snapshot")
        self.assertEqual(0, result.returncode, result.stderr)
        key_output = subprocess.run([sys.executable, str(CACHE),
            "keys", "--repository", str(self.root)], check=True, env=self.env, capture_output=True, text=True).stdout
        keys = dict(line.split("=", 1) for line in key_output.splitlines())
        cached = self.root / keys["project_path"]
        self.assertTrue((cached / "manifest.json").is_file())
        shutil.rmtree(self.root / ".lake")
        return cached, keys["project_key"]

    def production(self, key, failure=False):
        (self.root / "Makefile").write_text("current:\n\t@echo producer >> calls\n\t@exit " + ("7" if failure else "0") + "\n")
        return subprocess.run(["bash", "-euc", '"$PYTHON" "$CACHE" restore --repository "$ROOT" --project-key "$KEY"; make -C "$ROOT" current'],
            env=dict(self.env, PYTHON=sys.executable, CACHE=str(CACHE), ROOT=str(self.root), KEY=key),
            capture_output=True, text=True)

    def test_valid_actions_seed_still_enters_production_and_signals_release_skip(self):
        _, key = self.seed()
        result = self.production(key)
        self.assertEqual(0, result.returncode, result.stderr)
        self.assertEqual("producer\n", (self.root / "calls").read_text())
        self.assertEqual(b"seed bytes", (self.root / ".lake/build/lib/Module.olean").read_bytes())
        self.assertIn("STRATALINT_ACTIONS_CACHE_SEEDED=1", (self.root / "environment").read_text())

    def test_corruption_and_transfer_miss_reach_production_under_set_e(self):
        cached, key = self.seed()
        (cached / "data/lib/Module.olean").write_bytes(b"corrupt")
        result = self.production(key)
        self.assertEqual(0, result.returncode, result.stderr)
        self.assertFalse((self.root / ".lake/build/lib/Module.olean").exists())
        self.assertNotIn("STRATALINT_ACTIONS_CACHE_SEEDED=1", (self.root / "environment").read_text())
        result = self.production("")
        self.assertEqual(0, result.returncode, result.stderr)
        self.assertEqual("producer\nproducer\n", (self.root / "calls").read_text())
        result = self.production(key, failure=True)
        self.assertNotEqual(0, result.returncode)
        self.assertEqual("producer\nproducer\nproducer\n", (self.root / "calls").read_text())

    def test_foreign_partition_is_a_miss_and_snapshot_save_failure_is_nonfatal(self):
        _, key = self.seed()
        result = self.production(key.replace(REV, "b" * 40))
        self.assertEqual(0, result.returncode, result.stderr)
        self.assertFalse((self.root / ".lake/build/lib/Module.olean").exists())
        shutil.rmtree(self.root / "build/lean-cache")
        (self.root / "build/lean-cache").write_text("unwritable cache path")
        result = self.run_tool(CACHE, "snapshot")
        self.assertEqual(0, result.returncode, result.stderr)
        self.assertNotIn("project_ready=true", result.stdout)

    def test_malformed_actions_manifest_cannot_stop_normal_production(self):
        cached, key = self.seed()
        for malformed in ([], None, "broken", {"schema": "foreign"}):
            (cached / "manifest.json").write_text(json.dumps(malformed))
            result = self.production(key)
            self.assertEqual(0, result.returncode, result.stderr)
        self.assertEqual(4, len((self.root / "calls").read_text().splitlines()))

    def test_pull_request_cannot_publish_snapshot(self):
        (self.root / ".lake/build").mkdir(parents=True)
        (self.root / ".lake/build/output").write_text("project")
        result = self.run_tool(CACHE, "snapshot", env=dict(self.env, GITHUB_EVENT_NAME="pull_request_target"))
        self.assertEqual(0, result.returncode, result.stderr)
        self.assertFalse((self.root / "build/lean-cache/project/manifest.json").exists())

    def test_pull_request_restores_seed_with_writes_disabled(self):
        _, key = self.seed()
        self.env.update(GITHUB_EVENT_NAME="pull_request_target", STRATALINT_CACHE_WRITES="false")
        result = self.production(key)
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertEqual(b"seed bytes", (self.root / ".lake/build/lib/Module.olean").read_bytes())
        self.assertEqual("producer\n", (self.root / "calls").read_text())
        self.assertIn("STRATALINT_ACTIONS_CACHE_SEEDED=1", (self.root / "environment").read_text())

    def test_transport_delegates_to_common_owner_without_a_package_cache(self):
        sys.path.insert(0, str(CI.parent))
        owner = importlib.import_module("ci")
        self.git("init", "-q")
        lock = self.root / "packages.lock.json"
        lock.write_text(json.dumps({"dependencies": {"net10.0": {"Fixture": {"type": "Direct", "resolved": "1.0"}}}}))
        self.git("add", "packages.lock.json")
        run = subprocess.run
        calls = []
        def invoke(command, **options):
            if command[0] == "dotnet":
                calls.append((command, options))
                return subprocess.CompletedProcess(command, 0)
            return run(command, **options)
        args = owner.argparse.Namespace(repository=self.root, stage="engineering", commit=REV,
            run_id="17", run_attempt="2", archive=self.root / "stage.tar.gz")
        with mock.patch.dict(os.environ, dict(self.env, NUGET_PACKAGES=str(self.root / "absent-packages"))), \
             mock.patch.object(owner.subprocess, "run", side_effect=invoke), \
             mock.patch.object(owner, "extract") as extract:
            for command in ("pack", "restore", "verify"):
                with self.subTest(command=command):
                    args.command = command
                    owner.transport(args)
                    expected = ["dotnet", owner.RUNNER, "transport-pack" if command == "pack" else "transport-verify",
                        "--repository", str(self.root), "--stage", "engineering", "--commit", REV,
                        "--run-id", "17", "--run-attempt", "2"]
                    if command == "pack":
                        expected.extend(["--archive", str(args.archive)])
                    self.assertEqual((expected, dict(cwd=self.root, check=True)), calls[-1])
                    self.assertFalse((self.root / "build/ci/nuget").exists())
                    self.assertFalse((self.root / "environment").exists())
        extract.assert_called_once_with(self.root, args.archive)
        self.assertEqual(3, len(calls))


class SnapshotContracts(CacheFixture, unittest.TestCase):
    def test_internal_dependency_file_links_round_trip_as_private_material(self):
        source, material = self.dependency_files()
        links = {
            "mathlib/scripts/bench/size/run.py": "run",
            "mathlib/scripts/bench/build/fake-root/bin/lean.py": "lean",
            "batteries/docs/README.md": "../README.md",
            "batteries/docs/README.alias": "README.md",
        }
        expected = dict(material)
        for relative, target in links.items():
            path = source / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.symlink_to(target)
            expected[relative] = (path.read_bytes(), path.stat().st_mode & 0o777)
        readiness, receipts = self.snapshot_result()
        self.assertEqual({"dependency_ready": "true", "project_ready": "false", "report_ready": "false"},
                         readiness, receipts)
        self.assertEqual("snapshot", receipts["dependency"]["status"])
        cached = self.root / "build/lean-cache/dependency"
        manifest = json.loads((cached / "manifest.json").read_text())
        self.assertEqual("lean-actions-seed-v1", manifest["schema"])
        self.assertEqual([{"path": relative, "sha256": hashlib.sha256(data).hexdigest(), "mode": mode}
                          for relative, (data, mode) in sorted(expected.items())], manifest["files"])
        self.assertFalse(any(path.is_symlink() for path in (cached / "data").rglob("*")))
        for relative, (data, mode) in expected.items():
            self.assertEqual(data, (source / relative).read_bytes())
            self.assertEqual(mode, (source / relative).stat().st_mode & 0o777)
            self.assertEqual(data, (cached / "data" / relative).read_bytes())
        for relative, target in links.items():
            self.assertTrue((source / relative).is_symlink())
            self.assertEqual(target, os.readlink(source / relative))
        (source / "batteries/README.md").write_bytes(b"changed producer bytes")
        self.assertEqual(expected["batteries/README.md"][0], (cached / "data/batteries/README.md").read_bytes())
        shutil.rmtree(source)
        result = self.run_tool(CACHE, "restore", "--dependency-key", manifest["key"])
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertIn('"status": "restored"', result.stdout)
        self.assertIn("STRATALINT_ACTIONS_CACHE_SEEDED=0", (self.root / "environment").read_text())
        for relative, (data, mode) in expected.items():
            path = source / relative
            self.assertFalse(path.is_symlink())
            self.assertEqual(data, path.read_bytes())
            self.assertEqual(mode, path.stat().st_mode & 0o777)
        (source / "batteries/docs/README.md").write_bytes(b"changed consumer bytes")
        self.assertEqual(expected["batteries/docs/README.md"][0],
                         (cached / "data/batteries/docs/README.md").read_bytes())
        self.assertEqual(expected["batteries/README.md"][0], (source / "batteries/README.md").read_bytes())
        (cached / "data/batteries/README.md").write_bytes(b"changed cache bytes")
        self.assertEqual(expected["batteries/README.md"][0], (source / "batteries/README.md").read_bytes())

    def test_corrupt_dependency_seed_falls_back_without_replacing_current_material(self):
        source, _ = self.dependency_files()
        shutil.copy2(source / "batteries/README.md", source / "batteries/README.copy")
        readiness, _ = self.snapshot_result()
        self.assertEqual("true", readiness["dependency_ready"])
        cached = self.root / "build/lean-cache/dependency"
        key = json.loads((cached / "manifest.json").read_text())["key"]
        saved = cached / "data/batteries/README.md"
        original, mode = saved.read_bytes(), saved.stat().st_mode & 0o777
        (self.root / "Makefile").write_text("current:\n\t@echo producer >> calls\n\t@exit $${PRODUCER_EXIT:-0}\n")
        for corruption in ("bytes", "mode", "link", "missing", "extra"):
            with self.subTest(corruption=corruption):
                (source / "batteries/README.md").write_bytes(b"current material")
                if corruption == "bytes":
                    saved.write_bytes(b"corrupted bytes")
                elif corruption == "mode":
                    saved.chmod(0o755)
                elif corruption == "link":
                    saved.unlink()
                    saved.symlink_to("README.copy")
                elif corruption == "missing":
                    saved.unlink()
                else:
                    (saved.parent / "extra").write_bytes(b"unlisted")
                for production_exit in ("0", "9"):
                    result = subprocess.run(["bash", "-euc",
                        '"$PYTHON" "$CACHE" restore --repository "$ROOT" --dependency-key "$KEY"; make -C "$ROOT" current'],
                        env=dict(self.env, PYTHON=sys.executable, CACHE=str(CACHE), ROOT=str(self.root),
                                 KEY=key, PRODUCER_EXIT=production_exit), capture_output=True, text=True)
                    self.assertEqual(production_exit == "0", result.returncode == 0, result.stdout + result.stderr)
                    self.assertIn('"layer": "dependency", "reason":', result.stdout)
                    self.assertIn('"status": "miss"', result.stdout)
                    self.assertEqual(b"current material", (source / "batteries/README.md").read_bytes())
                    self.assertNotIn("STRATALINT_ACTIONS_CACHE_SEEDED=1", (self.root / "environment").read_text())
                saved.unlink(missing_ok=True)
                saved.write_bytes(original)
                saved.chmod(mode)
                (saved.parent / "extra").unlink(missing_ok=True)
        self.assertEqual(["producer"] * 10, (self.root / "calls").read_text().splitlines())


if __name__ == "__main__":
    unittest.main()
