"""Executable resolver and optional Actions seed contracts, with isolated Git/data."""
import hashlib
import builtins
import contextlib
import io
import json
import importlib
import os
import pathlib
import shutil
import signal
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
                        CI_WORKFLOW_INPUTS="", GITHUB_EVENT_PATH="",
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
        self.env["GITHUB_EVENT_NAME"] = "pull_request"
        self.git("init", "-q")
        (self.root / "Meta").mkdir()
        (self.root / "Meta/FILEMAP.toml").write_text('''schema_version = 4
resources = []
[residence_policy]
case_id = "fixture"
desired = "registered"
known_violation_count = 0
status = "compliant"
[[files]]
pattern = "lake-manifest.json"
require = []
kind = "data"
admission_plane = "content"
produced_by = "none"
consumed_by = ["fixture"]
verified_by = ["fixture"]
artifact_id = "none"
runtime_disposition = "committed-source"
''')
        self.git("add", "Meta/FILEMAP.toml")
        base = self.commit("base")
        self.git("checkout", "-qb", "topic")
        (self.root / "lake-manifest.json").write_text("{}")
        head = self.commit("head")
        merge = self.git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                         "commit-tree", "HEAD^{tree}", "-p", base, "-p", head, "-m", "merge")
        self.git("checkout", "--detach", merge)
        self.env["GITHUB_SHA"] = merge
        result = self.run_tool(CI, "resolve", "--head", head)
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
        self.env["GITHUB_SHA"] = commit
        self.assertNotEqual(0, self.run_tool(CI, "resolve", "--head", commit).returncode)
        self.assertNotEqual(0, self.run_tool(CI, "checkout", "--commit", "b" * 40).returncode)

    def test_reusable_input_cannot_fall_back_to_event_sha_when_empty(self):
        self.git("init", "-q")
        commit = self.commit("candidate")
        for candidate, expected in (("", 2), (None, 2), (19, 2), ("b" * 40, 2), (commit, 0)):
            result = self.run_tool(CI, "checkout", "--commit", commit, env=dict(self.env,
                CI_WORKFLOW_INPUTS=json.dumps({"candidate_sha": candidate})))
            self.assertEqual(expected, result.returncode, result.stderr)

    def test_native_checkout_accepts_empty_actions_input_context(self):
        self.git("init", "-q")
        commit = self.commit("candidate")
        for inputs in (None, {}):
            result = self.run_tool(CI, "checkout", "--commit", commit, env=dict(self.env,
                CI_WORKFLOW_INPUTS=json.dumps(inputs)))
            self.assertEqual(0, result.returncode, result.stderr)

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
            extract.assert_called_once_with(self.root, args.archive, args.stage)
        self.assertEqual(3, len(calls))


class SnapshotContracts(CacheFixture, unittest.TestCase):
    def restore_owner(self):
        sys.path.insert(0, str(CACHE.parent))
        return importlib.import_module("lean_actions")

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

    def test_bounded_snapshot_publishes_only_after_worker_and_save_window(self):
        owner = self.restore_owner()
        from cache_deadline import CacheDeadline
        source, cached, _ = self.restore_fixture("project", {"a.olean": b"accepted"})
        before = (cached / "manifest.json").read_bytes()
        (source / "a.olean").write_bytes(b"new source")
        for cutoff in (None, 164, 400):
            with self.subTest(cutoff=cutoff), mock.patch.dict(os.environ, self.env), \
                 contextlib.redirect_stdout(io.StringIO()) as receipts:
                (self.root / "outputs").unlink(missing_ok=True)
                deadline = CacheDeadline(cutoff, monotonic=lambda: 100)
                owner.snapshot(self.root, owner.actions_keys(self.root), ["project"], deadline=deadline)
                outputs = (self.root / "outputs").read_text().splitlines()
                self.assertEqual(["project_ready=" + str(cutoff == 400).lower(),
                                  "save_timeout_minutes=" + ("4" if cutoff == 400 else "1")], outputs)
                self.assertFalse(list(cached.parent.glob(".snapshot-*")))
                if cutoff == 400:
                    self.assertEqual(b"new source", (cached / "data/a.olean").read_bytes())
                else:
                    self.assertEqual(before, (cached / "manifest.json").read_bytes())

    def test_bounded_snapshot_timeout_and_signals_clean_only_owned_staging(self):
        owner = self.restore_owner()
        from cache_deadline import CacheDeadline
        source, cached, _ = self.restore_fixture("project", {"a.olean": b"accepted"})
        before = (cached / "manifest.json").read_bytes()
        sibling = cached.parent / ".snapshot-other-owner"
        sibling.mkdir()
        (sibling / "material").write_bytes(b"concurrent snapshot")
        for cancellation in ("timeout", signal.SIGTERM, signal.SIGINT, "late", "leader-exited"):
            process = mock.Mock(pid=12345)
            process.poll.return_value = None
            deadline = CacheDeadline(400, monotonic=lambda: 100)

            def start(command, **kwargs):
                self.assertNotIn("GITHUB_OUTPUT", kwargs["env"])
                self.assertTrue(kwargs["start_new_session"])
                staged = pathlib.Path(command[command.index("--snapshot-directory") + 1])
                (staged / "partial").write_bytes(b"unfinished new material")
                if cancellation == "late":
                    (staged / "manifest.json").write_text(json.dumps({"files": []}))
                return process

            def interrupted(*, timeout):
                self.assertEqual(235, timeout)
                if cancellation == "timeout":
                    raise subprocess.TimeoutExpired("snapshot", timeout)
                if cancellation == "late":
                    deadline.cutoff = 100
                    process.poll.return_value = 0
                    return 0
                if cancellation == "leader-exited":
                    process.poll.return_value = 7
                    return 7
                signal.getsignal(cancellation)(cancellation, None)

            calls = []
            def wait(*, timeout=None):
                calls.append(timeout)
                return interrupted(timeout=timeout) if len(calls) == 1 else 0
            process.wait.side_effect = wait
            with self.subTest(cancellation=cancellation), mock.patch.dict(os.environ, self.env), \
                 mock.patch.object(owner.subprocess, "Popen", side_effect=start), \
                 mock.patch.object(owner.os, "killpg") as kill, \
                 contextlib.redirect_stdout(io.StringIO()) as receipts:
                if cancellation in (signal.SIGTERM, signal.SIGINT):
                    with self.assertRaises(SystemExit) as raised:
                        owner.snapshot(self.root, owner.actions_keys(self.root), ["project"], deadline=deadline)
                    self.assertEqual(128 + cancellation, raised.exception.code)
                else:
                    owner.snapshot(self.root, owner.actions_keys(self.root), ["project"], deadline=deadline)
                kill.assert_called_once_with(process.pid, signal.SIGKILL)
                self.assertNotIn("project_ready=true", receipts.getvalue())
                self.assertIn("project_ready=false", receipts.getvalue())
                self.assertIn("save_timeout_minutes=1", receipts.getvalue())
                self.assertEqual(before, (cached / "manifest.json").read_bytes())
                self.assertEqual([sibling], list(cached.parent.glob(".snapshot-*")))
                self.assertEqual(b"concurrent snapshot", (sibling / "material").read_bytes())

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

    def test_snapshot_publication_failure_restores_previous_seed(self):
        owner = self.restore_owner()
        source, cached, _ = self.restore_fixture("project", {"a.olean": b"accepted"})
        before = {path.relative_to(cached).as_posix(): path.read_bytes()
                  for path in cached.rglob("*") if path.is_file()}
        (source / "a.olean").write_bytes(b"new source")
        rename = pathlib.Path.rename

        def fail_install(path, target):
            if path.name.startswith(".snapshot-") and target == cached:
                raise OSError("injected snapshot publication failure")
            return rename(path, target)

        with mock.patch.dict(os.environ, self.env), mock.patch.object(pathlib.Path, "rename", fail_install), \
             contextlib.redirect_stdout(io.StringIO()) as receipts:
            owner.snapshot(self.root, owner.actions_keys(self.root), ["project"])
        self.assertIn("project_ready=false", receipts.getvalue())
        self.assertEqual(before, {path.relative_to(cached).as_posix(): path.read_bytes()
                                 for path in cached.rglob("*") if path.is_file()})
        self.assertFalse(list(cached.parent.glob(".snapshot-*")))

    def test_large_layer_snapshot_copies_and_hashes_in_one_read(self):
        owner = self.restore_owner()
        material = {"a.olean": bytes(range(251)) * 9000, "nested/z.olean": b"last material"}
        for layer, target in (("dependency", ".lake/packages"), ("project", ".lake/build")):
            with self.subTest(layer=layer):
                source = self.root / target
                for name, data in material.items():
                    path = source / name
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_bytes(data)
                    path.chmod(0o640)
                    os.utime(path, (1_600_000_000, 1_600_000_000))
                observed = {"source": 0, "staged": 0}

                class CountReads:
                    def __init__(self, stream, area):
                        self.stream, self.area = stream, area

                    def __enter__(self):
                        return self

                    def __exit__(self, *args):
                        return self.stream.__exit__(*args)

                    def __getattr__(self, name):
                        return getattr(self.stream, name)

                    def read(self, size=-1):
                        data = self.stream.read(size)
                        observed[self.area] += len(data)
                        return data

                def instrument(open_file):
                    def opened(file, mode="r", *args, **kwargs):
                        stream = open_file(file, mode, *args, **kwargs)
                        path = pathlib.Path(file) if not isinstance(file, int) else None
                        if path is not None and "r" in mode:
                            if path.is_relative_to(source):
                                return CountReads(stream, "source")
                            if path.is_relative_to(self.root / "build/lean-cache") and path.suffix == ".olean":
                                return CountReads(stream, "staged")
                        return stream
                    return opened

                with mock.patch.dict(os.environ, self.env), \
                     mock.patch.object(io, "open", side_effect=instrument(io.open)), \
                     mock.patch.object(builtins, "open", side_effect=instrument(builtins.open)), \
                     mock.patch.object(shutil, "_HAS_FCOPYFILE", False, create=True), \
                     mock.patch.object(shutil, "_USE_CP_SENDFILE", False, create=True), \
                     contextlib.redirect_stdout(io.StringIO()) as receipts:
                    owner.snapshot(self.root, owner.actions_keys(self.root), [layer])
                self.assertIn('"status": "snapshot"', receipts.getvalue())
                self.assertEqual({"source": sum(map(len, material.values())), "staged": 0}, observed)
                cached = self.root / "build/lean-cache" / layer
                expected = [{"path": name, "sha256": hashlib.sha256(data).hexdigest(), "mode": 0o640}
                            for name, data in sorted(material.items())]
                self.assertEqual(expected, json.loads((cached / "manifest.json").read_text())["files"])
                for name, data in material.items():
                    destination = cached / "data" / name
                    self.assertEqual(data, destination.read_bytes())
                    self.assertEqual(0o640, destination.stat().st_mode & 0o777)
                    self.assertEqual(1_600_000_000, destination.stat().st_mtime)
                    self.assertNotEqual((source / name).stat().st_ino, destination.stat().st_ino)
                (source / "a.olean").write_bytes(b"source changed")
                self.assertEqual(material["a.olean"], (cached / "data/a.olean").read_bytes())

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

    def test_snapshot_late_read_failure_keeps_published_material_and_source(self):
        owner = self.restore_owner()
        for layer in ("dependency", "project"):
            with self.subTest(layer=layer):
                source, cached, _ = self.restore_fixture(layer, {"a.olean": b"accepted", "z.olean": b"last"})
                before = {path.relative_to(cached).as_posix(): path.read_bytes()
                          for path in cached.rglob("*") if path.is_file()}
                (source / "a.olean").write_bytes(b"new source")
                def fail_late(open_file):
                    def opened(path, mode="r", *args, **kwargs):
                        if pathlib.Path(path) == source / "z.olean" and mode == "rb":
                            raise OSError("injected late source read failure")
                        return open_file(path, mode, *args, **kwargs)
                    return opened

                with mock.patch.dict(os.environ, self.env), \
                     mock.patch.object(io, "open", side_effect=fail_late(io.open)), \
                     mock.patch.object(builtins, "open", side_effect=fail_late(builtins.open)), \
                     contextlib.redirect_stdout(io.StringIO()) as receipts:
                    owner.snapshot(self.root, owner.actions_keys(self.root), [layer])
                self.assertIn(layer + "_ready=false", receipts.getvalue())
                self.assertEqual(before, {path.relative_to(cached).as_posix(): path.read_bytes()
                                         for path in cached.rglob("*") if path.is_file()})
                self.assertEqual(b"new source", (source / "a.olean").read_bytes())
                self.assertFalse(list(cached.parent.glob(".snapshot-*")))

    def restore_fixture(self, layer, material):
        source = self.root / (".lake/packages" if layer == "dependency" else ".lake/build")
        for relative, data in material.items():
            path = source / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
            path.chmod(0o640)
            os.utime(path, (1_600_000_000, 1_600_000_000))
        snapshot = self.run_tool(CACHE, "snapshot", "--layers", layer)
        self.assertEqual(0, snapshot.returncode, snapshot.stdout + snapshot.stderr)
        self.assertIn('"status": "snapshot"', snapshot.stdout)
        cached = self.root / "build/lean-cache" / layer
        manifest = json.loads((cached / "manifest.json").read_text())
        (source / "current-only").write_bytes(b"current material")
        return source, cached, manifest

    def test_dependency_and_project_restore_read_each_material_once(self):
        owner = self.restore_owner()
        material = {"a.olean": bytes(range(251)) * 9000, "nested/z.olean": b"last material"}
        for layer in ("dependency", "project"):
            with self.subTest(layer=layer):
                source, cached, manifest = self.restore_fixture(layer, material)
                (cached / "data/unlisted").write_bytes(b"unlisted neighbour")
                observed = {relative: 0 for relative in material}

                class CountReads:
                    def __init__(self, stream, name):
                        self.stream, self.name = stream, name

                    def __enter__(self):
                        return self

                    def __exit__(self, *args):
                        return self.stream.__exit__(*args)

                    def __getattr__(self, name):
                        return getattr(self.stream, name)

                    def read(self, size=-1):
                        data = self.stream.read(size)
                        observed[self.name] += len(data)
                        return data

                def instrument(open_file):
                    def opened(file, mode="r", *args, **kwargs):
                        stream = open_file(file, mode, *args, **kwargs)
                        path = pathlib.Path(file) if not isinstance(file, int) else None
                        if path is not None and "r" in mode and path.is_relative_to(cached / "data"):
                            relative = path.relative_to(cached / "data").as_posix()
                            self.assertIn(relative, observed, "unlisted cache material was read")
                            return CountReads(stream, relative)
                        return stream
                    return opened

                # Observe bytes through the portable stream path, including copy2's reads.
                # Fast-copy syscalls bypass Python stream instrumentation.
                with mock.patch.dict(os.environ, self.env), \
                     mock.patch.object(io, "open", side_effect=instrument(io.open)), \
                     mock.patch.object(builtins, "open", side_effect=instrument(builtins.open)), \
                     mock.patch.object(shutil, "_HAS_FCOPYFILE", False, create=True), \
                     mock.patch.object(shutil, "_USE_CP_SENDFILE", False, create=True), \
                     contextlib.redirect_stdout(io.StringIO()) as receipts:
                    owner.restore(self.root, owner.actions_keys(self.root), {layer: manifest["key"]}, [layer])
                self.assertIn('"status": "restored"', receipts.getvalue())
                self.assertEqual({name: len(data) for name, data in material.items()}, observed)
                self.assertFalse((source / "current-only").exists())
                self.assertFalse((source / "unlisted").exists())
                for relative, data in material.items():
                    self.assertEqual(data, (source / relative).read_bytes())
                    self.assertEqual(0o640, (source / relative).stat().st_mode & 0o777)
                    self.assertEqual(1_600_000_000, (source / relative).stat().st_mtime)
                (source / "a.olean").write_bytes(b"changed consumer")
                self.assertEqual(material["a.olean"], (cached / "data/a.olean").read_bytes())

    def test_dependency_and_project_reject_late_bad_material_without_installing(self):
        owner = self.restore_owner()
        material = {"a.olean": b"first material", "nested/z.olean": b"last material"}
        for layer in ("dependency", "project"):
            source, cached, manifest = self.restore_fixture(layer, material)
            for failure in ("hash", "mode", "missing", "directory", "symlink", "parent-link",
                            "duplicate", "escape", "backslash", "invalid-sha", "invalid-mode", "empty", "copy-error"):
                with self.subTest(layer=layer, failure=failure):
                    saved = cached / "data/nested/z.olean"
                    inventory = json.loads(json.dumps(manifest))
                    last = inventory["files"][-1]
                    if failure == "hash":
                        saved.write_bytes(b"corrupt")
                    elif failure == "mode":
                        saved.chmod(0o755)
                    elif failure in ("missing", "directory", "symlink"):
                        saved.unlink()
                        if failure == "directory":
                            saved.mkdir()
                        elif failure == "symlink":
                            saved.symlink_to("../a.olean")
                    elif failure == "parent-link":
                        saved.parent.rename(cached / "data/real-nested")
                        saved.parent.symlink_to("real-nested", target_is_directory=True)
                    elif failure == "duplicate":
                        inventory["files"].append(dict(last))
                    elif failure == "escape":
                        last["path"] = "../escaped"
                    elif failure == "backslash":
                        last["path"] = "nested\\z.olean"
                    elif failure == "invalid-sha":
                        last["sha256"] = "broken"
                    elif failure == "invalid-mode":
                        last["mode"] = True
                    elif failure == "empty":
                        inventory["files"] = []
                    (cached / "manifest.json").write_text(json.dumps(inventory))
                    copy_metadata = shutil.copystat

                    def copy_failure(original, destination, **kwargs):
                        if pathlib.Path(original) == saved:
                            raise OSError("injected copy failure after earlier material was staged")
                        return copy_metadata(original, destination, **kwargs)

                    fault = (mock.patch.object(shutil, "copystat", side_effect=copy_failure)
                             if failure == "copy-error" else contextlib.nullcontext())
                    with mock.patch.dict(os.environ, self.env), fault, contextlib.redirect_stdout(io.StringIO()) as receipts:
                        owner.restore(self.root, owner.actions_keys(self.root), {layer: manifest["key"]}, [layer])
                    self.assertIn('"status": "miss"', receipts.getvalue())
                    self.assertEqual(b"current material", (source / "current-only").read_bytes())
                    self.assertEqual(material["a.olean"], (source / "a.olean").read_bytes())
                    self.assertEqual(material["nested/z.olean"], (source / "nested/z.olean").read_bytes())
                    self.assertEqual([], list(source.parent.glob(".actions-*")))
                    if failure == "parent-link":
                        saved.parent.unlink()
                        (cached / "data/real-nested").rename(saved.parent)
                    if saved.is_dir():
                        saved.rmdir()
                    else:
                        saved.unlink(missing_ok=True)
                    saved.write_bytes(material["nested/z.olean"])
                    saved.chmod(0o640)

    def test_dependency_module_and_submodule_seed_round_trip(self):
        self.assert_module_and_submodule_seed_round_trip("dependency")

    def test_project_module_and_submodule_seed_round_trip(self):
        self.assert_module_and_submodule_seed_round_trip("project")

    def assert_module_and_submodule_seed_round_trip(self, layer):
        source = self.root / (".lake/packages" if layer == "dependency" else ".lake/build")
        prefix = "mathlib/.lake/build/lib/lean" if layer == "dependency" else "lib/lean"
        material = {
            prefix + "/Foo.olean": (b"module bytes", 0o640),
            prefix + "/Foo/Bar.olean": (b"submodule bytes", 0o644),
        }
        for relative, (data, mode) in material.items():
            path = source / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
            path.chmod(mode)
        snapshot = self.run_tool(CACHE, "snapshot", "--layers", layer)
        self.assertEqual(0, snapshot.returncode, snapshot.stdout + snapshot.stderr)
        self.assertIn('"status": "snapshot"', snapshot.stdout, snapshot.stdout + snapshot.stderr)
        cached = self.root / "build/lean-cache" / layer
        key = json.loads((cached / "manifest.json").read_text())["key"]
        shutil.rmtree(source)
        restore = self.run_tool(CACHE, "restore", "--layers", layer, "--" + layer + "-key", key)
        self.assertEqual(0, restore.returncode, restore.stdout + restore.stderr)
        self.assertIn('"status": "restored"', restore.stdout, restore.stdout + restore.stderr)
        for relative, (data, mode) in material.items():
            path = source / relative
            self.assertEqual(data, path.read_bytes())
            self.assertEqual(mode, path.stat().st_mode & 0o777)

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
        self.assertEqual({"dependency_ready": "true", "project_ready": "false"},
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
                    if corruption == "extra":
                        # A cache neighbour is not registered material and must not be copied.
                        self.assertIn('"status": "restored"', result.stdout)
                        self.assertEqual(original, (source / "batteries/README.md").read_bytes())
                        self.assertFalse((source / "batteries/extra").exists())
                        self.assertEqual(b"unlisted", (saved.parent / "extra").read_bytes())
                    else:
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
