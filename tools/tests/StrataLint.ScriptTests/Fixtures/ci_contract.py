"""Executable resolver and optional Actions seed contracts, with isolated Git/data."""
import hashlib
import json
import importlib
import os
import pathlib
import platform
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
            "--candidate-lean-report", str(self.report), "--test-map-cache-root", str(self.root / "test-maps"),
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
                self.assertEqual(f"dotnet {dll} check --protected-base {'a' * 40} --candidate-lean-report {self.report} --test-map-cache-root {self.root / 'test-maps'}", calls[1])
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

    def tearDown(self):
        self.temp.cleanup()

    def run_tool(self, script, *args, env=None):
        return subprocess.run([sys.executable, str(script), *args, "--repository", str(self.root)],
                              env=env or self.env, capture_output=True, text=True)


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
        self.assertNotEqual(0, self.run_tool(CI, "resolve", "--head", commit).returncode)
        self.assertNotEqual(0, self.run_tool(CI, "checkout", "--commit", "b" * 40).returncode)

    def test_reusable_input_cannot_fall_back_to_event_sha_when_empty(self):
        self.git("init", "-q")
        commit = self.commit("candidate")
        for candidate, expected in (("", 2), ("b" * 40, 2), (commit, 0)):
            result = self.run_tool(CI, "checkout", "--commit", commit, env=dict(self.env,
                CI_WORKFLOW_INPUTS=json.dumps({"candidate_sha": candidate})))
            self.assertEqual(expected, result.returncode, result.stderr)

    def seed(self):
        (self.root / ".lake/build/lib").mkdir(parents=True)
        (self.root / ".lake/build/lib/Module.olean").write_bytes(b"seed bytes")
        result = self.run_tool(CACHE, "snapshot")
        self.assertEqual(0, result.returncode, result.stderr)
        keys = json.loads(subprocess.run([sys.executable, str(REPO / "tools/scripts/worktree/lean_cache.py"),
            "keys", "--repository", str(self.root)], check=True, env=self.env, capture_output=True, text=True).stdout)
        cached = self.root / keys["project"]["path"]
        self.assertTrue((cached / "manifest.json").is_file())
        shutil.rmtree(self.root / ".lake")
        return cached, keys["project"]["key"]

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
    def prepare_report(self):
        from lean_seed_contract import InspectorTests, FAKE_LAKE
        fixture = InspectorTests("test_inspector_runs_lake_on_exact_seed_with_zero_reinspection")
        fixture.setUp()
        self.addCleanup(fixture.doCleanups)
        self.root = fixture.root
        fixture.manifest["packages"][0]["rev"] = REV
        fixture.save_manifest()
        fixture.output = self.root / "out/declared-current-report.json"
        # Exercise real compaction/validation with nonempty declaration material.
        fixture.lake.write_text(FAKE_LAKE.replace("output.write_text(", '''
spool = pathlib.Path(args[args.index("--material-spool") + 1])
spool.mkdir(parents=True, exist_ok=True)
for index, row in enumerate(modules):
    name = str(index) + ".statement"
    (spool / name).write_text(row["module"] + ":" + (root / row["source_path"]).read_text())
    row["declarations"] = [{"name": "value", "name_key": "ns(n0,5:value)", "kind": "def",
        "include_in_statement": True, "axioms": [], "material_file": name}]
    row["imports"] = ["D5.A"] if row["module"] == "Trureturing" else []
output.write_text('''))
        self.env.update(HOME=str(self.root), GITHUB_OUTPUT=str(self.root / "outputs"),
                        GITHUB_ENV=str(self.root / "environment"))
        return fixture

    def produce_report(self, fixture):
        result = fixture.pair()
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        # Synthetic current/pack evidence for the export consumer. Fake Lake is
        # the statement producer; this fixture does not claim a real current run.
        (self.root / ".gitignore").write_text("*\n")
        for args in (("init", "-q"), ("add", "-f", ".gitignore", "D5", "Trureturing.lean",
                     "lakefile.toml", "lake-manifest.json", "lean-toolchain"),
                     ("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "candidate")):
            subprocess.run(["git", "-C", str(self.root), *args], check=True, capture_output=True)
        self.env.update(CANDIDATE_SHA=subprocess.check_output(
            ["git", "-C", str(self.root), "rev-parse", "HEAD"], text=True).strip(), GITHUB_REPOSITORY="fixture/trureturing")
        self.write_handoff(fixture)
        return next(seed for seed in fixture.seeds()
                    if fixture.bundle_bytes(seed)[".seed.json"] == fixture.bundle_bytes(fixture.output)[".seed.json"])

    def write_handoff(self, fixture):
        summary = self.root / "build/ci/current-result.json"
        summary.parent.mkdir(parents=True, exist_ok=True)
        candidate, round_id = "e" * 64, "fixture-current-round"
        summary.write_text(json.dumps({"stage": "current", "exit": 0, "candidate": candidate,
            "current_evidence": "build/ci/current.json",
            "report": fixture.output.relative_to(self.root).as_posix()}))
        paths = [str(fixture.output.relative_to(self.root)) + suffix for suffix in
                 ("", ".sha256", ".input.attestation", ".provenance.json", ".materials.zip", ".seed.json")]
        def materials(paths):
            return [{"path": path, "sha256": hashlib.sha256((self.root / path).read_bytes()).hexdigest()}
                    for path in sorted(paths)]
        current = self.root / "build/ci/current.json"
        current.write_text(json.dumps({"version": 1, "candidate": candidate, "round": round_id,
            "steps": [{"name": name, "raw_exit": 0, "exit": 0, "status": "executed", "log": "build/ci/fixture.log"}
                      for name in ("lean-report", "scribe", "filemap", "check-current")], "materials": materials(paths)}))
        (self.root / "build/ci/current-transport.json").write_text(json.dumps({"version": 1, "stage": "current",
            "candidate": candidate, "round": round_id, "commit": self.env["CANDIDATE_SHA"],
            "run_id": int(self.env["GITHUB_RUN_ID"]), "run_attempt": int(self.env["GITHUB_RUN_ATTEMPT"]),
            "repository": self.env["GITHUB_REPOSITORY"], "materials": [dict(item,
                mode=(self.root / item["path"]).stat().st_mode & 0o777) for item in
                materials(paths + ["build/ci/current.json", "build/ci/current-result.json"])]}))

    def test_report_export_requires_matching_handoff(self):
        fixture = self.prepare_report()
        self.produce_report(fixture)
        self.assertEqual("true", self.snapshot_result()[0]["report_ready"])
        manifest = self.root / "build/lean-cache/report/manifest.json"
        saved = manifest.read_bytes()
        paths = [self.root / "build/ci" / name for name in ("current-result.json", "current.json", "current-transport.json")]
        original = [path.read_bytes() for path in paths]
        cases = ("missing-current", "missing-transport", "current-bytes", "summary-bytes", "candidate", "round",
                 "commit", "run_id", "run_attempt", "repository", "stage", "missing-binding", "material-binding",
                 "current-candidate", "current-round", "current-material")
        for case in cases:
            with self.subTest(case=case):
                if case == "missing-current": paths[1].unlink()
                elif case == "missing-transport": paths[2].unlink()
                elif case == "current-bytes": paths[1].write_bytes(original[1] + b" ")
                elif case == "summary-bytes": paths[0].write_bytes(original[0] + b" ")
                else:
                    transport = json.loads(original[2])
                    if case.startswith("current-"):
                        current = json.loads(original[1])
                        if case == "current-material": current["materials"][0]["sha256"] = "0" * 64
                        else: current[case.removeprefix("current-")] = "stale"
                        paths[1].write_text(json.dumps(current))
                        for item in transport["materials"]:
                            if item["path"] == "build/ci/current.json":
                                item["sha256"] = hashlib.sha256(paths[1].read_bytes()).hexdigest()
                    elif case == "missing-binding": transport["materials"] = transport["materials"][1:]
                    elif case == "material-binding": transport["materials"][-1]["sha256"] = "0" * 64
                    else: transport[case] = 99 if case in ("run_id", "run_attempt") else "stale"
                    paths[2].write_text(json.dumps(transport))
                readiness, receipts = self.snapshot_result()
                self.assertEqual("false", readiness["report_ready"], receipts)
                self.assertEqual("save-failed", receipts["report"]["status"])
                self.assertEqual(saved, manifest.read_bytes())
                self.assertFalse(list(manifest.parent.parent.glob(".snapshot-*")))
            for path, data in zip(paths, original): path.write_bytes(data)

    def test_report_export_does_not_revalidate(self):
        fixture = self.prepare_report()
        self.produce_report(fixture)
        hooks = self.root / "export-hooks"
        hooks.mkdir()
        (hooks / "sitecustomize.py").write_text('''
import atexit, collections, json, os, pathlib, subprocess, sys
counts = collections.Counter()
processes = []
def observe(frame, event, arg):
    if event == "call":
        file, name = pathlib.Path(frame.f_code.co_filename).name, frame.f_code.co_name
        if (file == "delta.py" and name in ("valid_bundle", "parse_json_modules", "validate_materials")
                or file == "zipfile.py" and name == "read"):
            counts[name] += 1
sys.setprofile(observe)
start = subprocess.Popen
def process(command, *args, **kwargs):
    processes.append(command)
    return start(command, *args, **kwargs)
subprocess.Popen = process
def finish():
    sys.setprofile(None)
    with open(os.environ["EXPORT_OBSERVATIONS"], "a") as stream:
        stream.write(json.dumps({"counts": dict(counts), "processes": processes}) + "\\n")
atexit.register(finish)
''')
        observations = self.root / "export-observations.jsonl"
        with mock.patch.dict(self.env, PYTHONPATH=str(hooks), EXPORT_OBSERVATIONS=str(observations)):
            readiness, receipts = self.snapshot_result()
        self.assertEqual("true", readiness["report_ready"], receipts)
        recorded = [json.loads(line) for line in observations.read_text().splitlines()]
        print("REPORT_EXPORT_CALLS " + json.dumps(recorded), flush=True)
        self.assertEqual({}, {key: value for row in recorded for key, value in row["counts"].items()})
        self.assertTrue(all(pathlib.Path(command[0]).name == "git" for row in recorded for command in row["processes"]), recorded)

    def test_report_snapshot_keeps_only_current_complete_seed(self):
        from argparse import Namespace
        from lean_seed_contract import DeltaTests
        sys.path.insert(0, str(REPO / "tools/lean-inspector"))
        from report_cache import store
        fixture = self.prepare_report()
        current = self.produce_report(fixture)
        partition = json.loads(fixture.bundle_bytes(current)[".seed.json"])["partition"]
        history = DeltaTests()
        history.setUp()
        self.addCleanup(history.doCleanups)
        history.add_declaration_material()
        for index, seed_partition in enumerate((partition, partition, partition.replace(REV, "f" * 40)), 1):
            history.address = str(index) * 64
            history.store()
            pathlib.Path(str(history.report) + ".seed.json").write_text(json.dumps({
                "schema": "lean-report-seed-v1", "partition": seed_partition, "runtime_sha256": "c" * 64,
                "report_sha256": hashlib.sha256(history.report.read_bytes()).hexdigest(),
                "materials_sha256": hashlib.sha256(pathlib.Path(str(history.report) + ".materials.zip").read_bytes()).hexdigest()}))
            self.assertTrue(store(Namespace(repository=None, report=history.report, cache_root=fixture.cache)))
        seeds = fixture.seeds()
        self.assertEqual(4, len(seeds))
        for seed in seeds:
            os.utime(seed.parent, ns=(1, 1) if seed == current else (2, 2))
        before = {seed: fixture.bundle_bytes(seed) for seed in seeds}
        readiness, receipts = self.snapshot_result()
        self.assertEqual("true", readiness["report_ready"], receipts)
        cached = self.root / "build/lean-cache/report"
        expected = {current.relative_to(fixture.cache).as_posix() + suffix: data
                    for suffix, data in before[current].items()}
        actual = {path.relative_to(cached / "data").as_posix(): path.read_bytes()
                  for path in (cached / "data").rglob("*") if path.is_file()}
        print("REPORT_SNAPSHOT_INVENTORY " + json.dumps({
            "local_seed_count": len(seeds), "snapshot_files": len(actual),
            "snapshot_bytes": sum(map(len, actual.values())), "current_files": len(expected),
            "current_bytes": sum(map(len, expected.values())), "paths": sorted(actual)}), flush=True)
        self.assertEqual(expected, actual)
        self.assertEqual(before, {seed: fixture.bundle_bytes(seed) for seed in seeds})
        self.assertFalse(any(path.is_symlink() for path in (cached / "data").rglob("*")))
        self.assertEqual(0o700, (cached / "data").stat().st_mode & 0o777)
        key = json.loads((cached / "manifest.json").read_text())["key"]
        # Simulate a fresh PR runner; no report output can secretly seed it.
        shutil.rmtree(fixture.cache)
        shutil.rmtree(fixture.output.parent)
        self.env.update(GITHUB_EVENT_NAME="pull_request_target", STRATALINT_CACHE_WRITES="false")
        restored = self.run_tool(CACHE, "restore", "--report-key", key)
        self.assertEqual(0, restored.returncode, restored.stdout + restored.stderr)
        self.assertIn('"status": "restored"', restored.stdout)
        self.assertEqual([current], fixture.seeds())
        self.assertEqual(before[current], fixture.bundle_bytes(current))
        config = self.root / "lakefile.toml"
        config.write_text(config.read_text().replace('name = "fixture"', 'name = "metadata-only"'))
        reused = fixture.pair()
        self.assertEqual(0, reused.returncode, reused.stdout + reused.stderr)
        self.assertIn("mode=reuse changed=0 added=0 removed=0 recheck=0", reused.stdout)
        (self.root / "D5/A.lean").write_text("def a := 4\n")
        incremental = fixture.pair()
        self.assertEqual(0, incremental.returncode, incremental.stdout + incremental.stderr)
        self.assertIn("mode=delta changed=1 added=0 removed=0 recheck=2", incremental.stdout)
        produced = fixture.bundle_bytes(fixture.output)
        fixture.cache = self.root / "clean-cache"
        fixture.output = self.root / "clean-output/raw-lean-report.json"
        clean = fixture.pair()
        self.assertEqual(0, clean.returncode, clean.stdout + clean.stderr)
        for suffix in ("", ".materials.zip", ".seed.json", ".provenance.json", ".input.attestation"):
            self.assertEqual(produced[suffix], fixture.bundle_bytes(fixture.output)[suffix])
        commands = (self.root / "lake-runs").read_text().splitlines()
        self.assertEqual(4, commands.count("build"))
        self.assertEqual(3, sum("--run" in command for command in commands))
        readiness, receipts = self.snapshot_result()
        self.assertEqual("false", readiness["report_ready"])
        self.assertEqual("save-disabled", receipts["report"]["status"])
        self.assertEqual(actual, {path.relative_to(cached / "data").as_posix(): path.read_bytes()
                               for path in (cached / "data").rglob("*") if path.is_file()})

    def test_report_snapshot_rejects_invalid_current_without_using_history(self):
        fixture = self.prepare_report()
        current = self.produce_report(fixture)
        self.assertEqual("true", self.snapshot_result()[0]["report_ready"])
        cached = self.root / "build/lean-cache/report/manifest.json"
        saved = cached.read_bytes()
        bundle = fixture.bundle_bytes(fixture.output)
        summary = self.root / "build/ci/current-result.json"
        original_summary = summary.read_bytes()
        cases = ["missing-summary", "failed-current", "missing-report", "missing-seed", "materials", "partition", "identity",
                 "sha", "bound-sha", "bound-sha-name", "missing-sha", "missing-attestation", "missing-provenance", "missing-materials"]
        for case in cases:
            with self.subTest(case=case):
                if case == "missing-summary": summary.unlink()
                elif case == "failed-current":
                    failed = fixture.pair(LAKE_BUILD_FAIL="19")
                    self.assertEqual(19, failed.returncode, failed.stdout + failed.stderr)
                    summary.write_text(json.dumps({"stage": "current", "exit": 2,
                        "report": fixture.output.relative_to(self.root).as_posix()}))
                elif case == "missing-report": fixture.output.unlink()
                elif case == "missing-seed": pathlib.Path(str(fixture.output) + ".seed.json").unlink()
                elif case in ("sha", "bound-sha", "bound-sha-name"):
                    value = "0" * 64 + "  " + fixture.output.name + "\n"
                    if case == "bound-sha-name": value = hashlib.sha256(bundle[""]).hexdigest() + "  wrong-name.json\n"
                    pathlib.Path(str(fixture.output) + ".sha256").write_text(value)
                    # Current's material seal alone does not replace the original
                    # SHA sidecar grammar/digest check before copy rewrites it.
                    if case.startswith("bound-"): self.write_handoff(fixture)
                elif case.startswith("missing-"):
                    suffix = {"missing-sha": ".sha256", "missing-attestation": ".input.attestation",
                              "missing-provenance": ".provenance.json", "missing-materials": ".materials.zip"}[case]
                    pathlib.Path(str(fixture.output) + suffix).unlink()
                elif case == "materials": pathlib.Path(str(fixture.output) + ".materials.zip").write_bytes(b"corrupt")
                elif case == "partition":
                    seed = json.loads(bundle[".seed.json"])
                    seed["partition"] = seed["partition"].replace(REV, "f" * 40)
                    pathlib.Path(str(fixture.output) + ".seed.json").write_text(json.dumps(seed))
                else: (self.root / "D5/A.lean").write_text("def a := 99\n")
                readiness, receipts = self.snapshot_result()
                self.assertEqual("false", readiness["report_ready"], receipts)
                self.assertEqual("save-failed", receipts["report"]["status"])
                self.assertEqual(saved, cached.read_bytes())
                self.assertFalse(list(cached.parent.parent.glob(".snapshot-*")))
                fixture.write_bundle_bytes(fixture.output, bundle)
                summary.write_bytes(original_summary)
                (self.root / "D5/A.lean").write_text("def a := 1\n")
                self.write_handoff(fixture)
        self.assertEqual(bundle[".materials.zip"], fixture.bundle_bytes(current)[".materials.zip"])

    def test_report_staging_and_restore_validate_independently(self):
        fixture = self.prepare_report()
        self.produce_report(fixture)
        self.assertEqual("true", self.snapshot_result()[0]["report_ready"])
        cached = self.root / "build/lean-cache/report"
        saved = (cached / "manifest.json").read_bytes()
        hooks = self.root / "snapshot-hooks"
        hooks.mkdir()
        (hooks / "sitecustomize.py").write_text('''
import pathlib, shutil
copy = shutil.copyfile
def damaged(source, target, *args, **kwargs):
    result = copy(source, target, *args, **kwargs)
    path = pathlib.Path(target)
    if any(part.startswith(".snapshot-") for part in path.parts) and path.name.endswith(".materials.zip"):
        path.write_bytes(b"damaged staging copy")
    return result
shutil.copyfile = damaged
''')
        with mock.patch.dict(self.env, PYTHONPATH=str(hooks)):
            readiness, receipts = self.snapshot_result()
        self.assertEqual("false", readiness["report_ready"], receipts)
        self.assertEqual("save-failed", receipts["report"]["status"])
        self.assertEqual(saved, (cached / "manifest.json").read_bytes())
        self.assertFalse(list(cached.parent.glob(".snapshot-*")))
        report = next((cached / "data").glob("*/*/*/raw-lean-report.json"))
        bundle = fixture.bundle_bytes(report)
        for case in ("missing", "materials", "partition"):
            with self.subTest(case=case):
                manifest = json.loads(saved)
                if case == "missing": report.unlink()
                elif case == "materials": pathlib.Path(str(report) + ".materials.zip").write_bytes(b"corrupt")
                else:
                    path = pathlib.Path(str(report) + ".seed.json")
                    seed = json.loads(path.read_text())
                    seed["partition"] = seed["partition"].replace(REV, "f" * 40)
                    path.write_text(json.dumps(seed))
                    for item in manifest["files"]:
                        item["sha256"] = hashlib.sha256((cached / "data" / item["path"]).read_bytes()).hexdigest()
                (cached / "manifest.json").write_text(json.dumps(manifest))
                shutil.rmtree(fixture.cache, ignore_errors=True)
                restored = self.run_tool(CACHE, "restore", "--report-key", manifest["key"])
                self.assertEqual(0, restored.returncode, restored.stdout + restored.stderr)
                self.assertIn('"status": "miss"', restored.stdout)
                self.assertEqual([], fixture.seeds())
                fixture.write_bundle_bytes(report, bundle)
        (cached / "manifest.json").write_bytes(saved)

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

    def test_invalid_dependency_links_disable_only_that_save_with_an_offending_path(self):
        fixture = self.prepare_report()
        self.produce_report(fixture)
        source, _ = self.dependency_files()
        for target in (".lake/build",):
            directory = self.root / target
            directory.mkdir(parents=True)
            (directory / "fixture").write_bytes(b"other layer bytes")
        readiness, _ = self.snapshot_result()
        self.assertEqual({layer + "_ready": "true" for layer in ("dependency", "project", "report")}, readiness)
        cached = self.root / "build/lean-cache/dependency"
        outside = self.root / "outside"
        outside.write_bytes(b"outside must stay private")
        # The same relative escape also lands on an existing file from staging.
        staged_outside = cached.parent / "outside"
        staged_outside.write_bytes(b"outside staging must stay private")
        cases = {
            "escape": "../../../../outside",
            "absolute": str(outside),
            "broken": "missing",
            "self-cycle": "bad-link",
            "chain-cycle": "cycle-peer",
            "directory": "..",
        }
        link = source / "batteries/docs/bad-link"
        link.parent.mkdir()
        peer = link.with_name("cycle-peer")
        for name, target in cases.items():
            before = (cached / "manifest.json").read_bytes()
            with self.subTest(link=name):
                link.symlink_to(target)
                if name == "chain-cycle":
                    peer.symlink_to("bad-link")
                try:
                    readiness, receipts = self.snapshot_result()
                    self.assertEqual({"dependency_ready": "false", "project_ready": "true", "report_ready": "true"},
                                     readiness, receipts)
                    self.assertEqual("save-failed", receipts["dependency"]["status"])
                    self.assertIn("batteries/docs/bad-link", receipts["dependency"]["reason"])
                    self.assertEqual(before, (cached / "manifest.json").read_bytes())
                    self.assertEqual(target, os.readlink(link))
                    self.assertEqual(b"outside must stay private", outside.read_bytes())
                    self.assertEqual(b"outside staging must stay private", staged_outside.read_bytes())
                    self.assertFalse(list(cached.parent.glob(".snapshot-*")))
                finally:
                    link.unlink()
                    peer.unlink(missing_ok=True)

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

    def test_snapshot_readiness_and_material_follow_writer_permissions(self):
        fixture = self.prepare_report()
        current = self.produce_report(fixture)
        self.env.update(GITHUB_RUN_ID="34362630774", GITHUB_RUN_ATTEMPT="1")
        self.write_handoff(fixture)
        material = {
            "dependency": (".lake/packages", "mathlib/Mathlib.olean", b"private dependency seed\n"),
            "project": (".lake/build", "lib/Module.olean", b"private project seed\n"),
        }
        layers = (*material, "report")
        for target, relative, data in material.values():
            path = self.root / target / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
            path.chmod(0o640)
        system, machine = platform.system().lower(), platform.machine().lower()
        architecture = {"aarch64": "arm64", "x86_64": "x64", "amd64": "x64"}.get(machine, machine)
        partition = f"{REV}/{system}-{architecture}"
        cases = [
            ("dev_push", "push", "refs/heads/dev", "true", "true", True),
            ("dev_pr_target", "pull_request_target", "refs/heads/dev", "true", "true", False),
            ("pr_merge", "pull_request", "refs/pull/7/merge", "true", "true", False),
            ("dev_dispatch", "workflow_dispatch", "refs/heads/dev", "true", "true", False),
            ("dev_writes_false", "push", "refs/heads/dev", "false", "true", False),
            ("dev_check_failed", "push", "refs/heads/dev", "true", "false", False),
            ("dev_check_missing", "push", "refs/heads/dev", "true", None, False),
            ("other_branch", "push", "refs/heads/topic", "true", "true", False),
            ("other_integration", "push", "refs/heads/integration-ci-other-tests", "true", "true", False),
        ]
        # Integration-only rollout data: exclude this block from dev delivery.
        integration = "integration-ci-current-stability-0909-tests"
        cases += [
            ("integration_push", "push", f"refs/heads/{integration}", "true", "true", True),
            ("integration_pr_target", "pull_request_target", f"refs/heads/{integration}", "true", "true", False),
            ("integration_pr", "pull_request", f"refs/heads/{integration}", "true", "true", False),
            ("integration_dispatch", "workflow_dispatch", f"refs/heads/{integration}", "true", "true", False),
            ("integration_writes_false", "push", f"refs/heads/{integration}", "false", "true", False),
            ("integration_check_failed", "push", f"refs/heads/{integration}", "true", "false", False),
            ("integration_check_missing", "push", f"refs/heads/{integration}", "true", None, False),
            ("integration_suffix", "push", f"refs/heads/{integration}-other", "true", "true", False),
            ("integration_tag", "push", f"refs/tags/{integration}", "true", "true", False),
        ]
        # End integration-only rollout data.
        for name, event, ref, writes, success, allowed in cases:
            with self.subTest(case=name):
                cache = self.root / "build/lean-cache"
                if cache.exists():
                    shutil.rmtree(cache)
                output = self.root / "outputs"
                output.unlink(missing_ok=True)
                env = dict(self.env, GITHUB_RUN_ID="34362630774", GITHUB_RUN_ATTEMPT="1",
                           GITHUB_EVENT_NAME=event, GITHUB_REF=ref, STRATALINT_CACHE_WRITES=writes)
                env.pop("STRATALINT_CHECK_SUCCEEDED", None)
                if success is not None:
                    env["STRATALINT_CHECK_SUCCEEDED"] = success
                result = self.run_tool(CACHE, "snapshot", env=env)
                self.assertEqual(0, result.returncode, result.stdout + result.stderr)
                self.assertEqual({layer + "_ready": str(allowed).lower() for layer in layers},
                                 dict(line.split("=", 1) for line in output.read_text().splitlines()), result.stdout)
                receipts = [json.loads(line.removeprefix("LEAN_ACTIONS_CACHE "))
                            for line in result.stdout.splitlines() if line.startswith("LEAN_ACTIONS_CACHE ")]
                self.assertEqual({layer: "snapshot" if allowed else "save-disabled" for layer in layers},
                                 {receipt["layer"]: receipt["status"] for receipt in receipts})
                if not allowed:
                    self.assertFalse(cache.exists())
                    continue
                self.assertEqual(fixture.bundle_bytes(current), fixture.bundle_bytes(
                    cache / "report/data" / current.relative_to(fixture.cache)))
                for layer, (target, relative, data) in material.items():
                    staged = cache / layer
                    self.assertEqual(data, (staged / "data" / relative).read_bytes())
                    self.assertEqual(data, (self.root / target / relative).read_bytes())
                    self.assertEqual({
                        "schema": "lean-actions-seed-v1", "partition": partition, "layer": layer,
                        "key": f"lean-{layer}-v3-{REV}-{system}-{architecture}-34362630774-1",
                        "files": [{"path": relative, "sha256": hashlib.sha256(data).hexdigest(), "mode": 0o640}],
                    }, json.loads((staged / "manifest.json").read_text()))


if __name__ == "__main__":
    unittest.main()
