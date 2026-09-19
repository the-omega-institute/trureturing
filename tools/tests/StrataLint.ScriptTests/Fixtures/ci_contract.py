"""Candidate resolution, legacy callers, and optional Actions seed contracts."""
import importlib
import json
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

from cache_fixture import CACHE, CI, REPO, REV, CacheFixture


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
        (self.root / "Meta").mkdir(exist_ok=True)
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
        ancestor = self.commit("older than base")
        (self.root / "lake-manifest.json").write_text(json.dumps({"packages": [{"name": "mathlib", "rev": "b" * 40}]}))
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
        self.check_pr_shallow_resolution(ancestor, base, head, merge)

    def check_pr_shallow_resolution(self, ancestor, base, head, merge):
        expected_scope = json.loads((self.root / "build/ci/changes.json").read_text())
        expected_plan = json.loads((self.root / "build/ci/plan.json").read_text())
        self.assertEqual([base, head], self.git("show", "-s", "--format=%P", merge).split())
        self.assertEqual(ancestor, self.git("rev-parse", base + "^1"))
        for depth in (2, 1):
            with self.subTest(depth=depth), tempfile.TemporaryDirectory(prefix="ci-pr-shallow-") as directory:
                root = pathlib.Path(directory).resolve()

                def git(*args, check=True):
                    return subprocess.run(["git", "-C", str(root), *args], check=check,
                                          capture_output=True, text=True)

                def invoke(*args):
                    return subprocess.run([sys.executable, str(CI), *args, "--repository", str(root)],
                        env=dict(self.env, GITHUB_OUTPUT=str(root / "outputs")), capture_output=True, text=True)

                git("init", "-q")
                # file:// performs a real shallow fetch; a local clone without
                # that transport can copy the complete object store instead.
                git("-c", "protocol.file.allow=always", "fetch", "--no-tags", "--depth=" + str(depth),
                    self.root.resolve().as_uri(), merge)
                git("checkout", "--detach", "FETCH_HEAD")
                self.assertEqual("true", git("rev-parse", "--is-shallow-repository").stdout.strip())
                self.assertEqual("", git("remote").stdout.strip())
                self.assertEqual(merge, git("rev-parse", "HEAD").stdout.strip())
                self.assertNotEqual(0, git("cat-file", "-e", ancestor + "^{commit}", check=False).returncode)
                if depth == 1:
                    self.assertNotEqual(0, git("cat-file", "-e", base + "^{commit}", check=False).returncode)
                    for args in [("resolve", "--head", head),
                                 ("pr-plan", "--commit", merge, "--base", base, "--head", head)]:
                        result = invoke(*args)
                        self.assertEqual(2, result.returncode, result.stdout + result.stderr)
                    self.assertFalse((root / "outputs").exists())
                    self.assertFalse((root / "build/ci/changes.json").exists())
                    self.assertFalse((root / "build/ci/plan.json").exists())
                    continue

                for commit in (base, head, merge):
                    self.assertEqual(self.git("rev-parse", commit + "^{tree}"),
                                     git("rev-parse", commit + "^{tree}").stdout.strip())
                    for path in ("Meta/FILEMAP.toml", "lake-manifest.json"):
                        self.assertEqual(self.git("show", commit + ":" + path),
                                         git("show", commit + ":" + path).stdout.strip())
                result = invoke("resolve", "--head", head)
                self.assertEqual(0, result.returncode, result.stdout + result.stderr)
                outputs = dict(line.split("=", 1) for line in (root / "outputs").read_text().splitlines())
                self.assertEqual({"candidate_sha": merge, "base_sha": base,
                                  "no_work": str(not expected_plan["resources"]).lower()}, outputs)
                self.assertEqual("", git("remote").stdout.strip())
                self.assertEqual(expected_scope, json.loads((root / "build/ci/changes.json").read_text()))
                self.assertEqual(expected_plan, json.loads((root / "build/ci/plan.json").read_text()))
                result = invoke("validate-plan", "--commit", merge,
                    "--changes", str(root / "build/ci/changes.json"), "--plan", str(root / "build/ci/plan.json"))
                self.assertEqual(0, result.returncode, result.stdout + result.stderr)
                self.assertEqual(expected_plan, json.loads(result.stdout))
                for args in [("resolve", "--head", base),
                             ("pr-plan", "--commit", merge, "--base", head, "--head", head),
                             ("pr-plan", "--commit", merge, "--base", base, "--head", base)]:
                    result = invoke(*args)
                    self.assertEqual(2, result.returncode, result.stdout + result.stderr)
                self.assertEqual(expected_scope, json.loads((root / "build/ci/changes.json").read_text()))
                self.assertEqual(expected_plan, json.loads((root / "build/ci/plan.json").read_text()))

    def test_resolver_reads_schema_two_filemap_only_for_the_immutable_base(self):
        legacy = '''schema_version = 2
[residence_policy]
case_id = "fixture"
desired = "registered"
known_violation_count = 0
status = "compliant"
[[files]]
pattern = "**"
kind = "data"
admission_plane = "content"
produced_by = "none"
consumed_by = ["fixture"]
verified_by = ["fixture"]
artifact_id = "none"
runtime_disposition = "committed-source"
'''
        prefix, row = legacy.split("[[files]]", 1)
        resources = '''resources = [
{ id = "filemap", stage = "current", owner = "Meta/FILEMAP.toml", prerequisites = [], tools = [], cache_layers = [], cache_activation = {}, materials = ["Meta/ci-checks.json", "Meta/ci-resources.json", "Meta/engineering-projects.json"] },
{ id = "lean", stage = "current", owner = "Meta/FILEMAP.toml", prerequisites = [], tools = [], cache_layers = [], cache_activation = {}, materials = ["Meta/ci-checks.json", "Meta/ci-resources.json", "Meta/engineering-projects.json"] },
]
'''
        with self.assertRaises(ValueError):
            sys.path.insert(0, str(REPO / "tools/scripts/workflow"))
            importlib.import_module("ci_plan").load_filemap(legacy.encode())
        for mode in ("pr", "push"):
            for change in ("delete", "rename"):
                for match_count in (0, 1, 2):
                    with self.subTest(mode=mode, change=change, match_count=match_count), \
                         tempfile.TemporaryDirectory(prefix="ci-schema-migration-") as directory:
                        root = pathlib.Path(directory).resolve()
                        def git(*args):
                            return subprocess.run(["git", "-C", str(root), *args], check=True,
                                capture_output=True, text=True).stdout.strip()
                        git("init", "-q")
                        git("config", "user.name", "Fixture")
                        git("config", "user.email", "fixture@example.invalid")
                        for folder in ("Meta", "retired", "docs"):
                            (root / folder).mkdir()
                        (root / ".gitignore").write_text("build/\nevent.json\noutputs\n")
                        (root / "Meta/FILEMAP.toml").write_text(legacy)
                        (root / "Meta/ci-resources.json").write_text(json.dumps({
                            "schema": "ci-resource-execution-v1", "resources": [
                                {"id": name, "projects": [], "checks": [], "steps": [name]}
                                for name in ("filemap", "lean")]}))
                        (root / "Meta/engineering-projects.json").write_text('{"projects":[]}')
                        (root / "Meta/ci-checks.json").write_text('{"checks":[]}')
                        old = root / "retired/old.txt"
                        old.write_text("registered retired input\n")
                        git("add", ".")
                        git("commit", "-qm", "schema two base")
                        base = git("rev-parse", "HEAD")
                        if change == "delete": old.unlink()
                        else: old.rename(root / "docs/renamed.md")
                        patterns = ["*", "Meta/**", "docs/**", *("retired/*", "retired/old.txt")[:match_count]]
                        current = prefix.replace("schema_version = 2\n", "schema_version = 4\n" + resources)
                        for pattern in patterns:
                            require = '["filemap"]' if pattern.startswith("retired/") else "[]"
                            current += "[[files]]" + row.replace('pattern = "**"',
                                'pattern = "' + pattern + '"\nrequire = ' + require)
                        (root / "Meta/FILEMAP.toml").write_text(current)
                        git("add", "-A")
                        git("commit", "-qm", "schema four candidate")
                        head = git("rev-parse", "HEAD")
                        env = dict(self.env, GITHUB_EVENT_NAME="pull_request" if mode == "pr" else "push",
                                   GITHUB_OUTPUT=str(root / "outputs"), GITHUB_EVENT_PATH=str(root / "event.json"))
                        if mode == "pr":
                            merge = git("commit-tree", "HEAD^{tree}", "-p", base, "-p", head, "-m", "merge")
                            git("checkout", "--detach", merge)
                            env["GITHUB_SHA"] = merge
                            arguments = ["resolve", "--head", head]
                        else:
                            (root / "event.json").write_text(json.dumps({"before": base, "after": head}))
                            env["GITHUB_SHA"] = head
                            arguments = ["push-plan", "--commit", head]
                        result = subprocess.run([sys.executable, str(CI), *arguments, "--repository", str(root)],
                                                env=env, capture_output=True, text=True)
                        changes = json.loads((root / "build/ci/changes.json").read_text())["changes"]
                        retired_change = next(item for item in changes if item["old"]["path"] == "retired/old.txt")
                        self.assertEqual("D" if change == "delete" else "R", retired_change["status"])
                        plan_path = root / "build/ci/plan.json"
                        if match_count != 1:
                            self.assertEqual(2, result.returncode, result.stdout + result.stderr)
                            self.assertIn(f"retired/old.txt: FILEMAP match count {match_count}", result.stderr)
                            self.assertFalse(plan_path.exists())
                            continue
                        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
                        plan = json.loads(plan_path.read_text())
                        self.assertEqual(["filemap"], plan["declared_require"])
                        self.assertEqual(["filemap"], plan["resources"])
                        self.assertEqual(["filemap"], plan["execution"]["steps"])
                        self.assertEqual(base if mode == "pr" else None, plan["base"])
                        retired = next(item for item in plan["paths"] if item["path"] == "retired/old.txt")
                        self.assertEqual("**", retired["pattern"])
                        self.assertEqual(["filemap"], retired["require"])

    def test_parentless_checkout_needs_no_base_or_remote(self):
        self.git("init", "-q")
        commit = self.commit("parentless")
        result = self.run_tool(CI, "checkout", "--commit", commit)
        self.assertEqual(0, result.returncode, result.stderr)
        self.env["GITHUB_SHA"] = commit
        self.assertNotEqual(0, self.run_tool(CI, "resolve", "--head", commit).returncode)
        self.assertNotEqual(0, self.run_tool(CI, "checkout", "--commit", "b" * 40).returncode)

    def test_filemap_include_rows_and_bytes_bind_the_plan_identity(self):
        sys.path.insert(0, str(REPO / "tools/scripts/workflow"))
        planner = importlib.import_module("ci_plan")
        root = (REPO / planner.FILEMAP).read_bytes()
        fragment_path = "Meta/FILEMAP.docs.reports.toml"
        fragment = (REPO / fragment_path).read_bytes()
        documents = []

        manifest = planner.load_filemap(root, lambda path: fragment if path == fragment_path else None, documents)

        self.assertTrue(any(row["pattern"] == "docs/reports/**/*.json" for row in manifest["files"]))
        original = planner.filemap_digest(documents)
        changed = []
        planner.load_filemap(root, lambda path: fragment + b"# identity change\n" if path == fragment_path else None, changed)
        self.assertNotEqual(original, planner.filemap_digest(changed))
        with self.assertRaisesRegex(ValueError, "same candidate snapshot"):
            planner.load_filemap(root)

        delegated_root = b'''schema_version = 4
include = ["FILEMAP.fixture.toml"]
resources = []
[residence_policy]
case_id = "RESIDENCE-FIXTURE"
desired = "registered"
known_violation_count = 0
status = "compliant"
'''
        delegated_fragment = b'''schema_version = 4
[[files]]
pattern = "fixture/**"
require = []
kind = "data"
admission_plane = "content"
produced_by = "none"
consumed_by = ["fixture"]
verified_by = ["fixture"]
artifact_id = "none"
runtime_disposition = "committed-source"
'''
        delegated = planner.load_filemap(delegated_root,
            lambda path: delegated_fragment if path == "Meta/FILEMAP.fixture.toml" else None)
        self.assertEqual(["fixture/**"], [row["pattern"] for row in delegated["files"]])

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
        self.assertEqual(self.root / ".lake/build", cached)
        self.assertIn("project_ready=true", result.stdout)
        return cached, keys["project_key"]

    def production(self, key, failure=False, outcome="success"):
        (self.root / "Makefile").write_text("current:\n\t@echo producer >> calls\n\t@exit " + ("7" if failure else "0") + "\n")
        return subprocess.run(["bash", "-euc", '"$PYTHON" "$CACHE" restore --repository "$ROOT" --project-key "$KEY" --project-outcome "$OUTCOME"; make -C "$ROOT" current'],
            env=dict(self.env, PYTHON=sys.executable, CACHE=str(CACHE), ROOT=str(self.root), KEY=key, OUTCOME=outcome),
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
        (cached / "lib/Module.olean").write_bytes(b"partial archive")
        result = self.production(key, outcome="failure")
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
        shutil.rmtree(self.root / "build/lean-cache", ignore_errors=True)
        (self.root / "build/lean-cache").parent.mkdir(exist_ok=True)
        (self.root / "build/lean-cache").write_text("unwritable cache path")
        result = self.run_tool(CACHE, "snapshot")
        self.assertEqual(0, result.returncode, result.stderr)
        self.assertNotIn("project_ready=true", result.stdout)

    def test_missing_restored_directory_cannot_stop_normal_production(self):
        cached, key = self.seed()
        shutil.rmtree(cached)
        result = self.production(key)
        self.assertEqual(0, result.returncode, result.stderr)
        self.assertEqual("producer\n", (self.root / "calls").read_text())
        self.assertIn("STRATALINT_ACTIONS_CACHE_SEEDED=0", result.stdout)

    def test_pull_request_cannot_publish_snapshot(self):
        (self.root / ".lake/build").mkdir(parents=True)
        (self.root / ".lake/build/output").write_text("project")
        self.dependency_files()
        for event, ref in (("pull_request", "refs/pull/42/merge"), ("pull_request_target", "refs/heads/dev")):
            with self.subTest(event=event):
                shutil.rmtree(self.root / "build/lean-cache", ignore_errors=True)
                result = self.run_tool(CACHE, "snapshot", env=dict(self.env, GITHUB_EVENT_NAME=event,
                    GITHUB_REF=ref, GITHUB_SHA="a" * 40, CANDIDATE_SHA="a" * 40, STRATALINT_CACHE_WRITES="true"))
                self.assertEqual(0, result.returncode, result.stdout + result.stderr)
                for layer in ("dependency", "project"):
                    self.assertIn(layer + "_ready=false", result.stdout)
                    self.assertFalse((self.root / "build/lean-cache" / layer / "manifest.json").exists())

    def test_pull_request_restores_seed_with_writes_disabled(self):
        _, key = self.seed()
        self.env.update(GITHUB_EVENT_NAME="pull_request", GITHUB_REF="refs/pull/42/merge",
                        GITHUB_SHA="a" * 40, CANDIDATE_SHA="a" * 40, STRATALINT_CACHE_WRITES="false")
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
            run_id="17", run_attempt="2", archive=self.root / "stage.tar.gz", seed_archive=None, checks_seed_archive=None)
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
            args.command = "pack"
            for stage, writable, explicit in (("current", "true", False), ("current", "false", False),
                                               ("engineering", "true", False), ("current", "false", True)):
                with self.subTest(stage=stage, writable=writable, explicit=explicit):
                    args.stage = stage
                    args.seed_archive = self.root / "explicit-seed.tgz" if explicit else None
                    os.environ["STRATALINT_CACHE_WRITES"] = writable
                    owner.transport(args)
                    command = calls[-1][0]
                    expected = args.seed_archive or (self.root / "ci-current-seed.tar.gz"
                        if stage == "current" and writable == "true" else None)
                    self.assertEqual(expected is not None, "--seed-archive" in command)
                    if expected is not None:
                        self.assertEqual(str(expected), command[command.index("--seed-archive") + 1])
            planner = importlib.import_module("ci_plan")
            args.stage, args.seed_archive = "current", None
            for profiles in (["checks"], ["current"], ["checks", "current"]):
                with self.subTest(profiles=profiles), \
                     mock.patch.dict(os.environ, dict(STRATALINT_CACHE_WRITES="true",
                        CI_PLAN_PATH="build/ci/plan.json", CI_CHANGES_PATH="build/ci/changes.json")), \
                     mock.patch.object(planner, "validate_plan", return_value={}), \
                     mock.patch.object(planner, "stage_requirements", return_value={"cache_layers": profiles}):
                    owner.transport(args)
                    command = calls[-1][0]
                    self.assertEqual("current" in profiles, "--seed-archive" in command)
                    self.assertEqual("checks" in profiles, "--checks-seed-archive" in command)
                    if "checks" in profiles:
                        self.assertEqual(str(self.root / "ci-checks-seed.tar.gz"), command[command.index("--checks-seed-archive") + 1])
            with mock.patch.object(owner.subprocess, "run", side_effect=subprocess.CalledProcessError(1, "dotnet")):
                with self.assertRaises(subprocess.CalledProcessError):
                    owner.transport(args)
        self.assertEqual(10, len(calls))


if __name__ == "__main__":
    unittest.main()
