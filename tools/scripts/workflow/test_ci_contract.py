"""Behavioral endpoint parity against real Git candidate bytes and unit declarations."""
import copy
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).parent))
import ci_contract as contract

ROOT = Path(__file__).resolve().parents[3]


class ContractTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="ci parity ")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.env = dict(os.environ, GIT_AUTHOR_NAME="fixture", GIT_AUTHOR_EMAIL="fixture@example.com",
                        GIT_COMMITTER_NAME="fixture", GIT_COMMITTER_EMAIL="fixture@example.com", PYTHONDONTWRITEBYTECODE="1")
        self.git("init", "-q", "-b", "fixture")
        for relative in ("Meta/ci-units.json", "Makefile", "tools/scripts/local-harness-gate.sh"):
            self.put(relative, (ROOT / relative).read_bytes())
        shutil.copytree(ROOT / "tools/scripts/workflow", self.root / "tools/scripts/workflow", dirs_exist_ok=True,
                        ignore=shutil.ignore_patterns("__pycache__"))
        self.put("D5/old name\nsource.lean", b"theorem old : True := trivial\n")
        self.git("add", ".")
        self.git("commit", "-qm", "fixture base")
        self.base = self.git("rev-parse", "HEAD").strip()

    def git(self, *args):
        return subprocess.check_output(["git", "-C", str(self.root), *args], env=self.env).decode()

    def put(self, path, content):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(content)

    def parity(self, purpose="pull-request"):
        index = (self.root / ".git/index").read_bytes()
        refs = self.git("show-ref", "--head")
        paths = contract.changed_paths(self.root, self.base)
        data, revision = contract.load(self.root)
        expected = contract.selection(data, paths, purpose)
        local = subprocess.run(["bash", "tools/scripts/local-harness-gate.sh", "--base", self.base,
                                "--purpose", purpose, "--plan"], cwd=self.root, env=self.env,
                               capture_output=True, text=True)
        self.assertEqual(local.returncode, 0, local.stderr)
        observed = json.loads(next(line.removeprefix("CI_LOCAL ") for line in local.stdout.splitlines()
                                   if line.startswith("CI_LOCAL ")))
        self.assertEqual({key: observed[key] for key in expected}, expected)
        self.assertEqual(observed["contract_revision"], revision)
        candidate = observed["candidate"]
        self.assertEqual(index, (self.root / ".git/index").read_bytes())
        self.assertEqual(refs, self.git("show-ref", "--head"))
        # Commit packaging is irrelevant to the bytes used for comparison.
        self.git("add", ".")
        self.git("commit", "--allow-empty", "-qm", "fixture candidate")
        self.assertEqual(contract.candidate_identity(self.root), candidate)
        self.assertEqual(self.git("rev-parse", "HEAD^{tree}").strip(), candidate)
        hosted = contract.changed_paths(self.root, self.base, "HEAD")
        self.assertEqual(set(paths), set(hosted))
        with tempfile.TemporaryDirectory() as directory:
            changed = Path(directory) / "changed"
            output = Path(directory) / "output"
            contract.write_paths(changed, hosted)
            result = subprocess.run([sys.executable, "tools/scripts/workflow/ci_detect.py", "--contract",
                                     "--changed", str(changed)], cwd=self.root,
                                    env=dict(self.env, GITHUB_OUTPUT=str(output),
                                             GITHUB_EVENT_NAME="pull_request" if purpose == "pull-request" else "push"),
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            values = dict(line.split("=", 1) for line in output.read_text().splitlines())
            self.assertEqual({k: json.loads(values[k]) for k in expected}, expected)
        return expected

    def test_fib_program_selects_shared_current_consumer_and_lightweight_ack(self):
        self.put("tools/scripts/compiled-fib-test.sh", b"# changed FIB suite\n")
        plan = self.parity()
        self.assertTrue(plan["hits"]["tests-fib"])
        self.assertTrue(plan["fib-regressions"])
        data, _ = contract.load(self.root)
        self.assertEqual(data["units"]["tests-fib"]["lean"], "none")
        self.assertFalse(data["units"]["tests-fib"]["dotnet"])
        self.assertEqual(data["units"]["tests-declared-template"]["lean"], "none")

    def test_regular_owner_change_does_not_force_explicit_fib_suite(self):
        self.put("Reg/D5/NewOwner.lean", b"-- compiled Application inputs decide\n")
        plan = self.parity()
        self.assertFalse(plan["hits"]["tests-fib"])
        self.assertFalse(plan["fib-regressions"])

    def test_normal_content_uses_source_policy_without_worktree_lifecycle(self):
        self.put("Blueprint/D5/S3/Content.scribe.cs", b"// changed content\n")
        plan = self.parity()
        self.assertTrue(plan["hits"]["tests-architecture"])
        self.assertFalse(plan["hits"]["tests-worktree-contract"])
        self.assertTrue(plan["report"])
        self.assertFalse(plan["delta"])

    def test_theory_has_delta_but_no_report_or_global_checks(self):
        self.put("docs/develop/theory/Theory.md", b"# Theory\n")
        for purpose in ("pull-request", "push"):
            plan = self.parity(purpose)
            self.assertTrue(plan["theory"])
            self.assertTrue(plan["delta"])
            self.assertFalse(plan["report"])
            self.assertEqual([k for k, v in plan["hits"].items() if v], ["current", "tests-repository-filemap"])
            self.git("reset", "--soft", self.base)

    def test_real_infrastructure_keeps_behavioral_tests(self):
        self.put("tools/scripts/worktree/worktree_protocol.py", b"# infrastructure\n")
        self.assertTrue(self.parity()["hits"]["tests-worktree-contract"])

    def test_shared_compute_owner_selects_every_actual_consumer(self):
        self.put("tools/scripts/workflow/ci_compute.py", b"# changed shared compute owner\n")
        self.assertTrue(all(self.parity()["hits"].values()))

    def test_staged_rename_unstaged_deletion_untracked_nul_paths(self):
        self.git("mv", "D5/old name\nsource.lean", "D5/renamed\tfile.lean")
        self.put("D5/renamed\tfile.lean", b"theorem old : True := by trivial\n")
        self.put("docs/develop/theory/untracked\nname.md", b"# Untracked\n")
        (self.root / "tools/scripts/workflow/ci_required.py").unlink()
        paths = contract.changed_paths(self.root, self.base)
        for name in ("D5/old name\nsource.lean", "D5/renamed\tfile.lean",
                     "docs/develop/theory/untracked\nname.md", "tools/scripts/workflow/ci_required.py"):
            self.assertIn(name, paths)
        self.parity()

    def test_comparison_base_contains_files_absent_from_current_index(self):
        original = self.base
        identical = "tools/StrataLint.Cli/Admission/ProductionCliEnvironment.Source.cs"
        changed = "D5/changed name\nsource.lean"
        deleted = "docs/develop/theory/deleted name.md"
        for path in (identical, changed, deleted):
            self.put(path, b"comparison base bytes\n")
        self.git("add", ".")
        self.git("commit", "-qm", "comparison base additions")
        self.base = self.git("rev-parse", "HEAD").strip()
        self.git("reset", "--mixed", "-q", original)
        self.put(changed, b"actual changed bytes\n")
        (self.root / deleted).unlink()
        index = (self.root / ".git/index").read_bytes()
        refs = self.git("show-ref", "--head")
        self.assertEqual(set(contract.changed_paths(self.root, self.base)), {changed, deleted})
        self.assertEqual(index, (self.root / ".git/index").read_bytes())
        self.assertEqual(refs, self.git("show-ref", "--head"))
        plan = self.parity()
        self.assertFalse(plan["hits"]["tests-worktree-contract"])

    def test_staged_removal_of_ignored_tracked_file_matches_committed_candidate(self):
        retired = "tools/retired.py"
        self.put(retired, b"tracked before retirement\n")
        self.put(".gitignore", b"tools/retired.py\n")
        self.git("add", ".gitignore")
        self.git("add", "-f", retired)
        self.git("commit", "-qm", "track retired file")
        self.base = self.git("rev-parse", "HEAD").strip()

        self.git("rm", "--cached", "--", retired)
        paths = contract.changed_paths(self.root, self.base)
        self.assertEqual(paths, [retired])

        data, _ = contract.load(self.root)
        local = contract.selection(data, paths, "pull-request")
        self.git("commit", "-qm", "retire ignored file")
        candidate = contract.candidate_identity(self.root)
        self.assertEqual(self.git("rev-parse", "HEAD^{tree}").strip(), candidate)
        hosted = contract.changed_paths(self.root, self.base, "HEAD")
        self.assertEqual(hosted, paths)
        self.assertEqual(contract.selection(data, hosted, "pull-request"), local)

    @unittest.skipUnless(hasattr(os, "symlink"), "symlinks required")
    def test_unindexed_base_files_keep_mode_and_symlink_differences(self):
        original = self.base
        mode = "D5/executable name\nsource.lean"
        link = "D5/link name\nsource.lean"
        same_link = "D5/unchanged link.lean"
        changed_link = "D5/changed link.lean"
        for path in (mode, link):
            self.put(path, b"same file bytes\n")
        (self.root / same_link).symlink_to("missing target")
        (self.root / changed_link).symlink_to("original missing target")
        self.git("add", ".")
        self.git("commit", "-qm", "comparison base types")
        self.base = self.git("rev-parse", "HEAD").strip()
        self.git("reset", "--mixed", "-q", original)
        (self.root / mode).chmod(0o755)
        (self.root / link).unlink()
        (self.root / link).symlink_to("different missing target")
        (self.root / changed_link).unlink()
        (self.root / changed_link).symlink_to("new missing target")
        self.assertEqual(set(contract.changed_paths(self.root, self.base)), {mode, link, changed_link})
        self.parity()

    def test_empty_changes_differ_from_unavailable_hosted_base(self):
        data, _ = contract.load(self.root)
        self.assertFalse(any(contract.selection(data, [], "pull-request")["hits"].values()))
        self.assertTrue(all(contract.selection(data, None, "pull-request")["hits"].values()))
        self.assertFalse(contract.selection(data, None, "push")["theory"])

    def test_push_preserves_non_theory_delta_policy(self):
        self.put("D5/changed.lean", b"-- changed\n")
        data, _ = contract.load(self.root)
        paths = contract.changed_paths(self.root, self.base)
        self.assertTrue(contract.selection(data, paths, "pull-request")["delta"])
        self.assertFalse(self.parity("push")["delta"])

    def test_invalid_base_fails_and_local_keeps_remotes(self):
        self.git("remote", "add", "persistent", "https://example.invalid/repository.git")
        result = subprocess.run(["bash", "tools/scripts/local-harness-gate.sh", "--base", "does-not-exist", "--plan"],
                                cwd=self.root, env=self.env, capture_output=True, text=True)
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertIn("CI_CHECK_ERROR", result.stderr)
        self.assertEqual(self.git("remote").strip(), "persistent")

    def test_make_gate_and_host_unit_execute_same_program_and_preserve_failures(self):
        # Synthetic command unit isolates the adapter from real remote transport.
        # The real declaration's content/theory/infrastructure mapping is tested above.
        data, _ = contract.load(self.root)
        data["CI_UNITS"] = ["[current]", "unmatched/*", "[probe]", "probes/*"]
        data["units"] = {"probe": {"project": "", "command": 'bash -c \'exit "$PROBE_EXIT"\'',
                                   "dotnet": False, "lean": "none", "cache-dependency-path": ""}}
        self.put("Meta/ci-units.json", json.dumps(data).encode())
        self.git("add", ".")
        self.git("commit", "-qm", "fixture contract")
        base = self.git("rev-parse", "HEAD").strip()
        self.put("probes/input\nname", b"actual candidate bytes\n")
        self.git("remote", "add", "persistent", "https://example.invalid/repository.git")
        for raw in (0, 1, 2, 3):
            env = dict(self.env, PROBE_EXIT=str(raw))
            local = subprocess.run(["make", "gate", "BASE=" + base], cwd=self.root, env=env,
                                   capture_output=True, text=True)
            self.assertEqual(local.returncode, 0 if raw == 0 else 2, local.stderr)
            records = [json.loads(line[9:]) for line in local.stdout.splitlines() if line.startswith("CI_CHECK ")]
            probe = next(record for record in records if record["check"] == "probe")
            self.assertEqual(probe["raw_exit"], raw)
            self.assertEqual(probe["exit"], raw)
            self.assertNotEqual(probe["status"], "protected-only")
            with tempfile.TemporaryDirectory() as directory:
                budget = Path(directory) / "budget"
                budget.write_text("1800")
                hosted = subprocess.run([sys.executable, "tools/scripts/workflow/ci_checks.py", "unit", "probe"],
                                        cwd=self.root, env=dict(env, STRATALINT_CI_COMPUTE_BUDGET=str(budget)),
                                        capture_output=True, text=True)
                self.assertEqual(hosted.returncode, raw, hosted.stderr)
                self.assertEqual(json.loads(hosted.stdout.split("CI_CHECK ")[-1]), probe)
        self.assertEqual(self.git("remote").strip(), "persistent")

    def test_unknown_unit_is_infrastructure_failure(self):
        result = subprocess.run([sys.executable, "tools/scripts/workflow/ci_checks.py", "local-unit", "unknown"],
                                cwd=self.root, env=self.env, capture_output=True, text=True)
        self.assertEqual(result.returncode, 2)
        self.assertIn("unknown unit", result.stderr)

    def test_contract_rejects_unknown_fields_duplicate_members_and_unit_mismatch(self):
        data, _ = contract.load(self.root)
        for altered in (dict(data, unknown=True), dict(data, units={}),
                        dict(data, units=dict(data["units"], current=data["units"]["tests-ci-entry"])),
                        dict(data, current=dict(data["current"], unknown=True))):
            self.put("Meta/ci-units.json", json.dumps(altered).encode())
            with self.assertRaises((ValueError, TypeError)):
                contract.load(self.root)
        self.put("Meta/ci-units.json", b'{"CI_UNITS":[],"CI_UNITS":[]}')
        with self.assertRaisesRegex(ValueError, "duplicate"):
            contract.load(self.root)


if __name__ == "__main__":
    unittest.main()
