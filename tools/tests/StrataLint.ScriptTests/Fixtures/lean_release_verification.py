"""Native integration publication contracts with local Git and transport fixtures."""
import json
import pathlib
import shutil
import subprocess

from lean_seed_support import ROOT, digest, write


class ReleaseVerificationCases:
    def verification_fixture(self):
        shutil.copy2(ROOT / "Makefile", self.root / "Makefile")
        helper = "tools/scripts/workflow/source_reference.py"
        (self.root / helper).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(ROOT / helper, self.root / helper)
        for args in (["init", "-q", str(self.root)],
                     ["-C", str(self.root), "add", "Makefile", "tools", "lake-manifest.json",
                      "lean-toolchain", "lakefile.toml", "Trureturing.lean", "D5"],
                     ["-C", str(self.root), "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                      "-c", "commit.gpgsign=false", "commit", "-qm", "synthetic candidate"]):
            subprocess.run(["git", *args], check=True, capture_output=True)
        commit = subprocess.run(["git", "-C", str(self.root), "rev-parse", "HEAD"],
                                check=True, capture_output=True, text=True).stdout.strip()
        branch = "integration-cache-fixture"
        repo = "the-omega-institute/trureturing"
        self.verification_commit = commit
        self.verification_ref = "refs/heads/" + branch
        self.verification_api = {
            f"repos/{repo}/actions/runs/123/attempts/1": {
                "id": 123, "run_attempt": 1, "event": "push", "head_sha": commit,
                "head_branch": branch, "repository": {"full_name": repo}},
            f"repos/{repo}/branches/{branch}": {
                "name": branch, "protected": True, "commit": {"sha": commit}},
            f"repos/{repo}/compare/{commit}...{commit}": {
                "status": "identical", "merge_base_commit": {"sha": commit}}}
        self.verification_environment = {
            "GITHUB_ACTIONS": "true", "GITHUB_EVENT_NAME": "push", "GITHUB_REF": self.verification_ref,
            "GITHUB_SHA": commit, "GITHUB_REPOSITORY": repo,
            "FAKE_VERIFICATION_API": str(self.root / "verification-api.json"),
            "FAKE_GH_LOG": str(self.root / "gh-calls")}
        self.save_verification_api()

    def save_verification_api(self):
        write(self.root / "verification-api.json", json.dumps(self.verification_api))

    def verification(self, verb, arguments=(), **environment):
        return self.transport(verb, arguments=("--mode", "verification", "--source-ref", self.verification_ref,
            "--source-commit", self.verification_commit, *arguments),
            **{**self.verification_environment, **environment})

    def verification_calls(self):
        path = self.root / "gh-calls"
        return [json.loads(line) for line in path.read_text().splitlines()] if path.exists() else []

    def failing_git(self, operation, exit_code, stderr):
        real_git = shutil.which("git")
        script = """#!/usr/bin/env python3
import os
import sys
if len(sys.argv) > 3 and sys.argv[3] == {operation}:
    sys.stderr.write({stderr})
    raise SystemExit({exit_code})
os.execv({real_git}, [{real_git}, *sys.argv[1:]])
""".format(operation=repr(operation), stderr=repr(stderr), exit_code=exit_code,
           real_git=repr(real_git))
        path = self.root / "bin/git"
        path.write_text(script)
        path.chmod(0o755)

    def test_verification_direct_git_failures_preserve_diagnostics_and_exit_policy(self):
        (self.root / "bin/git").unlink(missing_ok=True)
        self.verification_fixture()
        for operation, exit_code in (("rev-parse", 17), ("status", 23)):
            for stderr in ("git fixture failed\nsecond line\n", ""):
                with self.subTest(operation=operation, stderr=stderr):
                    self.failing_git(operation, exit_code, stderr)
                    expected_stderr = stderr or "<empty>"
                    for verb, expected_exit in (("publish", 2), ("fetch", 1)):
                        result = self.verification(verb)
                        self.assertEqual(expected_exit, result.returncode, result.stdout + result.stderr)
                        line = next(line for line in result.stdout.splitlines()
                                     if line.startswith("LEAN_CACHE_" + verb.upper() + " "))
                        report = json.loads(line.partition(" ")[2])
                        reason = report["reason"]
                        command_tail = ([operation, "--verify", "HEAD"] if operation == "rev-parse"
                                        else [operation, "--porcelain", "--untracked-files=no"])
                        command = repr(["git", "-C", str(self.root), *command_tail])
                        self.assertIn("Command '" + command, reason)
                        self.assertIn(f"exit status {exit_code}", reason)
                        self.assertTrue(reason.endswith("stderr: " + expected_stderr), report)

    def test_verification_rejects_non_native_or_mismatched_context_before_build(self):
        self.verification_fixture()
        for changes in ({"GITHUB_ACTIONS": "false"}, {"GITHUB_EVENT_NAME": "schedule"},
                        {"GITHUB_EVENT_NAME": "pull_request"}, {"GITHUB_REF": "refs/heads/dev"},
                        {"GITHUB_SHA": "f" * 40}, {"GITHUB_RUN_ATTEMPT": "0"},
                        {"GITHUB_REPOSITORY": "other/repository"}):
            with self.subTest(changes=changes):
                result = self.verification("publish", **changes)
                self.assertNotEqual(0, result.returncode)
                self.assertIn("verification", result.stdout)
                self.assertFalse((self.root / "build-runs").exists())
                self.assertEqual([], list(self.remote.iterdir()))

    def test_verification_requires_bound_run_and_protected_source(self):
        self.verification_fixture()
        for endpoint, field, value in [
                ("actions/runs/123/attempts/1", "event", "workflow_dispatch"),
                ("actions/runs/123/attempts/1", "run_attempt", 2),
                ("actions/runs/123/attempts/1", "head_sha", "f" * 40),
                ("branches/integration-cache-fixture", "protected", False),
                (f"compare/{self.verification_commit}...{self.verification_commit}", "status", "diverged")]:
            with self.subTest(endpoint=endpoint, field=field):
                row = self.verification_api["repos/the-omega-institute/trureturing/" + endpoint]
                before = row[field]
                row[field] = value
                self.save_verification_api()
                try:
                    result = self.verification("publish")
                    self.assertNotEqual(0, result.returncode)
                    self.assertIn("verification", result.stdout)
                    self.assertFalse((self.root / "build-runs").exists())
                    self.assertEqual([], list(self.remote.iterdir()))
                finally:
                    row[field] = before
                    self.save_verification_api()

    def test_verification_roundtrip_uses_isolated_exact_tag_and_never_prunes(self):
        self.verification_fixture()
        self.assertEqual(0, self.transport("publish", "999").returncode)
        published = self.verification("publish", **self.installation_probe())
        self.assertEqual(0, published.returncode, published.stdout + published.stderr)
        receipt = json.loads(next(line.partition(" ")[2] for line in published.stdout.splitlines()
                                  if line.startswith("LEAN_CACHE_PUBLISH ")))
        tag = receipt["tag"]
        self.assertTrue(tag.startswith("lean-cache-verify-v1-"))
        self.assertTrue(tag.endswith("-123-1"))
        self.assertEqual("published", receipt["status"])
        release = json.loads((self.remote / tag / "release.json").read_text())
        manifest = json.loads((self.remote / tag / "manifest.json").read_text())
        self.assertNotEqual(self.verification_commit, release["target_commitish"])
        self.assertEqual(self.verification_commit, manifest["producer_commit_sha"])
        self.assertEqual(("123", "1", self.verification_ref), tuple(manifest[field] for field in
            ("workflow_run_id", "workflow_run_attempt", "source_ref")))
        self.assertFalse(any(event["operation"] == "copytree" for event in self.installation_events()))
        self.assertEqual(2, len(list(self.remote.iterdir())))
        self.assertFalse(any(call[:2] in (["release", "list"], ["release", "delete"])
                             for call in self.verification_calls()))
        shutil.rmtree(self.root / ".lake/build")
        fetched = self.verification("fetch", STRATALINT_ACTIONS_CACHE_SEEDED="true")
        self.assertEqual(0, fetched.returncode, fetched.stdout + fetched.stderr)
        self.assertIn('"status":"unpacked"', fetched.stdout)
        self.assertIn(tag, fetched.stdout)
        self.assertEqual("locally-produced-olean", (self.root / ".lake/build/lib/lean/D5/A.olean").read_text())
        self.assertEqual(["lean-report LEAN_REPORT=.lake/build/stratalint/raw-lean-report.json", "lean-report LEAN_REPORT=.lake/build/stratalint/raw-lean-report.json"], (self.root / "build-runs").read_text().splitlines())

    def test_verification_failure_never_falls_back_or_clobbers_tags(self):
        self.verification_fixture()
        self.assertEqual(0, self.transport("publish", "999").returncode)
        self.assertEqual(0, self.verification("publish").returncode)
        tag = next(path for path in self.remote.iterdir() if path.name.startswith("lean-cache-verify-v1-"))
        before = (tag / "manifest.json").read_bytes()
        collision = self.verification("publish")
        self.assertNotEqual(0, collision.returncode)
        self.assertEqual(before, (tag / "manifest.json").read_bytes())
        shutil.rmtree(self.root / ".lake/build")
        for damage in ("corrupt", "missing"):
            with self.subTest(damage=damage):
                if damage == "corrupt":
                    write(tag / "lean-build.tgz", "corrupt")
                else:
                    shutil.rmtree(tag)
                result = self.verification("fetch")
                self.assertNotEqual(0, result.returncode)
                self.assertIn('"status":"miss"', result.stdout)
                self.assertFalse((self.root / ".lake/build").exists())

    def test_verification_exact_lookup_errors_and_incomplete_metadata_are_nonzero(self):
        self.verification_fixture()
        partition = json.loads(self.transport("address").stdout)["partition"]
        tag = "lean-cache-verify-v1-" + partition.replace("/", "-") + "-123-1"
        valid = dict(tag_name=tag, target_commitish=self.verification_commit, draft=False)
        cases = [(json.dumps(dict(valid, draft=True)), "0"),
                 (json.dumps(valid), "0"), ('{"draft":false}', "0"),
                 ('{"message":"Forbidden","status":"403"}', "1"),
                 ('{"message":"Server error","status":"500"}', "1"), ("not-json", "1")]
        for metadata, status in cases:
            with self.subTest(metadata=metadata, status=status):
                (self.root / "gh-calls").unlink(missing_ok=True)
                result = self.verification("publish", FAKE_LOOKUP_API_JSON=metadata,
                                           FAKE_LOOKUP_API_EXIT=status)
                self.assertEqual(1, result.returncode, result.stdout + result.stderr)
                self.assertIn('"status":"failed"', result.stdout)
                self.assertNotIn('"status":"published"', result.stdout)
                self.assertNotIn('"status":"exists"', result.stdout)
                self.assertEqual([], list(self.remote.iterdir()))
                self.assertFalse(any(call[0] == "release" for call in self.verification_calls()))

    def test_verification_rejects_invalid_post_edit_confirmation(self):
        self.verification_fixture()
        partition = json.loads(self.transport("address").stdout)["partition"]
        tag = "lean-cache-verify-v1-" + partition.replace("/", "-") + "-123-1"
        for metadata, status in self.invalid_post_edit_responses(tag, self.verification_commit):
            with self.subTest(metadata=metadata, status=status):
                shutil.rmtree(self.remote)
                self.remote.mkdir()
                (self.root / "gh-calls").unlink(missing_ok=True)
                result = self.verification("publish", FAKE_POST_EDIT_API_JSON=metadata,
                                           FAKE_POST_EDIT_API_EXIT=status)
                self.assertEqual(1, result.returncode, result.stdout + result.stderr)
                self.assertIn('"status":"failed"', result.stdout)
                self.assertNotIn('"status":"published"', result.stdout)
                calls = self.verification_calls()
                self.assertEqual(2, sum(call[0] == "api" and "/releases/tags/" in call[1] for call in calls))
                self.assertFalse(any(call[:2] in (["release", "list"], ["release", "delete"]) for call in calls))

    def test_verification_upload_failure_and_real_build_failure_are_nonzero(self):
        self.verification_fixture()
        self.assertEqual(19, self.verification("publish", FAKE_BUILD_EXIT="19").returncode)
        self.assertEqual([], list(self.remote.iterdir()))
        diagnostic = "HTTP 422: fixture upload rejected\n"
        failed = self.verification("publish", FAKE_FAIL="upload", FAKE_FAIL_STDERR=diagnostic)
        self.assertNotEqual(0, failed.returncode)
        self.assertIn('"status":"failed"', failed.stdout)
        report = json.loads(next(line.removeprefix("LEAN_CACHE_PUBLISH ")
                                 for line in failed.stdout.splitlines() if line.startswith("LEAN_CACHE_PUBLISH ")))
        self.assertIn("exit status 23", report["reason"])
        self.assertTrue(report["reason"].endswith("stderr: " + diagnostic), report)
        self.assertFalse(any(call[:2] == ["release", "edit"] for call in self.verification_calls()))

    def test_verification_local_preparation_deadline_is_nonzero_before_release_creation(self):
        environment = self.preparation_deadline_probe("archive")
        self.verification_fixture()
        self.assert_preparation_stopped(self.verification("publish", **environment), 1)
        self.assertFalse(any(call[:2] == ["release", "create"] for call in self.verification_calls()))

    def test_verification_rejects_dirty_checkout_before_build(self):
        self.verification_fixture()
        write(self.root / "D5/A.lean", "def a := 2\n")
        result = self.verification("publish")
        self.assertNotEqual(0, result.returncode)
        self.assertIn("clean fixed source checkout", result.stdout)
        self.assertFalse((self.root / "build-runs").exists())
        self.assertEqual([], list(self.remote.iterdir()))

    def test_verification_post_upload_damage_cannot_report_publication_success(self):
        self.verification_fixture()
        result = self.verification("publish", FAKE_DAMAGE_AFTER_EDIT="1")
        self.assertNotEqual(0, result.returncode)
        self.assertIn('"status":"failed"', result.stdout)
        self.assertNotIn('"status":"published"', result.stdout)
        self.assertEqual(["lean-report LEAN_REPORT=.lake/build/stratalint/raw-lean-report.json"], (self.root / "build-runs").read_text().splitlines())

    def test_verification_truncated_gzip_normalizes_fetch_and_publish_failures(self):
        self.verification_fixture()
        self.assertEqual(0, self.verification("publish").returncode)
        snapshot = next(self.remote.iterdir())
        archive = snapshot / "lean-build.tgz"
        packed = archive.read_bytes()[:-8]
        archive.write_bytes(packed)
        manifest = json.loads((snapshot / "manifest.json").read_text())
        manifest.update(archive_bytes=len(packed), archive_sha256=digest(packed),
            parts=[{"name": archive.name, "bytes": len(packed), "sha256": digest(packed)}])
        write(snapshot / "manifest.json", json.dumps(manifest))
        shutil.rmtree(self.root / ".lake/build")
        result = self.verification("fetch")
        self.assertEqual(1, result.returncode, result.stdout + result.stderr)
        self.assertIn('"status":"miss"', result.stdout)
        self.assertNotIn("Traceback", result.stderr)
        self.assertFalse((self.root / ".lake/build").exists())
        shutil.rmtree(snapshot)
        write(self.root / ".lake/build/lib/lean/D5/A.olean", "locally-produced-olean")
        result = self.verification("publish", FAKE_TRUNCATE_AFTER_EDIT="1")
        self.assertEqual(1, result.returncode, result.stdout + result.stderr)
        self.assertIn('"status":"failed"', result.stdout)
        self.assertNotIn("Traceback", result.stderr)
        self.assertNotIn('"status":"published"', result.stdout)

    def test_verification_fetch_binds_source_ref_and_attempt_without_fallback(self):
        self.verification_fixture()
        self.assertEqual(0, self.verification("publish").returncode)
        shutil.rmtree(self.root / ".lake/build")
        manifest = next(self.remote.glob("*/manifest.json"))
        original = manifest.read_text()
        for field, value in (("source_ref", "refs/heads/integration-other"),
                             ("producer_commit_sha", "a" * 40), ("workflow_run_id", "124"),
                             ("workflow_run_attempt", "2")):
            with self.subTest(field=field):
                data = json.loads(original)
                data[field] = value
                write(manifest, json.dumps(data))
                result = self.verification("fetch")
                self.assertEqual(1, result.returncode, result.stdout + result.stderr)
                self.assertIn('"status":"miss"', result.stdout)
                self.assertFalse((self.root / ".lake/build").exists())
        write(manifest, original)
        result = self.verification("fetch", FAKE_MANIFEST_DIGEST="sha256:" + "0" * 64)
        self.assertEqual(1, result.returncode, result.stdout + result.stderr)
        self.assertIn("digest mismatch", result.stdout)
        self.assertFalse((self.root / ".lake/build").exists())
        write(manifest, original)
        run_api = "repos/the-omega-institute/trureturing/actions/runs/123/attempts/"
        self.verification_api[run_api + "2"] = {**self.verification_api[run_api + "1"], "run_attempt": 2}
        self.save_verification_api()
        result = self.verification("fetch", GITHUB_RUN_ATTEMPT="2")
        self.assertNotEqual(0, result.returncode)
        self.assertIn("-123-2", result.stdout)
        self.assertFalse((self.root / ".lake/build").exists())

    def test_verification_keeps_production_namespace_and_schedule_gate_unchanged(self):
        self.verification_fixture()
        self.assertEqual(0, self.verification("publish").returncode)
        default_push = self.transport("publish", **self.verification_environment)
        self.assertEqual(0, default_push.returncode, default_push.stdout + default_push.stderr)
        self.assertIn("scheduled dev producer", default_push.stdout)
        self.assertEqual(1, len(list(self.remote.iterdir())))
        shutil.rmtree(self.root / ".lake/build")
        production_fetch = self.transport("fetch")
        self.assertNotEqual(0, production_fetch.returncode)
        self.assertFalse((self.root / ".lake/build").exists())

    def test_verification_make_parameters_reach_the_same_program(self):
        self.verification_fixture()
        result = subprocess.run([shutil.which("make"), "-C", str(self.root), "lean-cache-to-github-without-mathlib",
            "LEAN_CACHE_MODE=verification", "LEAN_CACHE_SOURCE_REF=" + self.verification_ref,
            "LEAN_CACHE_SOURCE_COMMIT=" + self.verification_commit], text=True, capture_output=True,
            env=self.transport_environment(**self.verification_environment))
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertIn('"status":"published"', result.stdout)
        self.assertIn("lean-cache-verify-v1-", result.stdout)
