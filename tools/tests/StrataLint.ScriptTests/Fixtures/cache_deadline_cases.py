"""Cache deadlines use explicit job metadata and an injected clock."""
import importlib.util
import json
import pathlib
import subprocess
from datetime import datetime, timezone

from lean_seed_support import ROOT


class CacheDeadlineCases:
    def deadline_owner(self):
        path = ROOT / "tools/scripts/worktree/cache_deadline.py"
        spec = importlib.util.spec_from_file_location("cache_deadline_contract", path)
        owner = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(owner)
        return owner

    def deadline_fixture(self):
        owner = self.deadline_owner()
        env = {"GITHUB_EVENT_NAME": "push", "STRATALINT_CACHE_WRITES": "true",
               "GITHUB_REPOSITORY": "fixture/project", "GITHUB_RUN_ID": "123",
               "GITHUB_RUN_ATTEMPT": "2", "GITHUB_JOB": "current",
               "GITHUB_SHA": "a" * 40, "CANDIDATE_SHA": "a" * 40,
               "RUNNER_NAME": "fixture-runner"}
        epoch = 1800000000
        clock = [100.0]
        jobs = {"total_count": 1, "jobs": [{"id": 77, "name": "current", "run_id": 123,
                "run_attempt": 2, "head_sha": "a" * 40, "status": "in_progress",
                "runner_name": "fixture-runner", "started_at": datetime.fromtimestamp(
                    epoch - 2300, timezone.utc).isoformat().replace("+00:00", "Z")}]}
        calls = []
        def fetch(*arguments):
            calls.append(arguments)
            return jobs
        return owner, env, epoch, clock, jobs, calls, fetch

    def test_cache_deadline_is_shared_by_later_layers_and_reserves_save_and_cleanup(self):
        owner, env, epoch, clock, jobs, calls, fetch = self.deadline_fixture()
        first = owner.begin(self.root, "current", 45, env=env, fetch_jobs=fetch,
                            now=lambda: epoch, monotonic=lambda: clock[0])
        self.assertEqual(1, len(calls))
        self.assertEqual(215, first.snapshot_seconds())
        self.assertEqual(4, first.save_timeout_minutes())
        clock[0] += 120
        later = owner.load_deadline(self.root, "current", env=env, monotonic=lambda: clock[0])
        self.assertEqual(95, later.snapshot_seconds())
        self.assertEqual(2, later.save_timeout_minutes())
        self.assertEqual(1, len(calls))
        clock[0] += 160
        self.assertEqual(0, later.snapshot_seconds())
        self.assertEqual(0, later.save_timeout_minutes())

    def test_cache_deadline_checks_exact_run_attempt_candidate_and_job(self):
        for key, value in (("name", "engineering"), ("run_id", 124), ("run_attempt", 1),
                           ("head_sha", "b" * 40), ("status", "completed"),
                           ("runner_name", "other-runner"), ("started_at", "tomorrow")):
            with self.subTest(key=key):
                owner, env, epoch, clock, jobs, calls, fetch = self.deadline_fixture()
                jobs["jobs"][0][key] = value
                result = owner.begin(self.root, "current", 45, env=env, fetch_jobs=fetch,
                                     now=lambda: epoch, monotonic=lambda: clock[0])
                self.assertEqual(0, result.snapshot_seconds())
                self.assertEqual(0, result.save_timeout_minutes())

    def test_cache_deadline_duplicate_or_incomplete_job_response_disables_saves(self):
        for defect in ("duplicate", "incomplete", "not-object"):
            owner, env, epoch, clock, jobs, calls, fetch = self.deadline_fixture()
            if defect == "duplicate":
                jobs["jobs"] *= 2
                jobs["total_count"] = 2
            elif defect == "incomplete": jobs["total_count"] = 2
            else: fetch = lambda *_: []
            result = owner.begin(self.root, "current", 45, env=env, fetch_jobs=fetch,
                                 now=lambda: epoch, monotonic=lambda: clock[0])
            self.assertEqual(0, result.save_timeout_minutes())

    def test_cache_deadline_disabled_or_mismatched_context_never_requests_metadata(self):
        for key, value in (("GITHUB_EVENT_NAME", "pull_request"), ("STRATALINT_CACHE_WRITES", "false"),
                           ("CANDIDATE_SHA", "b" * 40), ("GITHUB_JOB", "other"),
                           ("GITHUB_RUN_ATTEMPT", "0")):
            owner, env, epoch, clock, jobs, calls, fetch = self.deadline_fixture()
            env[key] = value
            result = owner.begin(self.root, "current", 45, env=env, fetch_jobs=fetch,
                                 now=lambda: epoch, monotonic=lambda: clock[0])
            self.assertEqual([], calls)
            self.assertEqual(0, result.save_timeout_minutes())

    def test_cache_deadline_failed_metadata_cannot_reuse_an_old_window(self):
        owner, env, epoch, clock, jobs, calls, fetch = self.deadline_fixture()
        owner.begin(self.root, "current", 45, env=env, fetch_jobs=fetch,
                    now=lambda: epoch, monotonic=lambda: clock[0])
        def unavailable(*_):
            raise subprocess.TimeoutExpired(["gh", "api"], 15)
        failed = owner.begin(self.root, "current", 45, env=env, fetch_jobs=unavailable,
                             now=lambda: epoch, monotonic=lambda: clock[0])
        self.assertEqual(0, failed.snapshot_seconds())
        self.assertEqual(0, owner.load_deadline(self.root, "current", env=env,
                                              monotonic=lambda: clock[0]).save_timeout_minutes())

    def test_cache_deadline_foreign_or_corrupt_state_does_not_enable_saves(self):
        owner, env, epoch, clock, jobs, calls, fetch = self.deadline_fixture()
        owner.begin(self.root, "current", 45, env=env, fetch_jobs=fetch,
                    now=lambda: epoch, monotonic=lambda: clock[0])
        for key, value in (("GITHUB_RUN_ID", "124"), ("GITHUB_RUN_ATTEMPT", "3"),
                           ("CANDIDATE_SHA", "b" * 40), ("RUNNER_NAME", "other-runner")):
            self.assertEqual(0, owner.load_deadline(self.root, "current", env={**env, key: value},
                             monotonic=lambda: clock[0]).save_timeout_minutes())
        path = self.root / "build/ci/cache-deadline-current.json"
        original = json.loads(path.read_text())
        for key, value in (("started_at", False), ("cutoff_monotonic", "later"),
                           ("sampled_monotonic", float("nan")), ("job_timeout_minutes", 46)):
            path.write_text(json.dumps({**original, key: value}))
            self.assertEqual(0, owner.load_deadline(self.root, "current", env=env,
                             monotonic=lambda: clock[0]).save_timeout_minutes())
        path.write_text("broken")
        self.assertEqual(0, owner.load_deadline(self.root, "current", env=env,
                         monotonic=lambda: clock[0]).save_timeout_minutes())

    def test_cache_deadline_save_minute_rounding_has_no_zero_timeout_output(self):
        owner, env, epoch, clock, jobs, calls, fetch = self.deadline_fixture()
        window = owner.begin(self.root, "current", 45, env=env, fetch_jobs=fetch,
                             now=lambda: epoch, monotonic=lambda: clock[0])
        self.assertEqual(1, window.save_timeout_minutes(maximum=1))
        clock[0] += 215
        self.assertEqual(0, window.snapshot_seconds())
        self.assertEqual({"save_allowed": True, "save_timeout_minutes": 1}, owner.save_outputs(window))
        clock[0] += 1
        self.assertEqual({"save_allowed": False, "save_timeout_minutes": 1}, owner.save_outputs(window))

    def test_cache_deadline_metadata_transport_is_bounded_and_does_not_log_tokens(self):
        owner = self.deadline_owner()
        calls = []
        def run(command, **kwargs):
            calls.append((command, kwargs))
            return subprocess.CompletedProcess(command, 0, '{"jobs":[],"total_count":0}')
        env = {"GH_TOKEN": "private-token"}
        owner.query_jobs("fixture/project", "123", "2", env, run=run)
        command, options = calls[0]
        self.assertEqual(15, options["timeout"])
        self.assertNotIn("private-token", str(command))
        self.assertNotIn("shell", options)
        self.assertIn("/attempts/2/jobs?per_page=100", command[-1])
