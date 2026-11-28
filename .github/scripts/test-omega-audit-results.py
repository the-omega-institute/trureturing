"""GitHub Actions transport fixtures for the Omega audit cache."""

import hashlib
import importlib.util
import io
import json
from pathlib import Path
import stat
import tempfile
import unittest
from unittest.mock import patch
import warnings
import zipfile


spec = importlib.util.spec_from_file_location("transport", Path(__file__).with_name("omega-audit-results.py"))
transport = importlib.util.module_from_spec(spec)
spec.loader.exec_module(transport)

FIRST = "1" * 64 + ".json"
SECOND = "2" * 64 + ".json"


def archive(members):
    with io.BytesIO() as buffer:
        with zipfile.ZipFile(buffer, "w", zipfile.ZIP_DEFLATED) as zf:
            for name, data in members:
                zf.writestr(name, data)
        return buffer.getvalue()


class FakeGitHub:
    repo_id = 42

    def __init__(self):
        self.artifacts = []
        self.metadata_calls = []
        self.downloads = []
        self.responses = {f"actions/artifacts?name={transport.NAME}&per_page=100": {"artifacts": self.artifacts}}
        self.blobs = {}
        self.branches = {"dev", "integration-omega"}

    def add(self, rows, *, branch="dev", manifest=None):
        run_id = len(self.artifacts) + 1
        sha = f"{run_id:040x}"
        expected = {"run_id": run_id, "attempt": 2, "repository_id": self.repo_id, "branch": branch, "sha": sha}
        content = archive([("producer.json", json.dumps(expected if manifest is None else manifest)), *rows])
        artifact = {"id": run_id + 100, "name": transport.NAME, "expired": False, "size_in_bytes": len(content),
                    "workflow_run": {"id": run_id, "repository_id": self.repo_id, "head_repository_id": self.repo_id,
                                     "head_branch": branch, "head_sha": sha},
                    "digest": "sha256:" + hashlib.sha256(content).hexdigest()}
        self.artifacts.append(artifact)
        run = {"id": run_id, "repository": {"id": self.repo_id}, "head_repository": {"id": self.repo_id},
               "path": transport.WORKFLOW, "head_branch": branch, "head_sha": sha, "event": "push",
               "status": "completed", "conclusion": "success", "run_attempt": 2}
        job = {"name": "omega", "run_id": run_id, "run_attempt": 2, "head_sha": sha, "status": "completed",
               "conclusion": "success", "steps": [{"name": transport.PUBLISH_STEP, "conclusion": "success"}]}
        self.responses[f"compare/{sha}...{'f' * 40}?per_page=1&page=2"] = {"status": "ahead"}
        self.responses[f"actions/runs/{run_id}"] = run
        self.responses[f"actions/runs/{run_id}/attempts/2/jobs?per_page=100"] = {"jobs": [job]}
        self.blobs[f"actions/artifacts/{run_id + 100}/zip"] = content
        return artifact, run, job

    def protected_tip(self, branch):
        return "f" * 40 if branch in self.branches else None

    def metadata(self, path):
        self.metadata_calls.append(path)
        return self.responses[path]

    def read(self, path, limit):
        self.downloads.append(path)
        return self.blobs[path]


class TransportTests(unittest.TestCase):
    def setUp(self):
        self.api = FakeGitHub()
        self.directory = Path(self.enterContext(tempfile.TemporaryDirectory()))
        self.env = {"GITHUB_EVENT_NAME": "push", "GITHUB_REF_PROTECTED": "true", "GITHUB_REF_TYPE": "branch",
                    "GITHUB_REF_NAME": "dev", "GITHUB_RUN_ID": "1", "GITHUB_RUN_ATTEMPT": "2",
                    "GITHUB_REPOSITORY_ID": "42", "GITHUB_SHA": "1" * 40}

    def restore(self, base="dev"):
        directory = Path(self.enterContext(tempfile.TemporaryDirectory(dir=self.directory)))
        transport.restore(self.api, base, directory)
        return {p.name: p.read_bytes() for p in (directory / "restored").iterdir()}

    def test_fresh_runner_combines_successful_dev_and_same_integration_batches(self):
        self.api.add([(FIRST, b"first")])
        self.api.add([(SECOND, b"second")], branch="integration-omega")
        self.api.add([("3" * 64 + ".json", b"other")], branch="integration-other")
        self.assertEqual(self.restore("integration-omega"), {FIRST: b"first", SECOND: b"second"})
        self.assertEqual(len(self.api.downloads), 2)
        self.assertEqual(self.restore("dev"), {FIRST: b"first"})

    def test_static_name_selects_historical_runs_with_one_list_request(self):
        self.api.add([(FIRST, b"result")])
        self.api.add([(FIRST, b"result")])
        self.assertEqual(self.restore(), {FIRST: b"result"})
        self.assertEqual(self.api.metadata_calls.count(f"actions/artifacts?name={transport.NAME}&per_page=100"), 1)

    def test_rejects_untrusted_artifact_run_or_job_before_download(self):
        for what, field, value in (
            ("artifact", "name", "omega-official-axioms"), ("artifact", "expired", True),
            ("artifact", "digest", ""), ("artifact", "size_in_bytes", transport.ARCHIVE_BYTES + 1),
            ("source", "repository_id", 7), ("source", "head_repository_id", 7),
            ("run", "id", 7), ("run", "repository", {"id": 7}), ("run", "head_repository", {"id": 7}),
            ("run", "event", "pull_request"), ("run", "status", "in_progress"), ("run", "conclusion", "failure"),
            ("run", "path", ".github/workflows/other.yml"), ("run", "head_sha", "0" * 40),
            ("run", "head_branch", "other"), ("run", "run_attempt", 3), ("job", "name", "other"),
            ("job", "run_id", 3), ("job", "run_attempt", 1), ("job", "head_sha", "0" * 40),
            ("job", "conclusion", "skipped"), ("job", "steps", []), ("step", "conclusion", "failure"),
        ):
            with self.subTest(layer=what, field=field, value=value):
                self.api = FakeGitHub()
                artifact, run, job = self.api.add([(FIRST, b"invalid")])
                layer = {"artifact": artifact, "source": artifact["workflow_run"], "run": run,
                         "job": job, "step": job["steps"][0]}
                layer[what][field] = value
                self.assertEqual(self.restore(), {})
                self.assertEqual(self.api.downloads, [])

    def test_batch_on_replaced_branch_history_is_a_miss(self):
        self.api.add([(FIRST, b"orphan")])
        path = next(path for path in self.api.responses if path.startswith("compare/"))
        self.api.responses[path] = {"status": "diverged"}
        self.assertEqual(self.restore(), {})
        self.assertEqual(self.api.downloads, [])

    def test_unprotected_branch_cannot_produce(self):
        self.api.add([(FIRST, b"invalid")])
        self.api.branches.clear()
        self.assertEqual(self.restore(), {})
        self.assertEqual(self.api.downloads, [])

    def test_digest_size_mismatch_stale_attempt_partial_download_and_later_good_run(self):
        a, _, _ = self.api.add([(FIRST, b"corrupt")])
        a["digest"] = "sha256:" + "0" * 64
        self.api.add([(FIRST, b"stale")], manifest={"run_id": 2, "attempt": 1})
        a, _, _ = self.api.add([(FIRST, b"truncated")])
        a["size_in_bytes"] += 1
        a, _, _ = self.api.add([(FIRST, b"error")])
        del self.api.blobs[f"actions/artifacts/{a['id']}/zip"]
        self.api.add([(SECOND, b"good")])
        self.assertEqual(self.restore(), {SECOND: b"good"})

    def test_invalid_member_discards_entire_batch_and_preserves_another(self):
        symlink = zipfile.ZipInfo(SECOND)
        symlink.create_system = 3
        symlink.external_attr = (stat.S_IFLNK | 0o777) << 16
        for bad in ["../escape.json", "/tmp/file", "subdir/", "producer.json", FIRST, symlink]:
            with self.subTest(bad=bad), warnings.catch_warnings():
                warnings.simplefilter("ignore", UserWarning)
                self.api = FakeGitHub()
                self.api.add([(FIRST, b"partial"), (bad, b"bad")])
                self.api.add([(SECOND, b"good")])
                self.assertEqual(self.restore(), {SECOND: b"good"})

    def test_bounded_inflated_members_and_count(self):
        self.api.add([(FIRST, b"a" * 500)])
        with patch.object(transport, "RECORD_BYTES", 499):
            self.assertEqual(self.restore(), {})
        with patch.object(transport, "MAX_RECORDS", 0):
            self.assertEqual(self.restore(), {})

    def test_conflicting_results_stay_misses_across_later_batches(self):
        self.api.add([(FIRST, b"one")])
        self.api.add([(FIRST, b"two"), (SECOND, b"good")])
        self.api.add([(FIRST, b"one")])
        self.assertEqual(self.restore(), {SECOND: b"good"})

    def test_prepare_only_fresh_records_and_publish_provenance(self):
        restored = self.directory / "restored"
        restored.mkdir()
        (restored / FIRST).write_bytes(b"previous")
        produced = self.directory / "produced"
        produced.mkdir()
        self.assertIsNone(transport.prepare(self.directory, self.env))
        (produced / SECOND).write_bytes(b"fresh")
        path = transport.prepare(self.directory, self.env)
        self.assertEqual({item.name for item in path.iterdir()}, {"producer.json", SECOND})
        self.assertEqual((path / SECOND).read_bytes(), b"fresh")
        self.assertEqual(json.loads((path / "producer.json").read_text()), transport.producer(self.env))
        (produced / FIRST).symlink_to(restored / FIRST)
        with self.assertRaisesRegex(ValueError, "invalid produced"):
            transport.prepare(self.directory, self.env)

    def test_no_publish_from_pr_unprotected_ref_or_tag(self):
        produced = self.directory / "produced"
        produced.mkdir()
        (produced / FIRST).write_bytes(b"record")
        for changes in ({"GITHUB_EVENT_NAME": "pull_request"}, {"GITHUB_REF_PROTECTED": "false"},
                        {"GITHUB_REF_NAME": "feature"}, {"GITHUB_REF_TYPE": "tag"}):
            with self.subTest(changes=changes):
                self.assertIsNone(transport.prepare(self.directory, self.env | changes))


if __name__ == "__main__":
    unittest.main()
