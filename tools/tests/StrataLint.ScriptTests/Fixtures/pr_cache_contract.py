"""Executable contracts for merge-bound eligibility and native artifact transport."""
import contextlib
import io
import json
import os
import subprocess
import pathlib
import shutil
import tarfile
import zipfile
import sys
import unittest
from unittest import mock

from cache_fixture import REPO, CacheFixture

sys.path.insert(0, str(REPO / "tools/scripts/worktree"))
import lean_pr_cache as producer
import lean_actions_shards as shards


class PrCacheContracts(CacheFixture, unittest.TestCase):
    def test_slow_artifact_transfer_has_no_whole_artifact_deadline(self):
        destination = self.root / "artifact.zip"
        def transfer(command, *, stdout, stderr, check, timeout=None):
            if timeout is not None and timeout < 601:
                raise subprocess.TimeoutExpired(command, timeout)
            self.assertTrue(check)
            stdout.write(b"complete streamed artifact")
        with mock.patch.object(producer.subprocess, "run", side_effect=transfer):
            producer.download("owner/repository", 81, destination)
        self.assertEqual(b"complete streamed artifact", destination.read_bytes())

    def test_native_artifact_transfer_failure_propagates(self):
        error = subprocess.CalledProcessError(23, ["gh", "api"])
        with mock.patch.object(producer.subprocess, "run", side_effect=error) as run:
            with self.assertRaises(subprocess.CalledProcessError) as caught:
                producer.download("owner/repository", 81, self.root / "artifact.zip")
        run.assert_called_once()
        self.assertIs(error, caught.exception)

    def test_native_artifact_interruption_retries_same_id_and_discards_partial_bytes(self):
        destination = self.root / "artifact.zip"
        timeout = b"read tcp runner:1234->artifact:443: read: connection timed out\n"
        attempts = []

        def transfer(command, *, stdout, stderr, check):
            attempts.append(command)
            if len(attempts) == 1:
                stdout.write(b"incomplete archive with extra bytes")
                raise subprocess.CalledProcessError(1, command, stderr=timeout)
            stdout.write(b"valid archive")

        with mock.patch.object(producer.subprocess, "run", side_effect=transfer):
            producer.download("owner/repository", 81, destination)
        self.assertEqual(2, len(attempts))
        self.assertEqual(attempts[0], attempts[1])
        self.assertEqual(b"valid archive", destination.read_bytes())

    def setUp(self):
        super().setUp()
        self.git("init", "-q")
        tree = self.git("mktree", data="")
        base = self.git("commit-tree", tree, data="base\n")
        head = self.git("commit-tree", tree, "-p", base, data="head\n")
        merge = self.git("commit-tree", tree, "-p", base, "-p", head, data="merge\n")
        self.git("update-ref", "HEAD", merge)
        self.identity = dict(repository="owner/repository", pr="12", head=head, merge=merge, base=base,
            source_run="17", source_attempt="2", target_ref="refs/heads/integration-cache-tests")
        self.event = dict(action="labeled", label=dict(name="lean-cache-produce"), number=12,
            pull_request=dict(head=dict(sha=head), base=dict(ref="integration-cache-tests"),
                              labels=[dict(name="lean-cache-produce")]))
        self.event_file = self.root / "event.json"
        self.event_file.write_text(json.dumps(self.event))
        self.env.update(GITHUB_EVENT_NAME="pull_request", GITHUB_REF="refs/pull/12/merge", GITHUB_SHA=merge,
                        GITHUB_REPOSITORY="owner/repository", GITHUB_EVENT_PATH=str(self.event_file))
        self.runtime_sha = "d" * 40
        self.calls = []
        self.pr = dict(number=12, state="open", merged=False, merge_commit_sha=None, merged_at=None,
                       labels=[dict(name="lean-cache-produce")],
                       head=dict(sha=head), base=dict(ref="integration-cache-tests", repo=dict(full_name="owner/repository")))
        self.actual_merge = self.git("commit-tree", tree, "-p", base, "-p", head, data="actual merged commit\n")
        self.artifact = dict(id=81, name=producer.artifact_name(self.identity), expired=False,
                             created_at="2026-01-01T01:00:00Z", workflow_run=dict(id=28, head_sha=self.runtime_sha))
        self.artifacts = [self.artifact]
        self.producer_run = dict(id=28, run_attempt=1, event="workflow_dispatch", head_sha=self.runtime_sha,
            path=".github/workflows/lean-cache-publish.yml", head_branch="integration-cache-tests",
            status="completed", conclusion="success", run_started_at="2026-01-01T00:00:00Z", updated_at="2026-01-01T02:00:00Z")

    def git(self, *args, data=None):
        env = dict(os.environ, GIT_AUTHOR_NAME="Fixture", GIT_COMMITTER_NAME="Fixture",
                   GIT_AUTHOR_EMAIL="fixture@example.test", GIT_COMMITTER_EMAIL="fixture@example.test")
        return subprocess.run(["git", "-C", str(self.root), *args], input=data, env=env,
                              text=True, capture_output=True, check=True).stdout.strip()

    def runtime(self):
        return dict(self.env, GITHUB_EVENT_NAME="workflow_dispatch", GITHUB_REF=self.identity["target_ref"],
                    GITHUB_SHA=self.runtime_sha, GITHUB_WORKFLOW_SHA=self.runtime_sha,
                    GITHUB_WORKFLOW_REF="owner/repository/.github/workflows/lean-cache-publish.yml@" + self.identity["target_ref"],
                    GITHUB_RUN_ID="28", GITHUB_RUN_ATTEMPT="1", PR_SOURCE=json.dumps(self.identity),
                    SOURCE_REF=self.identity["target_ref"], SOURCE_SHA=self.identity["merge"])

    def api(self, repository, path, body=None):
        self.assertEqual("owner/repository", repository)
        self.calls.append((path, body))
        if path.startswith("branches/"):
            return dict(protected=True, commit=dict(sha="c" * 40))
        if path.startswith("compare/"):
            self.assertNotIn(self.identity["merge"], path, "M must never be required to be a target ancestor")
            return dict(merge_base_commit=dict(sha=path.split("/")[1].split("...")[0]))
        if path == "pulls/12":
            return self.pr.copy()
        if path == "actions/runs/17/attempts/2":
            return dict(id=17, run_attempt=2, event="pull_request", head_sha=self.identity["head"],
                        path=".github/workflows/lean-cache-publish.yml", status="in_progress",
                        pull_requests=[dict(number=99, base=dict(ref="dev"), head=dict(sha=self.identity["head"]))])
        if path == "actions/runs/28/attempts/1":
            return self.producer_run.copy()
        if path == "actions/artifacts/81":
            return self.artifact.copy()
        if path.startswith("actions/artifacts?"):
            return dict(artifacts=self.artifacts)
        if path.startswith("commits/"):
            return [self.pr.copy()]
        if path.startswith("git/commits/"):
            return dict(sha=self.identity["merge"], parents=[dict(sha=self.identity[k]) for k in ("base", "head")])
        if path.endswith("/dispatches"):
            return dict(workflow_run_id=28)
        self.fail("unexpected API request: " + path)

    def run_with(self, function, *, env=None, api=None, association=None):
        run = subprocess.run

        def transport(command, **kwargs):
            if command[:2] != ["gh", "api"]:
                return run(command, **kwargs)
            _, owner, repository, path = command[2].split("/", 3)
            repository = owner + "/" + repository
            if path.startswith("commits/") and association is not None:
                self.assertNotIn("--method", command)
                self.assertGreater(kwargs["timeout"], 0)
                self.assertLessEqual(kwargs["timeout"], 60)
                status, stdout, stderr, code = association(path)
            else:
                body = kwargs.get("input")
                value = (api or self.api)(repository, path, json.loads(body) if body is not None else None)
                status, stdout, stderr, code = "200 OK", json.dumps(value), "", 0
            if "--include" in command and status is not None:
                stdout = f"HTTP/2.0 {status}\r\nX-Fixture: private-header\r\n\r\n{stdout}"
            if kwargs.get("check") and code:
                raise subprocess.CalledProcessError(code, command, stdout, stderr)
            if not kwargs.get("text"):
                stdout, stderr = stdout.encode(), stderr.encode()
            return subprocess.CompletedProcess(command, code, stdout, stderr)

        with mock.patch.dict(os.environ, env or self.env, clear=True), \
                mock.patch.object(subprocess, "run", side_effect=transport), contextlib.redirect_stdout(io.StringIO()):
            return function()

    def test_label_dispatch_pins_event_identity_and_one_exact_target_run(self):
        result = self.run_with(lambda: producer.dispatch(self.root))
        self.assertEqual("dispatched", result["status"])
        self.assertEqual(self.identity, result["source"])
        self.assertEqual(28, result["producer_run"])
        calls = [body for path, body in self.calls if path.endswith("/dispatches")]
        self.assertEqual(self.identity, json.loads(calls[0]["inputs"].pop("pr_source")))
        self.assertEqual([dict(ref=self.identity["target_ref"], return_run_details=True,
            inputs=dict(operation="pr", source_ref=self.identity["target_ref"], source_sha=self.identity["merge"]))], calls)
        self.assertEqual("producer_run=28\n", (self.root / "outputs").read_text())

    def test_dispatch_rejects_wrong_label_event_ref_and_head(self):
        for change in (dict(action="closed"), dict(label=dict(name="other")), dict(number=99),
                       dict(pull_request=dict(head=dict(sha="b" * 40), base=dict(ref="integration-cache-tests")))):
            with self.subTest(change=change):
                self.event_file.write_text(json.dumps(dict(self.event, **change)))
                with self.assertRaises(ValueError):
                    self.run_with(lambda: producer.dispatch(self.root))
        self.assertFalse(any(path.endswith("/dispatches") for path, _ in self.calls))

    def test_opted_in_current_head_events_dispatch_and_absent_label_rejects(self):
        for action in ("opened", "reopened", "synchronize", "labeled"):
            with self.subTest(action=action):
                event = dict(self.event, action=action)
                self.event_file.write_text(json.dumps(event))
                result = self.run_with(lambda: producer.dispatch(self.root))
                self.assertEqual(self.identity, result["source"])
                event["pull_request"] = dict(event["pull_request"], labels=[])
                self.event_file.write_text(json.dumps(event))
                with self.assertRaisesRegex(ValueError, "opted-in"):
                    self.run_with(lambda: producer.dispatch(self.root))
        for action in ("unlabeled", "edited", "closed"):
            self.event_file.write_text(json.dumps(dict(self.event, action=action)))
            with self.assertRaises(ValueError):
                self.run_with(lambda: producer.dispatch(self.root))

    def test_synchronize_pins_the_replacement_head_and_rejects_the_old_event(self):
        old = dict(self.identity)
        tree = self.git("rev-parse", "HEAD^{tree}")
        head = self.git("commit-tree", tree, "-p", old["head"], data="new current head\n")
        merge = self.git("commit-tree", tree, "-p", old["base"], "-p", head, data="new candidate\n")
        self.git("update-ref", "HEAD", merge)
        self.identity.update(head=head, merge=merge)
        self.pr["head"] = dict(sha=head)
        self.env["GITHUB_SHA"] = merge
        self.event["action"] = "synchronize"
        self.event["pull_request"]["head"] = dict(sha=head)
        self.event_file.write_text(json.dumps(self.event))
        result = self.run_with(lambda: producer.dispatch(self.root))
        self.assertEqual(self.identity, result["source"])
        with self.assertRaisesRegex(ValueError, "head or target changed"):
            self.run_with(lambda: producer.validate_remote(old))

    def test_removed_label_blocks_delayed_dispatch_and_production(self):
        self.pr["labels"] = []
        with self.assertRaisesRegex(ValueError, "opted-in"):
            self.run_with(lambda: producer.dispatch(self.root))
        with self.assertRaisesRegex(ValueError, "opted-in"):
            self.run_with(lambda: producer.prepare(self.root, self.identity), env=self.runtime())
        self.assertFalse(any(path.endswith("/dispatches") for path, _ in self.calls))

    def test_dispatch_requires_exact_run_id_and_preserves_api_failure(self):
        for response in ({}, dict(workflow_run_id="28"), dict(workflow_run_id=0)):
            def api(repository, path, body=None):
                return response if path.endswith("/dispatches") else self.api(repository, path, body)
            with self.subTest(response=response), self.assertRaisesRegex(ValueError, "exact producer run id"):
                self.run_with(lambda: producer.dispatch(self.root), api=api)
        with mock.patch.dict(os.environ, self.env, clear=True), \
                mock.patch.object(producer, "api", side_effect=subprocess.CalledProcessError(1, "gh", stderr="HTTP 403")), \
                mock.patch.object(sys, "argv", ["lean_pr_cache.py", "dispatch", "--repository", str(self.root)]), \
                contextlib.redirect_stderr(io.StringIO()) as errors:
            self.assertEqual(2, producer.main())
        self.assertIn("HTTP 403", errors.getvalue())

    def test_prepare_keeps_source_distinct_from_workflow_and_cache_scope(self):
        result = self.run_with(lambda: producer.prepare(self.root, self.identity), env=self.runtime())
        self.assertEqual(self.identity, result["source"])
        self.assertEqual(self.runtime_sha, result["runtime"]["sha"])
        self.assertNotEqual(self.identity["merge"], result["runtime"]["sha"])
        markers = dict(row.split("=", 1) for row in (self.root / "environment").read_text().splitlines())
        self.assertEqual("refs/pull/12/merge", markers["STRATALINT_CACHE_SOURCE_REF"])
        self.assertNotIn("STRATALINT_CACHE_SOURCE_VALIDATED", markers)
        with mock.patch.dict(os.environ, dict(self.runtime(), **markers), clear=True):
            self.assertFalse(producer.actions.manual_source_is_valid())
            keys = producer.actions.actions_keys(self.root)
            self.assertFalse(keys["save_allowed"])
            self.assertFalse(keys["project_save_allowed"])
            self.assertTrue(keys["project"]["key"].endswith("28-1"))

    def test_prepare_accepts_same_head_draft_association_and_moved_target(self):
        result = self.run_with(lambda: producer.prepare(self.root, self.identity), env=self.runtime())
        self.assertEqual("12", result["source"]["pr"])
        self.assertEqual(self.identity["base"], result["source"]["base"])

    def test_prepare_rejects_wrong_runtime_inputs_and_checkout(self):
        for field, value in (("GITHUB_REF", "refs/heads/dev"), ("GITHUB_EVENT_NAME", "pull_request"),
                             ("GITHUB_WORKFLOW_SHA", "e" * 40), ("GITHUB_WORKFLOW_REF", "other@refs/heads/dev"),
                             ("SOURCE_SHA", "f" * 40), ("SOURCE_REF", "refs/heads/dev"), ("GITHUB_SHA", "bad")):
            with self.subTest(field=field), self.assertRaises(ValueError):
                self.run_with(lambda: producer.prepare(self.root, self.identity), env=dict(self.runtime(), **{field: value}))
        for change in (dict(merge="a" * 40), dict(head="b" * 40), dict(base="c" * 40)):
            with self.subTest(change=change), self.assertRaises(ValueError):
                self.run_with(lambda: producer.prepare(self.root, dict(self.identity, **change)), env=self.runtime())

    def test_source_shape_rejects_missing_extra_zero_and_invalid_fields(self):
        for change in (dict(extra=True), dict(pr="0"), dict(source_run="17\n"), dict(source_attempt="0"),
                       dict(head="0" * 40), dict(merge="A" * 40), dict(repository="../other"),
                       dict(target_ref="refs/heads/topic"), dict(target_ref="refs/heads/integration-../x")):
            with self.subTest(change=change), self.assertRaises((ValueError, subprocess.SubprocessError)):
                producer.validate_identity(dict(self.identity, **change))
        with self.assertRaises(ValueError):
            producer.validate_identity({})

    def test_prepare_rejects_unprotected_target_nonancestor_or_changed_pr(self):
        cases = [("branches/", dict(protected=False)), ("compare/", dict(merge_base_commit=dict(sha="f" * 40))),
                 ("pulls/", dict(state="closed")), ("pulls/", dict(head=dict(sha="a" * 40))),
                 ("pulls/", dict(base=dict(ref="dev", repo=dict(full_name="owner/repository"))))]
        for prefix, update in cases:
            def api(repository, path, body=None):
                result = self.api(repository, path, body)
                return dict(result, **update) if path.startswith(prefix) else result
            with self.subTest(prefix=prefix, update=update), self.assertRaises(ValueError):
                self.run_with(lambda: producer.prepare(self.root, self.identity), env=self.runtime(), api=api)

    def test_prepare_rejects_source_run_identity_changes(self):
        for update in (dict(id=18), dict(run_attempt=1), dict(event="push"), dict(head_sha="a" * 40), dict(path="other.yml")):
            def api(repository, path, body=None):
                result = self.api(repository, path, body)
                return dict(result, **update) if path.startswith("actions/runs/") else result
            with self.subTest(update=update), self.assertRaises(ValueError):
                self.run_with(lambda: producer.prepare(self.root, self.identity), env=self.runtime(), api=api)

    def build_work(self, env, report=0, programs=0):
        path = self.root / "build/lean-cache/build-work.json"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(dict(schema_version=1, run_id=env["GITHUB_RUN_ID"],
            run_attempt=env["GITHUB_RUN_ATTEMPT"], repository=str(self.root.resolve()), report=report, programs=programs)))

    def preparation(self):
        self.dependency_files()
        files = {"lib/Module.olean": b"native", "bin/audit": b"#!/bin/sh\nexit 0\n",
                 "lib/.hidden": b"hidden", "ir/Module.c": b"c", "ir/A/Module.c.hash": b"hash",
                 "reg/.hidden": b"reg", "stratalint/raw-lean-report.json": b"report",
                 "unregistered.txt": b"not transported"}
        for relative, data in files.items():
            path = self.root / ".lake/build" / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        (self.root / ".lake/build/bin/audit").chmod(0o755)
        (self.root / ".lake/build/lib/alias").symlink_to("Module.olean")
        self.build_work(self.runtime())
        self.bundle = self.root / "preparation"
        self.run_with(lambda: producer.pack(self.root, self.identity, self.bundle), env=self.runtime())
        self.zipped = self.root / "preparation.zip"
        self.zip_preparation()
        shutil.rmtree(self.root / ".lake")

    def zip_preparation(self):
        with zipfile.ZipFile(self.zipped, "w") as archive:
            for path in sorted(self.bundle.rglob("*")):
                if path.is_file():
                    archive.write(path, path.relative_to(self.bundle))

    def merged(self):
        self.pr.update(state="closed", merged=True, merged_at="2026-01-02T00:00:00Z", merge_commit_sha=self.actual_merge)
        self.git("update-ref", "HEAD", self.actual_merge)
        self.env.update(GITHUB_EVENT_NAME="push", GITHUB_REF=self.identity["target_ref"], GITHUB_SHA=self.actual_merge)
        self.event_file.write_text(json.dumps(dict(after=self.actual_merge, ref=self.identity["target_ref"])))

    def adopt(self, *, env=None, api=None, association=None, cache_action=None):
        with mock.patch.object(producer, "download", side_effect=lambda repo, aid, path: shutil.copyfile(self.zipped, path)) as download:
            result = self.run_with(lambda: producer.adopt(self.root, cache_action), env=env, api=api, association=association)
        return result, download

    def test_association_retries_only_failed_page_before_adoption(self):
        self.preparation()
        self.merged()
        unrelated = dict(self.pr, merge_commit_sha=self.identity["merge"])
        association = mock.Mock(side_effect=[
            ("200 OK", json.dumps([unrelated] * 100), "", 0),
            ("500 Internal Server Error", "", "gh: unexpected end of JSON input", 1),
            ("200 OK", json.dumps([self.pr]), "", 0),
        ])
        result, download = self.adopt(association=association)
        self.assertEqual("adopted", result["status"])
        self.assertEqual(self.actual_merge, result["actual_merge"])
        download.assert_called_once()
        path = f"commits/{self.actual_merge}/pulls?per_page=100&page="
        self.assertEqual([mock.call(path + str(page)) for page in (1, 2, 2)], association.call_args_list)
        self.assertIn(("pulls/12", None), self.calls)
        self.assertIn(("actions/artifacts/81", None), self.calls)

    def test_manual_association_recovers_truncated_or_interrupted_reads(self):
        self.merged()
        env = dict(self.env, GITHUB_EVENT_NAME="workflow_dispatch", GITHUB_SHA=self.runtime_sha,
                   STRATALINT_CACHE_SOURCE_VALIDATED="true", STRATALINT_CACHE_SOURCE_REF=self.identity["target_ref"],
                   STRATALINT_CACHE_SOURCE_COMMIT=self.actual_merge, STRATALINT_CACHE_CHECKED_OUT_SHA=self.actual_merge)
        for first in (("200 OK", "", "", 0),
                      ("200 OK", '[{"number":', "", 0),
                      (None, "", "gh: unexpected EOF", 1)):
            with self.subTest(first=first):
                association = mock.Mock(side_effect=[first, ("200 OK", json.dumps([self.pr]), "", 0)])
                result = self.run_with(lambda: producer.consumer_context(self.root), env=env, association=association)
                self.assertTrue(result["merged"])
                self.assertEqual(self.actual_merge, result["checkout"])
                self.assertEqual(2, association.call_count)
                self.assertEqual(*association.call_args_list)

    def test_association_empty_listing_is_immediate_miss(self):
        self.merged()
        association = mock.Mock(return_value=("200 OK", "[]", "", 0))
        with mock.patch.object(sys, "argv", ["lean_pr_cache.py", "adopt", "--repository", str(self.root)]):
            self.assertEqual(0, self.run_with(producer.main, association=association))
        association.assert_called_once()
        self.assertEqual([], self.calls)
        self.assertEqual("adopted=false\n", (self.root / "outputs").read_text())

    def test_association_retry_does_not_extend_the_page_deadline(self):
        self.merged()
        association = mock.Mock(return_value=("500 Internal Server Error", "", "", 1))
        clock = mock.Mock()
        clock.monotonic.side_effect = [100, 100, 159.9]
        with mock.patch.object(producer, "time", clock), self.assertRaisesRegex(ValueError, "HTTP 500"):
            self.run_with(lambda: producer.consumer_context(self.root), association=association)
        association.assert_called_once()
        clock.sleep.assert_not_called()

    def test_association_errors_fail_closed_without_using_partial_pages(self):
        self.merged()
        temporary = ("502 Bad Gateway", "", "gh: unexpected end of JSON input", 1)
        first_page = ("200 OK", json.dumps([self.pr] + [dict(self.pr, merged_at=None)] * 99), "", 0)
        cases = [
            ([first_page, temporary, temporary], "HTTP 502", (1, 2, 2)),
            ([("403 Forbidden", "", "gh: unexpected end of JSON input", 1)], "HTTP 403", (1,)),
            ([("404 Not Found", "", "gh: unexpected end of JSON input", 1)], "HTTP 404", (1,)),
            ([("200 OK", '{"items":[]}', "", 0)], "invalid API listing", (1,)),
            ([("200 OK", "[invalid]", "", 0)], "invalid JSON", (1,)),
            ([(None, "", "gh: unexpected end of JSON input", 1)], "no HTTP status", (1,)),
        ]
        for responses, expected, pages in cases:
            with self.subTest(expected=expected), \
                    mock.patch.object(sys, "argv", ["lean_pr_cache.py", "adopt", "--repository", str(self.root)]), \
                    mock.patch.object(producer, "download") as download, contextlib.redirect_stderr(io.StringIO()) as errors:
                (self.root / "outputs").unlink(missing_ok=True)
                association = mock.Mock(side_effect=responses)
                self.assertEqual(2, self.run_with(producer.main, association=association))
                path = f"commits/{self.actual_merge}/pulls?per_page=100&page="
                self.assertEqual([mock.call(path + str(page)) for page in pages], association.call_args_list)
                self.assertIn(expected, errors.getvalue())
                self.assertNotIn("private-header", errors.getvalue())
                self.assertEqual("adopted=false\n", (self.root / "outputs").read_text())
                self.assertEqual([], self.calls)
                self.assertFalse((self.root / "build/lean-cache/pr-adopted.json").exists())
                download.assert_not_called()

    def test_confirm_binds_immutable_artifact_instead_of_ordinary_cache_keys(self):
        result = self.run_with(lambda: producer.confirm(self.root, self.identity, 81), env=self.runtime())
        self.assertEqual("prepared", result["status"])
        self.assertEqual(81, result["artifact"])
        self.assertFalse(any(path.startswith("actions/caches") for path, _ in self.calls))
        self.pr.update(state="closed", merged=True, merge_commit_sha=self.actual_merge)
        self.run_with(lambda: producer.confirm(self.root, self.identity, 81), env=self.runtime())
        self.pr["merged"] = False
        with self.assertRaisesRegex(ValueError, "head or target changed"):
            self.run_with(lambda: producer.confirm(self.root, self.identity, 81), env=self.runtime())

    def test_confirm_rejects_expired_wrong_run_head_name_and_id(self):
        good = self.artifact.copy()
        for defect in (dict(expired=True), dict(id=82), dict(name="other"),
                       dict(workflow_run=dict(id=29, head_sha=self.runtime_sha)),
                       dict(workflow_run=dict(id=28, head_sha="e" * 40))):
            self.artifact = dict(good, **defect)
            with self.subTest(defect=defect), self.assertRaisesRegex(ValueError, "artifact is expired"):
                self.run_with(lambda: producer.confirm(self.root, self.identity, 81), env=self.runtime())

    def test_source_pr_retrieves_preparation_without_target_seed_and_preserves_native_files(self):
        self.preparation()
        result, download = self.adopt()
        self.assertEqual("adopted", result["status"])
        self.assertIsNone(result["actual_merge"])
        download.assert_called_once()
        self.assertEqual(b"native", (self.root / ".lake/build/lib/Module.olean").read_bytes())
        self.assertEqual(b"hidden", (self.root / ".lake/build/lib/.hidden").read_bytes())
        self.assertEqual(0o755, (self.root / ".lake/build/bin/audit").stat().st_mode & 0o777)
        self.assertEqual(0, subprocess.run([str(self.root / ".lake/build/bin/audit")], check=False).returncode)
        self.assertTrue((self.root / ".lake/build/lib/alias").is_symlink())
        self.assertEqual(b"native", (self.root / ".lake/build/lib/alias").read_bytes())
        self.assertTrue((self.root / ".lake/build/ir/Module.c").is_file())
        self.assertTrue((self.root / ".lake/build/ir/A/Module.c.hash").is_file())
        self.assertFalse((self.root / ".lake/build/unregistered.txt").exists())
        self.assertEqual(0o755, (self.root / ".lake/packages/mathlib/scripts/bench/size/run").stat().st_mode & 0o777)
        with mock.patch.dict(os.environ, self.env, clear=True):
            actions = producer.actions
            self.assertFalse(actions.adoption_record(self.root)["merged"])
            self.assertEqual("pull-requests-do-not-publish-project-seeds", actions.project_publication(self.root)[1])

    def test_adoption_reclaims_download_zip_before_native_unpack(self):
        self.preparation()
        with mock.patch.object(producer, "unpack", wraps=producer.unpack) as unpack:
            result, _ = self.adopt()
        self.assertEqual("adopted", result["status"])
        native_archive = unpack.call_args.args[1]
        self.assertFalse(native_archive.with_name("artifact.zip").exists())

    def test_sharded_preparation_installs_bundled_and_referenced_files_together(self):
        self.preparation()
        packages, _ = self.dependency_files()
        with tarfile.open(self.bundle / "native.tar.gz", "w:gz") as archive:
            archive.add(packages, arcname=".lake/packages")
        shutil.rmtree(self.root / ".lake")
        group = [["D5.Fixture"]]
        key = shards.group_identity(group)
        compiler_path = "lib/lean/D5/Fixture.olean"
        build = self.root / "producer-build"
        material = {}
        for entry, relative in [(key, compiler_path), (shards.REPORT, shards.REPORT_PATH)]:
            path = build / relative
            path.parent.mkdir(parents=True)
            path.write_text(entry)
            material[entry] = shards.write_payload(self.root, build, [relative])
        packed = self.bundle / "shards"
        packed.mkdir()
        local = self.root / shards.transport_payload(material[key])
        local.rename(packed / local.name)
        with mock.patch.dict(os.environ, self.env, clear=True):
            binding = shards.binding(self.root, "complete")
        index = dict(binding=binding, state="complete", layout={key: group},
            owner=dict(commit=self.identity["merge"], ref=self.identity["target_ref"], run="28", attempt="1"),
            entries=material, required={key: [compiler_path], shards.REPORT: [shards.REPORT_PATH]},
            fingerprints={entry: "a" * 64 for entry in material}, sources={"D5.Fixture": "b" * 64})
        (self.bundle / "project.json").write_text(json.dumps(index))
        self.artifact["name"] = producer.artifact_name(self.identity, sharded=True)
        self.zip_preparation()

        # Exercise the real Python validator and install while replacing network
        # transport with the locally staged reference.
        runtime = ("/fixture/node", "/fixture/cache-action")
        run = subprocess.run

        def restore(command, *args, **kwargs):
            if tuple(command[:2]) != runtime:
                return run(command, *args, **kwargs)
            self.assertEqual("restore-preparation", command[2])
            directory = pathlib.Path(command[3])
            record = shards.read_index(directory / "project.json", binding, "complete")
            result = shards.install(self.root, record, [], require_complete=True, preparation=directory)
            return subprocess.CompletedProcess(command, 0 if result["complete"] else 3)

        reference = self.root / shards.transport_payload(material[shards.REPORT])
        unavailable = reference.with_suffix(".unavailable")
        reference.rename(unavailable)
        with mock.patch.object(producer.subprocess, "run", side_effect=restore):
            result, download = self.adopt()
            self.assertEqual("miss", result["status"])
            download.assert_not_called()
            result, _ = self.adopt(cache_action=runtime)
            self.assertEqual("miss", result["status"])
            self.assertFalse((self.root / ".lake/build").exists())
            self.assertFalse((self.root / ".lake/packages").exists())
            unavailable.rename(reference)
            result, _ = self.adopt(cache_action=runtime)
        self.assertEqual("adopted", result["status"])
        self.assertIn("sharded=true", (self.root / "outputs").read_text())
        self.assertEqual(key, (self.root / ".lake/build" / compiler_path).read_text())
        self.assertEqual(shards.REPORT, (self.root / ".lake/build" / shards.REPORT_PATH).read_text())
        self.assertTrue((self.root / ".lake/packages/mathlib/scripts/bench/size/run").is_file())

    def test_merge_activates_at_actual_event_checkout_without_second_publisher(self):
        self.preparation()
        self.merged()
        result, _ = self.adopt()
        self.assertEqual(self.actual_merge, result["actual_merge"])
        self.assertNotEqual(result["source"]["merge"], result["actual_merge"])
        self.assertEqual(self.identity["merge"], result["source"]["merge"])
        self.build_work(self.env)
        with mock.patch.dict(os.environ, self.env, clear=True), contextlib.redirect_stdout(io.StringIO()) as out:
            actions = producer.actions
            actions.restore(self.root, actions.actions_keys(self.root), {})
            self.assertTrue((self.root / ".lake/build/lib/Module.olean").is_file())
            self.assertEqual((True, "adopted-merged-preparation", 0), actions.project_publication(self.root))
            actions.snapshot(self.root, actions.actions_keys(self.root), ["project"])
        self.assertIn('"build_work": 0', out.getvalue())
        self.assertIn("project_ready=true", out.getvalue())
        self.assertNotIn("STRATALINT_ACTIONS_CACHE_SEEDED=1", out.getvalue())

    def test_adoption_record_cannot_override_unknown_work_report_failure_or_another_invocation(self):
        self.preparation()
        self.merged()
        self.adopt()
        actions = producer.actions
        record = self.root / "build/lean-cache/pr-adopted.json"
        original = json.loads(record.read_text())
        self.build_work(self.env)
        for defect in (dict(run="16"), dict(attempt="1"), dict(repository="/other"),
                       dict(checkout=self.identity["merge"]), dict(ref="refs/heads/dev"), dict(artifact=0), dict(merged=False)):
            record.write_text(json.dumps(dict(original, **defect)))
            with self.subTest(defect=defect), mock.patch.dict(os.environ, self.env, clear=True):
                self.assertEqual((False, "no-build-work", 0), actions.project_publication(self.root))
        record.write_text(json.dumps(original))
        (self.root / "build/lean-cache/build-work.json").unlink()
        with mock.patch.dict(os.environ, self.env, clear=True):
            self.assertEqual((False, "build-work-unknown", None), actions.project_publication(self.root))
        self.build_work(self.env)
        with mock.patch.dict(os.environ, dict(self.env, STRATALINT_REPORT_SUCCEEDED="false"), clear=True), \
                contextlib.redirect_stdout(io.StringIO()) as out:
            actions.snapshot(self.root, actions.actions_keys(self.root), ["project"])
        self.assertIn("project_ready=false", out.getvalue())

    def test_actual_merge_source_tree_drift_is_left_to_native_increment(self):
        self.preparation()
        blob = self.git("hash-object", "-w", "--stdin", data="actual target source drift\n")
        tree = self.git("mktree", data="100644 blob " + blob + "\tchanged-source\n")
        moved = self.git("commit-tree", tree, "-p", self.identity["base"], data="target moved\n")
        self.actual_merge = self.git("commit-tree", tree, "-p", moved, "-p", self.identity["head"], data="merge after target movement\n")
        self.merged()
        result, _ = self.adopt()
        self.assertEqual(self.actual_merge, result["checkout"])
        self.assertEqual(self.identity["base"], result["source"]["base"])
        self.assertNotEqual(self.git("rev-parse", self.identity["merge"] + "^{tree}"), self.git("rev-parse", "HEAD^{tree}"))

    def test_unmerged_closed_unmerged_and_wrong_event_never_activate_for_target(self):
        self.preparation()
        self.git("update-ref", "HEAD", self.identity["base"])
        self.env.update(GITHUB_EVENT_NAME="push", GITHUB_REF=self.identity["target_ref"], GITHUB_SHA=self.identity["base"])
        self.event_file.write_text(json.dumps(dict(after=self.identity["base"], ref=self.identity["target_ref"])))
        for state in ("open", "closed"):
            self.pr["state"] = state
            result, download = self.adopt()
            self.assertEqual("miss", result["status"])
            download.assert_not_called()
        self.merged()
        self.event_file.write_text(json.dumps(dict(after=self.identity["merge"], ref=self.identity["target_ref"])))
        with self.assertRaisesRegex(ValueError, "event checkout mismatch"):
            self.adopt()

    def test_changed_source_head_and_unrelated_pr_cannot_use_old_preparation(self):
        self.preparation()
        self.pr["head"] = dict(sha="b" * 40)
        with self.assertRaisesRegex(ValueError, "source PR head or target changed"):
            self.adopt()
        self.merged()
        result, download = self.adopt()
        self.assertEqual("miss", result["status"])
        download.assert_not_called()
        self.git("update-ref", "HEAD", self.identity["merge"])
        self.env.update(GITHUB_EVENT_NAME="pull_request", GITHUB_REF="refs/pull/12/merge", GITHUB_SHA=self.identity["merge"])
        self.event_file.write_text(json.dumps(self.event))
        self.pr.update(state="open", head=dict(sha=self.identity["head"]), number=99)
        # A same-head PR association is not evidence for source PR 12.
        with self.assertRaisesRegex(ValueError, "source PR identity"):
            self.adopt()

    def test_missing_expired_or_unfinished_preparation_is_not_successful_handoff(self):
        self.preparation()
        self.merged()
        for candidates in ([], [dict(self.artifact, expired=True)]):
            self.artifacts = candidates
            result, download = self.adopt()
            self.assertEqual("miss", result["status"])
            download.assert_not_called()
        self.artifacts = [self.artifact]
        self.producer_run.update(status="in_progress", conclusion=None)
        result, _ = self.adopt()
        self.assertEqual("miss", result["status"])
        self.assertFalse((self.root / "build/lean-cache/pr-adopted.json").exists())

    def test_manual_and_automatic_long_fallback_can_adopt_same_merge(self):
        self.preparation()
        self.merged()
        env = dict(self.env, GITHUB_EVENT_NAME="workflow_dispatch", GITHUB_SHA=self.runtime_sha,
                   STRATALINT_CACHE_SOURCE_VALIDATED="true", STRATALINT_CACHE_SOURCE_REF=self.identity["target_ref"],
                   STRATALINT_CACHE_SOURCE_COMMIT=self.actual_merge, STRATALINT_CACHE_CHECKED_OUT_SHA=self.actual_merge)
        result, _ = self.adopt(env=env)
        self.assertEqual(self.actual_merge, result["actual_merge"])
        self.build_work(env)
        with mock.patch.dict(os.environ, env, clear=True):
            self.assertEqual((True, "adopted-merged-preparation", 0), producer.actions.project_publication(self.root))

    def test_preparation_identity_partition_runtime_attempt_and_synthetic_parents_fail_closed(self):
        self.preparation()
        self.merged()
        original = json.loads((self.bundle / "preparation.json").read_text())
        for key, update, reason in (("source", dict(pr="99"), "PR/head/target"),
                                   ("source", dict(target_ref="refs/heads/dev"), "PR/head/target"),
                                   ("runtime", dict(workflow_sha="e" * 40), "runtime identity"),
                                   ("runtime", dict(attempt="0"), "runtime identity")):
            value = dict(original, **{key: dict(original[key], **update)})
            (self.bundle / "preparation.json").write_text(json.dumps(value))
            self.zip_preparation()
            with self.subTest(key=key, update=update), self.assertRaisesRegex(ValueError, reason):
                self.adopt()
        for key in ("partition", "elan_key"):
            (self.bundle / "preparation.json").write_text(json.dumps(dict(original, **{key: "foreign"})))
            self.zip_preparation()
            with self.assertRaisesRegex(ValueError, "invalid preparation native identity"):
                self.adopt()
        (self.bundle / "preparation.json").write_text(json.dumps(original))
        self.zip_preparation()
        def api(repository, path, body=None):
            result = self.api(repository, path, body)
            if path.startswith("git/commits/"):
                result["parents"].reverse()
            return result
        with self.assertRaisesRegex(ValueError, "M parents are not B,H"):
            self.adopt(api=api)
        self.assertFalse((self.root / ".lake/build").exists())

    def test_changed_native_inputs_skip_preparation_without_touching_cache(self):
        self.preparation()
        self.merged()
        for filename, replacement in (
                ("lean-toolchain", "leanprover/lean4:v4.35.0\n"),
                ("lake-manifest.json", json.dumps({"packages": [{"name": "mathlib", "rev": "b" * 40}]}))):
            path = self.root / filename
            original = path.read_bytes()
            path.write_text(replacement)
            with self.subTest(filename=filename):
                with mock.patch.object(producer, "receipt", wraps=producer.receipt) as receipts:
                    result, _ = self.adopt()
                self.assertEqual("miss", result["status"])
                incompatible = [call.kwargs for call in receipts.call_args_list
                                if call.args[0] == "incompatible"]
                self.assertEqual(1, len(incompatible))
                self.assertEqual(81, incompatible[0]["artifact"])
                self.assertNotEqual(incompatible[0]["prepared"], incompatible[0]["current"])
                self.assertFalse((self.root / ".lake").exists())
                self.assertFalse((self.root / "build/lean-cache/pr-adopted.json").exists())
                self.assertNotIn("adopted=true", (self.root / "outputs").read_text())
                self.assertTrue(any(path.startswith("git/commits/") for path, _ in self.calls))
            path.write_bytes(original)

    def test_incompatible_preparation_still_rejects_invalid_identity(self):
        self.preparation()
        self.merged()
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
        self.producer_run["run_attempt"] = 2
        with self.assertRaisesRegex(ValueError, "attempt identity differs"):
            self.adopt()
        self.assertFalse((self.root / ".lake").exists())

    def test_attempt_status_is_immutable_and_artifact_time_must_belong_to_it(self):
        self.preparation()
        self.merged()
        # Only attempts/1 is consulted; a mutable latest run association is unused.
        self.adopt()
        self.assertNotIn(("actions/runs/28", None), self.calls)
        self.artifact["created_at"] = "2025-12-31T23:59:59Z"
        with self.assertRaisesRegex(ValueError, "producer attempt interval"):
            self.adopt()
        self.producer_run["run_attempt"] = 2
        with self.assertRaisesRegex(ValueError, "attempt identity differs"):
            self.adopt()

    def test_invalid_payload_or_download_failure_keeps_original_error_and_no_adoption(self):
        self.preparation()
        self.merged()
        self.zipped.write_bytes(b"broken zip")
        with self.assertRaises(zipfile.BadZipFile):
            self.adopt()
        with mock.patch.object(producer, "download", side_effect=subprocess.CalledProcessError(1, "gh", stderr="HTTP 410 expired")), \
                self.assertRaises(subprocess.CalledProcessError) as failure:
            self.run_with(lambda: producer.adopt(self.root))
        self.assertIn("HTTP 410", failure.exception.stderr)
        self.assertFalse((self.root / "build/lean-cache/pr-adopted.json").exists())

    def test_native_transport_rejects_unregistered_files_and_escaping_links_before_replacement(self):
        self.preparation()
        self.merged()
        target = self.root / ".lake/build/lib/keep"
        target.parent.mkdir(parents=True)
        target.write_text("original")
        for name, link in (("../outside", None), (".lake/build/unregistered", None),
                           (".lake/build/lib/escape", "/outside")):
            with tarfile.open(self.bundle / "native.tar.gz", "w:gz") as archive:
                info = tarfile.TarInfo(name)
                if link:
                    info.type, info.linkname = tarfile.SYMTYPE, link
                archive.addfile(info)
            self.zip_preparation()
            with self.subTest(name=name), self.assertRaises((ValueError, tarfile.TarError)):
                self.adopt()
            self.assertEqual("original", target.read_text())

    def test_api_preserves_structured_dispatch_and_read_only_gets(self):
        with mock.patch.object(subprocess, "run", return_value=mock.Mock(stdout='{"workflow_run_id":28}')) as run:
            producer.api("owner/repository", "actions/workflows/x/dispatches", {"ref": "refs/heads/dev"})
            self.assertEqual({"ref": "refs/heads/dev"}, json.loads(run.call_args.kwargs["input"]))
            self.assertIn("POST", run.call_args.args[0])
            producer.api("owner/repository", "")
            self.assertEqual(["gh", "api", "repos/owner/repository"], run.call_args.args[0])


if __name__ == "__main__":
    unittest.main(verbosity=2)
