"""Behavioral contracts for PR source identity and target-scoped production."""
import contextlib
import io
import json
import os
import subprocess
import sys
import unittest
from unittest import mock
from urllib.parse import parse_qs, urlsplit

from cache_fixture import REPO, CacheFixture

sys.path.insert(0, str(REPO / "tools/scripts/worktree"))
import lean_pr_cache as producer


class PrCacheContracts(CacheFixture, unittest.TestCase):
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
            pull_request=dict(head=dict(sha=head), base=dict(ref="integration-cache-tests")))
        self.event_file = self.root / "event.json"
        self.event_file.write_text(json.dumps(self.event))
        self.env.update(GITHUB_EVENT_NAME="pull_request", GITHUB_REF="refs/pull/12/merge", GITHUB_SHA=merge,
                        GITHUB_REPOSITORY="owner/repository", GITHUB_EVENT_PATH=str(self.event_file))
        self.runtime_sha = "d" * 40
        self.calls = []

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
            return dict(state="open", head=dict(sha=self.identity["head"]),
                        base=dict(ref="integration-cache-tests", repo=dict(full_name=repository)))
        if path == "actions/runs/17/attempts/2":
            return dict(id=17, run_attempt=2, event="pull_request", head_sha=self.identity["head"],
                        path=".github/workflows/lean-cache-publish.yml", status="in_progress",
                        pull_requests=[dict(number=99, base=dict(ref="dev"), head=dict(sha=self.identity["head"]))])
        if path.endswith("/dispatches"):
            return dict(workflow_run_id=28)
        if path == "":
            return dict(default_branch="dev")
        if path.startswith("actions/caches?"):
            query = parse_qs(urlsplit(path).query)
            return dict(actions_caches=[dict(id=70, key=query["key"][0], ref=query["ref"][0])])
        self.fail("unexpected API request: " + path)

    def run_with(self, function, *, env=None, api=None):
        with mock.patch.dict(os.environ, env or self.env, clear=True), \
                mock.patch.object(producer, "api", side_effect=api or self.api), contextlib.redirect_stdout(io.StringIO()):
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
        for change in (dict(action="opened"), dict(label=dict(name="other")), dict(number=99),
                       dict(pull_request=dict(head=dict(sha="b" * 40), base=dict(ref="integration-cache-tests")))):
            with self.subTest(change=change):
                self.event_file.write_text(json.dumps(dict(self.event, **change)))
                with self.assertRaises(ValueError):
                    self.run_with(lambda: producer.dispatch(self.root))
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
            self.assertTrue(keys["save_allowed"])
            self.assertTrue(keys["project_save_allowed"])
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

    def cache_env(self, suffix="28-1"):
        env = self.runtime()
        with mock.patch.dict(os.environ, env, clear=True):
            keys = producer.actions.actions_keys(self.root)
            env.update({layer.upper() + "_CACHE_KEY": keys[layer]["restore_prefix"] + suffix
                        for layer in ("project", "dependency")})
            env["ELAN_CACHE_KEY"] = producer.actions.elan_key(self.root)
        return env

    def test_confirm_records_actual_target_keys_and_source_runtime(self):
        result = self.run_with(lambda: producer.confirm(self.root, self.identity), env=self.cache_env())
        self.assertEqual("published", result["status"])
        self.assertEqual(self.identity, result["source"])
        self.assertEqual({"project", "dependency", "elan"}, set(result["caches"]))
        self.assertTrue(all(v["ref"] == self.identity["target_ref"] for v in result["caches"].values()))

    def test_confirm_accepts_validated_zero_work_seed_visible_on_default(self):
        def api(repository, path, body=None):
            if path.startswith("actions/caches?") and parse_qs(urlsplit(path).query)["ref"][0] != "refs/heads/dev":
                return dict(actions_caches=[])
            return self.api(repository, path, body)
        result = self.run_with(lambda: producer.confirm(self.root, self.identity), env=self.cache_env("16-2"), api=api)
        self.assertTrue(all(v["ref"] == "refs/heads/dev" for v in result["caches"].values()))
        self.assertTrue(result["caches"]["project"]["key"].endswith("16-2"))

    def test_confirm_rejects_missing_wrong_key_or_wrong_scope_for_each_layer(self):
        for layer in ("project", "dependency", "elan"):
            for defect in ("absent", "key", "ref"):
                def api(repository, path, body=None):
                    value = self.api(repository, path, body)
                    if path.startswith("actions/caches?") and layer in parse_qs(urlsplit(path).query)["key"][0]:
                        if defect == "absent":
                            return dict(actions_caches=[])
                        value["actions_caches"][0][defect] = "wrong"
                    return value
                with self.subTest(layer=layer, defect=defect), self.assertRaisesRegex(ValueError, "publication missing"):
                    self.run_with(lambda: producer.confirm(self.root, self.identity), env=self.cache_env(), api=api)

    def test_confirm_rechecks_current_head_and_pin(self):
        def api(repository, path, body=None):
            result = self.api(repository, path, body)
            return dict(result, head=dict(sha="b" * 40)) if path == "pulls/12" else result
        with self.assertRaisesRegex(ValueError, "head or target changed"):
            self.run_with(lambda: producer.confirm(self.root, self.identity), env=self.cache_env(), api=api)
        for layer in ("project", "dependency", "elan"):
            with self.subTest(layer=layer), self.assertRaisesRegex(ValueError, "invalid produced"):
                self.run_with(lambda: producer.confirm(self.root, self.identity),
                              env=dict(self.cache_env(), **{layer.upper() + "_CACHE_KEY": "foreign-key"}))

    def test_api_preserves_structured_dispatch_and_read_only_gets(self):
        with mock.patch.object(subprocess, "run", return_value=mock.Mock(stdout='{"workflow_run_id":28}')) as run:
            producer.api("owner/repository", "actions/workflows/x/dispatches", {"ref": "refs/heads/dev"})
            self.assertEqual({"ref": "refs/heads/dev"}, json.loads(run.call_args.kwargs["input"]))
            self.assertIn("POST", run.call_args.args[0])
            producer.api("owner/repository", "")
            self.assertEqual(["gh", "api", "repos/owner/repository"], run.call_args.args[0])


if __name__ == "__main__":
    unittest.main(verbosity=2)
