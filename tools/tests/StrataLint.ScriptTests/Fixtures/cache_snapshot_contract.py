"""Actions snapshot publication, material restoration, and rollback contracts."""
import contextlib
import importlib
import io
import json
import os
import pathlib
import shutil
import sys
import subprocess
import tempfile
import unittest
from unittest import mock
import urllib.error
import urllib.parse
import urllib.request

from cache_fixture import CACHE, REV, CacheFixture


class SnapshotContracts(CacheFixture, unittest.TestCase):
    def lookup_keys(self, responses=(), **environment):
        owner = self.restore_owner()
        env = dict(self.env, GH_TOKEN="synthetic-token", GITHUB_REPOSITORY="owner/repository",
                   GITHUB_API_URL="https://cache.example.test/api/v3")
        env.update(environment)
        with mock.patch.dict(os.environ, env, clear=True):
            publication = owner.actions_keys(self.root)["project"]
            with mock.patch.object(urllib.request, "urlopen", side_effect=responses) as opened, \
                    mock.patch.object(sys, "argv", [str(CACHE), "keys", "--repository", str(self.root)]), \
                    contextlib.redirect_stdout(io.StringIO()) as result:
                code = owner.main()
        self.assertEqual(0, code, result.getvalue())
        lines = result.getvalue().splitlines()
        values = dict(line.split("=", 1) for line in lines if "=" in line)
        receipts = [json.loads(line.removeprefix("LEAN_ACTIONS_CACHE "))
                    for line in lines if line.startswith("LEAN_ACTIONS_CACHE ")]
        self.assertEqual(publication["key"], values["project_key"])
        self.assertEqual(publication["restore_prefix"], values["project_restore_prefix"])
        self.assertEqual(1, len(receipts), result.getvalue())
        self.assertEqual("project", receipts[0]["layer"])
        saved = (self.root / "outputs").read_text()
        self.assertIn("project_restore_key=" + values["project_restore_key"] + "\n", saved)
        return values, receipts[0], opened

    def cache_row(self, suffix, ref="refs/heads/dev", prefix=None, **fields):
        owner = self.restore_owner()
        with mock.patch.dict(os.environ, self.env):
            prefix = prefix or owner.actions_keys(self.root)["project"]["restore_prefix"]
        return dict(key=prefix + suffix, ref=ref, **fields)

    def cache_page(self, rows=(), total=None, link=None, status=200, body=None):
        response = mock.MagicMock()
        response.__enter__.return_value = response
        response.status = status
        response.headers = {} if link is None else {"Link": link}
        response.read.return_value = (body if body is not None else
            json.dumps(dict(total_count=len(rows) if total is None else total,
                            actions_caches=list(rows))).encode())
        return response

    def next_page(self, number, ref="refs/heads/dev"):
        prefix = self.cache_row("")["key"]
        query = urllib.parse.urlencode(dict(key=prefix, ref=ref, per_page=100, page=number))
        return "https://cache.example.test/api/v3/repos/owner/repository/actions/caches?" + query

    def assert_lookup_fallback(self, responses, reason, **environment):
        values, receipt, opened = self.lookup_keys(responses, **environment)
        self.assertEqual(values["project_key"], values["project_restore_key"])
        self.assertEqual("restore-preference-fallback", receipt["status"])
        self.assertEqual(reason, receipt["reason"])
        self.assertEqual(values["project_key"], receipt["requested_key"])
        return opened

    def test_project_lookup_is_optional_without_credentials_repository_or_reader_ref(self):
        for missing in (dict(GH_TOKEN=""), dict(GITHUB_REPOSITORY=""), dict(GITHUB_REF=""),
                dict(GITHUB_EVENT_NAME="pull_request", GITHUB_BASE_REF=""),
                dict(GITHUB_EVENT_NAME="workflow_dispatch")):
            with self.subTest(missing=missing):
                opened = self.assert_lookup_fallback([], "lookup-not-configured", **missing)
                opened.assert_not_called()

    def test_project_lookup_transport_and_http_errors_are_optional(self):
        for failure, reason in ((OSError("network unavailable"), "lookup-request-failed"),
                (TimeoutError("transport guard"), "lookup-request-failed"),
                (RuntimeError("unexpected HTTP-layer failure"), "lookup-request-failed"),
                (urllib.error.HTTPError("https://cache.example.test", 403, "rate limit", {}, None), "lookup-http-error"),
                (self.cache_page(status=429), "lookup-http-error"),
                (self.cache_page(status=500), "lookup-http-error")):
            with self.subTest(reason=reason, failure=type(failure).__name__):
                opened = self.assert_lookup_fallback([failure], reason)
                self.assertEqual(1, opened.call_count)

    def test_project_lookup_invalid_json_and_malformed_listings_are_optional(self):
        for body in (b"{", b"\xff", b"[]", b"{}",
                b'{"total_count":true,"actions_caches":[]}',
                b'{"total_count":-1,"actions_caches":[]}',
                b'{"total_count":0,"actions_caches":null}',
                b'{"total_count":1,"actions_caches":[null]}',
                b'{"total_count":1,"actions_caches":[{"key":"key"}]}',
                b'{"total_count":1,"actions_caches":[{"key":1,"ref":"ref"}]}',
                b'{"total_count":0,"total_count":1,"actions_caches":[]}'):
            with self.subTest(body=body):
                self.assert_lookup_fallback([self.cache_page(body=body)], "lookup-malformed-listing")

    def test_project_lookup_never_uses_a_partial_listing(self):
        page = self.cache_page([self.cache_row("999-1")], total=2)
        self.assert_lookup_fallback([page], "lookup-incomplete-listing")
        link = '<' + self.next_page(2) + '>; rel="next"'
        first = self.cache_page([self.cache_row("999-1")], total=2, link=link)
        for second, reason in ((OSError("second page failed"), "lookup-request-failed"),
                (self.cache_page(), "lookup-incomplete-listing"),
                (self.cache_page([self.cache_row("1000-1")], total=3), "lookup-incomplete-listing")):
            with self.subTest(reason=reason):
                self.assert_lookup_fallback([first, second], reason)

    def test_project_lookup_rejects_broken_or_cyclic_pagination_without_following_it(self):
        for link in ("broken", '<' + self.next_page(1) + '>; rel="next"',
                '<' + self.next_page(3) + '>; rel="next"',
                '<' + self.next_page(2).replace("cache.example.test", "other.example.test") + '>; rel="next"',
                '<' + self.next_page(2).replace("refs%2Fheads%2Fdev", "refs%2Fheads%2Fother") + '>; rel="next"',
                '<' + self.next_page(2) + '>; rel="next", <' + self.next_page(2) + '>; rel="next"'):
            with self.subTest(link=link):
                opened = self.assert_lookup_fallback(
                    [self.cache_page([self.cache_row("999-1")], total=2, link=link)],
                    "lookup-incomplete-listing")
                self.assertEqual(1, opened.call_count)

    def test_project_lookup_empty_or_ineligible_listing_uses_the_existing_key(self):
        self.assert_lookup_fallback([self.cache_page()], "lookup-no-eligible-seed")
        rows = [self.cache_row(suffix) for suffix in ("0-1", "1-0", "01-1", "1-01",
                "-1-1", "1-1-tail", "1-1\n", "1", "1-a")]
        prefix = self.cache_row("")["key"]
        rows += [self.cache_row("999-1", ref="refs/heads/other"),
                 self.cache_row("999-1", prefix=prefix.replace("lean-project-push-", "lean-project-v4-")),
                 self.cache_row("999-1", prefix=prefix.replace(REV, "b" * 40)),
                 self.cache_row("999-1", prefix=prefix.replace("lean-project-push-", "lean-dependency-v4-"))]
        self.assert_lookup_fallback([self.cache_page(rows)], "lookup-no-eligible-seed")

    def test_project_lookup_uses_numeric_run_and_attempt_order_not_creation_order(self):
        rows = [self.cache_row("100-2", created_at="oldest"),
                self.cache_row("99-9", created_at="newest"),
                self.cache_row("100-10", created_at="middle"), self.cache_row("100-9"),
                self.cache_row("10000-1", ref="refs/heads/other")]
        values, receipt, opened = self.lookup_keys([self.cache_page(rows)])
        self.assertEqual(values["project_restore_prefix"] + "100-10", values["project_restore_key"])
        self.assertEqual("restore-preference", receipt["status"])
        self.assertEqual(values["project_restore_key"], receipt["requested_key"])
        self.assertEqual(1, opened.call_count)

    def test_project_lookup_does_not_change_snapshot_publication(self):
        self.native_seed("project")
        values, _, _ = self.lookup_keys([self.cache_page([self.cache_row("100-10")])])
        self.assertNotEqual(values["project_key"], values["project_restore_key"])
        ready, receipts = self.snapshot_result()
        self.assertEqual("true", ready["project_ready"])
        self.assertEqual(values["project_key"], receipts["project"]["key"])

    def test_project_lookup_follows_all_pages_before_selecting(self):
        rows = [self.cache_row("99-9"), self.cache_row("100-1"), self.cache_row("100-12")]
        responses = [self.cache_page([rows[0]], total=3,
            link='<' + self.next_page(2) + '>; rel="next", <' + self.next_page(3) + '>; rel="last"'),
            self.cache_page([rows[1]], total=3, link='<' + self.next_page(3) + '>; rel="next"'),
            self.cache_page([rows[2]], total=3, link='<' + self.next_page(2) + '>; rel="prev"')]
        values, _, opened = self.lookup_keys(responses)
        self.assertEqual(rows[2]["key"], values["project_restore_key"])
        self.assertEqual(3, opened.call_count)
        self.assertEqual(self.next_page(2), opened.call_args_list[1].args[0].full_url)
        self.assertEqual(self.next_page(3), opened.call_args_list[2].args[0].full_url)

    def test_project_lookup_queries_the_pr_base_or_push_ref_with_a_bounded_request(self):
        for event, ref, base, expected in (("pull_request", "refs/pull/12/merge", "feature/with space", "refs/heads/feature/with space"),
                ("push", "refs/heads/integration-ci-tests", "ignored", "refs/heads/integration-ci-tests")):
            with self.subTest(event=event):
                row = self.cache_row("123-1", ref=expected)
                values, receipt, opened = self.lookup_keys([self.cache_page([row])],
                    GITHUB_EVENT_NAME=event, GITHUB_REF=ref, GITHUB_BASE_REF=base)
                self.assertEqual(row["key"], values["project_restore_key"])
                self.assertEqual(expected, receipt["base_ref"])
                request = opened.call_args.args[0]
                url = urllib.parse.urlsplit(request.full_url)
                self.assertEqual("/api/v3/repos/owner/repository/actions/caches", url.path)
                self.assertEqual(dict(key=[values["project_restore_prefix"]], ref=[expected], per_page=["100"]),
                                 urllib.parse.parse_qs(url.query))
                self.assertEqual("GET", request.get_method())
                self.assertEqual("Bearer synthetic-token", request.get_header("Authorization"))
                self.assertGreater(opened.call_args.kwargs["timeout"], 0)
                self.assertNotIn("synthetic-token", json.dumps(receipt))

    def test_project_restore_receipt_reports_requested_and_actual_keys_even_on_a_miss(self):
        owner, keys, _ = self.native_seed("project")
        preferred = keys["project"]["restore_prefix"] + "100-2"
        keys["project"]["restore_key"] = preferred
        actual = keys["project"]["restore_prefix"] + "99-1"
        for outcome, matched in (("success", preferred), ("success", actual), ("skipped", "")):
            with self.subTest(outcome=outcome, matched=matched), mock.patch.dict(os.environ, self.env), \
                    contextlib.redirect_stdout(io.StringIO()) as result:
                owner.restore(self.root, keys, {"project": matched}, ["project"], outcomes={"project": outcome})
            entry = next(json.loads(line.removeprefix("LEAN_ACTIONS_CACHE "))
                         for line in result.getvalue().splitlines() if line.startswith("LEAN_ACTIONS_CACHE "))
            self.assertEqual(preferred, entry["requested_key"])
            self.assertEqual(matched, entry["key"])

    def test_project_restore_cli_transports_the_requested_key_without_another_lookup(self):
        owner, keys, _ = self.native_seed("project")
        actual = keys["project"]["restore_prefix"] + "99-1"
        preferred = keys["project"]["restore_prefix"] + "100-2"
        arguments = [str(CACHE), "restore", "--repository", str(self.root), "--layers", "project",
                     "--project-key", actual, "--project-restore-key", preferred, "--project-outcome", "success"]
        with mock.patch.dict(os.environ, dict(self.env, GH_TOKEN="synthetic-token"), clear=True), \
                mock.patch.object(urllib.request, "urlopen") as opened, \
                mock.patch.object(sys, "argv", arguments), contextlib.redirect_stdout(io.StringIO()) as result:
            self.assertEqual(0, owner.main())
        opened.assert_not_called()
        entry = json.loads(result.getvalue().splitlines()[0].removeprefix("LEAN_ACTIONS_CACHE "))
        self.assertEqual(preferred, entry["requested_key"])
        self.assertEqual(actual, entry["key"])

    def test_dependency_only_keys_do_not_perform_a_project_lookup(self):
        owner = self.restore_owner()
        arguments = [str(CACHE), "keys", "--repository", str(self.root), "--layers", "dependency"]
        with mock.patch.dict(os.environ, dict(self.env, GH_TOKEN="synthetic-token"), clear=True), \
                mock.patch.object(urllib.request, "urlopen") as opened, \
                mock.patch.object(sys, "argv", arguments), contextlib.redirect_stdout(io.StringIO()) as result:
            self.assertEqual(0, owner.main())
        opened.assert_not_called()
        self.assertNotIn("project_", result.getvalue())
        self.assertNotIn("LEAN_ACTIONS_CACHE", result.getvalue())

    def test_project_keys_cli_uses_an_explicit_repository_with_spaces_from_another_directory(self):
        with tempfile.TemporaryDirectory(prefix="cache contract with spaces ") as temporary:
            directory = pathlib.Path(temporary)
            root = directory / "repository with spaces"
            shutil.copytree(self.root, root)
            result = subprocess.run([sys.executable, "-B", str(CACHE), "keys", "--repository", str(root)],
                cwd=directory, env=dict(PATH=os.environ.get("PATH", ""), GH_TOKEN="",
                    GITHUB_RUN_ID="17", GITHUB_RUN_ATTEMPT="2", GITHUB_EVENT_NAME="push",
                    GITHUB_REF="refs/heads/dev", GITHUB_OUTPUT=str(directory / "output with spaces")),
                capture_output=True, text=True)
            self.assertEqual(0, result.returncode, result.stdout + result.stderr)
            self.assertIn('"reason": "lookup-not-configured"', result.stdout)
            flat = dict(line.split("=", 1) for line in result.stdout.splitlines() if "=" in line)
            self.assertEqual(flat["project_key"], flat["project_restore_key"])
            self.assertIn("project_restore_key=" + flat["project_key"],
                          (directory / "output with spaces").read_text())

    def work(self, report=1, programs=0, **changes):
        path = self.root / "build/lean-cache/build-work.json"
        path.parent.mkdir(parents=True, exist_ok=True)
        value = dict(schema_version=1, run_id="17", run_attempt="2",
                     repository=str(self.root.resolve()), report=report, programs=programs)
        value.update(changes)
        path.write_text(json.dumps(value))
        self.env["STRATALINT_LEAN_BUILD_WORK_FILE"] = str(path)
        return path

    def native_seed(self, layer):
        self.work()
        owner = self.restore_owner()
        owner.dependency_restored_record(self.root).unlink(missing_ok=True)
        with mock.patch.dict(os.environ, self.env):
            keys = owner.actions_keys(self.root)
            target = self.root / keys[layer]["path"]
            target.mkdir(parents=True, exist_ok=True)
            (target / "module.olean").write_bytes(b"native build material")
            with contextlib.redirect_stdout(io.StringIO()) as result:
                owner.snapshot(self.root, keys, [layer])
            self.assertIn(layer + "_ready=true", result.getvalue())
        return owner, keys, target

    def test_native_restore_requires_success_and_the_selected_partition(self):
        for layer in ("dependency", "project"):
            for outcome, key_kind, accepted in (("success", "matching", True),
                    ("failure", "matching", False), ("cancelled", "matching", False),
                    ("success", "foreign", False), ("success", "legacy", False)):
                with self.subTest(layer=layer, outcome=outcome, key=key_kind):
                    owner, keys, target = self.native_seed(layer)
                    key = keys[layer]["key"]
                    if key_kind == "foreign": key = key.replace(REV, "b" * 40)
                    if key_kind == "legacy":
                        key = (key.replace("lean-project-push-", "lean-project-v4-") if layer == "project"
                               else key.replace("-v4-", "-v3-"))
                    sibling = self.root / ".lake" / ("build" if layer == "dependency" else "packages")
                    sibling.mkdir(exist_ok=True)
                    (sibling / "keep").write_bytes(b"other accepted material")
                    with mock.patch.dict(os.environ, self.env), contextlib.redirect_stdout(io.StringIO()) as result:
                        owner.restore(self.root, keys, {layer: key}, [layer], outcomes={layer: outcome})
                    self.assertIn('"status": "restored"' if accepted else '"status": "miss"', result.getvalue())
                    self.assertEqual(accepted, target.exists())
                    self.assertEqual(b"other accepted material", (sibling / "keep").read_bytes())
                    if layer == "project":
                        self.assertIn("STRATALINT_ACTIONS_CACHE_SEEDED=" + str(int(accepted)), result.getvalue())

    def test_unexecuted_action_preserves_current_evidence_and_cannot_claim_a_seed(self):
        owner, keys, target = self.native_seed("project")
        for outcome, key in (("skipped", keys["project"]["key"]), ("", keys["project"]["key"])):
            with self.subTest(outcome=outcome), mock.patch.dict(os.environ, self.env), \
                    contextlib.redirect_stdout(io.StringIO()) as result:
                owner.restore(self.root, keys, {"project": key}, ["project"], outcomes={"project": outcome})
            self.assertIn("STRATALINT_ACTIONS_CACHE_SEEDED=0", result.getvalue())
            self.assertEqual(b"native build material", (target / "module.olean").read_bytes())

    def test_success_without_a_matched_key_discards_partial_action_extraction(self):
        owner, keys, target = self.native_seed("project")
        with mock.patch.dict(os.environ, self.env), contextlib.redirect_stdout(io.StringIO()) as result:
            owner.restore(self.root, keys, {"project": ""}, ["project"], outcomes={"project": "success"})
        self.assertIn("STRATALINT_ACTIONS_CACHE_SEEDED=0", result.getvalue())
        self.assertFalse(target.exists())

    def test_success_without_restored_directory_is_a_miss(self):
        owner = self.restore_owner()
        with mock.patch.dict(os.environ, self.env), contextlib.redirect_stdout(io.StringIO()) as result:
            keys = owner.actions_keys(self.root)
            owner.restore(self.root, keys, {"project": keys["project"]["key"]}, ["project"],
                          outcomes={"project": "success"})
        self.assertIn("STRATALINT_ACTIONS_CACHE_SEEDED=0", result.getvalue())

    def test_dependency_retention_uses_only_registered_small_inputs_after_successful_restore(self):
        owner, keys, target = self.native_seed("dependency")
        original_key = keys["dependency"]["key"]
        with mock.patch.dict(os.environ, self.env), contextlib.redirect_stdout(io.StringIO()):
            owner.restore(self.root, keys, {"dependency": original_key}, ["dependency"],
                          outcomes={"dependency": "success"})
        (self.root / "unrelated.lean").write_text("theorem changed := True.intro\n")
        with mock.patch.dict(os.environ, self.env), \
                mock.patch.object(pathlib.Path, "rglob", side_effect=AssertionError("native directory scan")), \
                contextlib.redirect_stdout(io.StringIO()) as result:
            owner.snapshot(self.root, keys, ["dependency"])
        self.assertIn("retained-restored-dependency", result.getvalue())
        self.assertIn("dependency_ready=false", result.getvalue())
        for file in ("lake-manifest.json", "lean-toolchain", "lakefile.toml"):
            path = self.root / file
            before = path.read_bytes()
            path.write_bytes(before + b"\n")
            with self.subTest(file=file), mock.patch.dict(os.environ, self.env), \
                    contextlib.redirect_stdout(io.StringIO()) as result:
                self.assertEqual(original_key, owner.actions_keys(self.root)["dependency"]["key"])
                owner.snapshot(self.root, keys, ["dependency"])
            self.assertIn("dependency_ready=true", result.getvalue())
            path.write_bytes(before)
        with mock.patch.dict(os.environ, dict(self.env, LEAN_OPTS="-DmaxRecDepth=1024")), \
                contextlib.redirect_stdout(io.StringIO()) as result:
            owner.snapshot(self.root, keys, ["dependency"])
        self.assertIn("dependency_ready=true", result.getvalue())

    def test_dependency_retention_requires_this_round_and_an_accepted_small_receipt(self):
        owner, keys, target = self.native_seed("dependency")
        marker = target / ".stratalint-actions-inputs.json"
        original = marker.read_bytes()
        for defect in ("missing", "invalid", "wrong-type", "stale-round"):
            with self.subTest(defect=defect), mock.patch.dict(os.environ, self.env):
                marker.write_bytes(original)
                if defect == "missing": marker.unlink()
                elif defect == "invalid": marker.write_text("broken")
                elif defect == "wrong-type": marker.write_text("[]")
                with contextlib.redirect_stdout(io.StringIO()) as restored:
                    owner.restore(self.root, keys, {"dependency": keys["dependency"]["key"]}, ["dependency"],
                                  outcomes={"dependency": "success"})
                self.assertIn('"status": "restored"', restored.getvalue())
                if defect == "stale-round":
                    changed = dict(keys, dependency=dict(keys["dependency"], key=keys["dependency"]["key"] + "0"))
                else: changed = keys
                with contextlib.redirect_stdout(io.StringIO()) as saved:
                    owner.snapshot(self.root, changed, ["dependency"])
                self.assertIn("dependency_ready=true", saved.getvalue())

    def test_project_updates_after_each_successful_production_even_with_an_unchanged_report(self):
        owner, keys, target = self.native_seed("project")
        with mock.patch.dict(os.environ, self.env), contextlib.redirect_stdout(io.StringIO()):
            owner.restore(self.root, keys, {"project": keys["project"]["key"]}, ["project"],
                          outcomes={"project": "success"})
        (target / "new.olean").write_bytes(b"newly compiled module")
        with mock.patch.dict(os.environ, self.env), contextlib.redirect_stdout(io.StringIO()) as saved:
            owner.snapshot(self.root, keys, ["project"])
        self.assertIn("project_ready=true", saved.getvalue())
        self.assertEqual(b"newly compiled module", (target / "new.olean").read_bytes())


    def test_native_metadata_save_failure_keeps_produced_material(self):
        owner, keys, target = self.native_seed("dependency")
        with mock.patch.dict(os.environ, self.env), \
                mock.patch.object(owner, "write_small_record", side_effect=OSError("save unavailable")), \
                contextlib.redirect_stdout(io.StringIO()) as result:
            owner.snapshot(self.root, keys, ["dependency"])
        self.assertIn("dependency_ready=false", result.getvalue())
        self.assertEqual(b"native build material", (target / "module.olean").read_bytes())

    def test_native_actions_paths_are_the_registered_build_directories(self):
        owner = self.restore_owner()
        with mock.patch.dict(os.environ, self.env):
            keys = owner.actions_keys(self.root)
        for layer, path in (("dependency", ".lake/packages"), ("project", ".lake/build")):
            self.assertEqual(path, keys[layer]["path"])
            self.assertTrue(keys[layer]["restore_prefix"].startswith(
                "lean-project-push-" if layer == "project" else "lean-dependency-v4-"))

    def test_native_project_authorization_preserves_outputs_without_directory_reads(self):
        self.work()
        owner = self.restore_owner()
        source = self.root / ".lake/build/lib/Module.olean"
        source.parent.mkdir(parents=True)
        source.write_bytes(b"new successful build")
        before = source.stat().st_ino
        with mock.patch.dict(os.environ, self.env), \
                mock.patch.object(pathlib.Path, "rglob", side_effect=AssertionError("native cache directory scan")), \
                contextlib.redirect_stdout(io.StringIO()) as receipts:
            owner.snapshot(self.root, owner.actions_keys(self.root), ["project"])
        self.assertIn("project_ready=true", receipts.getvalue())
        self.assertEqual(before, source.stat().st_ino)
        self.assertEqual(b"new successful build", source.read_bytes())
        self.assertFalse((self.root / "build/lean-cache/project/data").exists())

    def test_project_zero_report_and_program_work_skips_upload(self):
        self.native_seed("project")
        self.work(0, 0)
        ready, receipts = self.snapshot_result()
        self.assertEqual("false", ready["project_ready"])
        self.assertEqual("no-build-work", receipts["project"]["reason"])

    def test_project_report_and_program_only_work_are_publishable_on_push(self):
        self.native_seed("project")
        for report, programs in ((2, 0), (0, 3)):
            with self.subTest(report=report, programs=programs):
                self.work(report, programs)
                ready, receipts = self.snapshot_result()
                self.assertEqual("true", ready["project_ready"])
                self.assertEqual(report + programs, receipts["project"]["build_work"])

    def test_project_unknown_work_never_claims_zero_or_uploads(self):
        self.native_seed("project")
        for defect in ("missing", "malformed", "stale", "negative", "bool", "unknown", "foreign-root", "duplicate-field", "archived-path", "symlink"):
            with self.subTest(defect=defect):
                path = self.work()
                if defect == "missing": path.unlink()
                elif defect == "malformed": path.write_text("[]")
                elif defect == "stale": self.work(run_attempt="1")
                elif defect == "negative": self.work(-1)
                elif defect == "bool": self.work(True)
                elif defect == "unknown": self.work(None)
                elif defect == "foreign-root": self.work(repository="/other")
                elif defect == "duplicate-field": path.write_text(path.read_text().rstrip()[:-1] + ', "report": 0}')
                elif defect == "archived-path":
                    archived = self.root / ".lake/build/work.json"
                    archived.write_bytes(path.read_bytes())
                    self.env["STRATALINT_LEAN_BUILD_WORK_FILE"] = str(archived)
                elif defect == "symlink":
                    link = path.with_suffix(".link")
                    link.symlink_to(path)
                    self.env["STRATALINT_LEAN_BUILD_WORK_FILE"] = str(link)
                ready, receipts = self.snapshot_result()
                self.assertEqual("false", ready["project_ready"])
                self.assertEqual("build-work-unknown", receipts["project"]["reason"])

    def test_pull_requests_never_publish_project_seeds_even_with_build_work(self):
        self.native_seed("project")
        self.native_seed("dependency")
        self.env.update(GITHUB_EVENT_NAME="pull_request", GITHUB_REF="refs/pull/12/merge")
        for report, programs in ((2, 0), (0, 3), (0, 0), (None, None)):
            with self.subTest(report=report, programs=programs):
                self.work(report, programs)
                ready, receipts = self.snapshot_result()
                self.assertEqual("false", ready["project_ready"])
                self.assertEqual("pull-requests-do-not-publish-project-seeds", receipts["project"]["reason"])
                self.assertEqual("true", ready["dependency_ready"])

    def test_only_dev_and_integration_pushes_publish_project_seeds(self):
        self.native_seed("project")
        for ref, expected in (("refs/heads/dev", "true"),
                ("refs/heads/integration-ci-perf-tests", "true"), ("refs/heads/topic", "false")):
            with self.subTest(ref=ref):
                self.env["GITHUB_REF"] = ref
                ready, _ = self.snapshot_result()
                self.assertEqual(expected, ready["project_ready"])

    def test_project_save_authorization_and_dependency_policy_remain_independent(self):
        self.native_seed("project")
        self.native_seed("dependency")
        self.work(0, 0)
        ready, receipts = self.snapshot_result()
        self.assertEqual("true", ready["dependency_ready"])
        self.env["STRATALINT_CACHE_WRITES"] = "false"
        ready, receipts = self.snapshot_result()
        self.assertEqual("false", ready["project_ready"])
        self.assertEqual("false", ready["dependency_ready"])
        self.assertEqual("save-disabled", receipts["project"]["status"])

    def test_project_guard_requires_report_success_and_dependency_requires_check_success(self):
        self.native_seed("project")
        self.native_seed("dependency")
        for report, checked, project, dependency in (("true", "false", "true", "false"),
                ("false", "true", "false", "true"), (None, "true", "false", "true"),
                ("true", "true", "true", "true")):
            with self.subTest(report=report, checked=checked):
                self.env["STRATALINT_CHECK_SUCCEEDED"] = checked
                self.env.pop("STRATALINT_REPORT_SUCCEEDED", None)
                if report is not None: self.env["STRATALINT_REPORT_SUCCEEDED"] = report
                ready, _ = self.snapshot_result()
                self.assertEqual(project, ready["project_ready"])
                self.assertEqual(dependency, ready["dependency_ready"])

    def test_elan_inventory_lists_installed_toolchains_without_modifying_them(self):
        home = self.root / "elan cache with spaces"
        binary = home / "bin/elan"
        binary.parent.mkdir(parents=True)
        binary.write_text("#!/bin/bash\n[[ \"$*\" == 'toolchain list' ]] || exit 23\n"
                          "[[ \"${ELAN_HOME:-}\" == \"$EXPECTED_INVENTORY_HOME\" ]] || exit 24\n"
                          "printf '%s\\n' 'leanprover/lean4:v4.33.0 (default)' 'leanprover/lean4:v4.31.0'\n")
        binary.chmod(0o755)
        toolchains = home / "toolchains/stale"
        toolchains.mkdir(parents=True)
        material = toolchains / "keep"
        material.write_bytes(b"installed toolchain")
        result = subprocess.run(["bash", "--noprofile", "--norc",
            str(CACHE.parents[1] / "workflow/elan-cache-inventory.sh"), str(home)],
            cwd=self.root, env=dict(self.env, EXPECTED_INVENTORY_HOME=str(home)), capture_output=True, text=True)
        self.assertEqual(0, result.returncode, result.stderr)
        self.assertIn("ELAN_CACHE_TOOLCHAINS", result.stdout)
        self.assertIn("leanprover/lean4:v4.33.0 (default)", result.stdout)
        self.assertIn("leanprover/lean4:v4.31.0", result.stdout)
        self.assertEqual(b"installed toolchain", material.read_bytes())

    def restore_owner(self):
        sys.path.insert(0, str(CACHE.parent))
        return importlib.import_module("lean_actions")







if __name__ == "__main__":
    unittest.main()
