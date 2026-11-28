"""Exercise tools pin admission with the GitHub objects seen by the required check."""

import base64
from contextlib import chdir
import importlib.util
import io
import json
from pathlib import Path
import re
import subprocess
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import call, patch

spec = importlib.util.spec_from_file_location("installer", Path(__file__).with_name("install-tools.py"))
installer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(installer)

OLD, A, B_OLD, B_NEW, DEV = (letter * 40 for letter in "01234")
ROOT_PIN, A_PIN = (letter * 40 for letter in "ab")
DIGEST = "d" * 64


def pin(source, number, run):
    return {"version": f"v0.1.1-pr.{number}.{run}.g{source[:12]}", "source_sha": source, "sha256": DIGEST}


class Admission(unittest.TestCase):
    def setUp(self):
        self.objects = {}
        self.legacy = {"version": f"v0.1.1-dev.g{OLD}", "sha256": DIGEST}
        self.a, self.b_old, self.b_new = pin(A, 10, 1), pin(B_OLD, 11, 2), pin(B_NEW, 11, 3)
        self.add_tag(self.legacy["version"], OLD)
        self.add_preview(self.a, ROOT_PIN)
        self.add_preview(self.b_old, ROOT_PIN)
        self.add_preview(self.b_new, A_PIN)
        self.add_ancestry(OLD, A)
        self.add_ancestry(OLD, B_OLD)
        self.add_ancestry(A, B_OLD)  # B was already stacked when it published its old preview.
        self.add_ancestry(A, B_NEW)
        self.add_ancestry(OLD, "dev")
        api = patch.object(installer, "api", side_effect=lambda repo, path, **_: self.objects[repo, path])
        api.start()
        self.addCleanup(api.stop)

    def add_tag(self, version, source):
        self.objects[installer.TOOLS, f"git/ref/tags/{version}"] = {"object": {"type": "commit", "sha": source}}
        self.objects[installer.TOOLS, f"releases/tags/{version}"] = {
            "tag_name": version, "draft": False, "prerelease": "-" in version, "author": {"id": 41898282},
            "assets": [{"name": "trureturing-tools.tar.gz", "state": "uploaded", "digest": f"sha256:{DIGEST}",
                        "uploader": {"id": installer.ACTIONS_BOT}}],
        }

    def add_preview(self, pin, baseline):
        version, source = pin["version"], pin["source_sha"]
        self.add_tag(version, source)
        self.objects[installer.TOOLS, f"git/commits/{source}"] = {
            "message": f"Preview\n\nConsumer-Tools-Base: {baseline}\n",
        }
        number = installer.PR_PREVIEW.fullmatch(version)[1]
        self.objects[installer.TOOLS, f"pulls/{number}"] = {
            "base": {"ref": "dev", "repo": {"full_name": installer.TOOLS}},
            "head": {"repo": {"full_name": installer.TOOLS}, "sha": source, "ref": f"pair-{number}"},
            "draft": False, "state": "open", "merged": False,
        }
        run = {"id": int(number), "run_attempt": 1, "path": ".github/workflows/ci.yml",
               "head_sha": source, "head_branch": f"pair-{number}", "status": "completed",
               "conclusion": "success", "event": "pull_request",
               "head_repository": {"full_name": installer.TOOLS},
               "pull_requests": [{"number": int(number), "head": {"sha": source}}]}
        self.objects[installer.TOOLS, f"actions/workflows/ci.yml/runs?head_sha={source}&status=success&per_page=100"] = [
            {"workflow_runs": [run]}
        ]
        self.objects[installer.TOOLS, f"actions/runs/{number}/attempts/1/jobs?per_page=100"] = {
            "jobs": [
                {"name": name, "conclusion": "success", "steps": [{"name": step, "conclusion": "success"}]}
                for name, step in [
                    ("verify", "Run python3 .github/scripts/test-suites.py standalone"),
                    ("package", "Run python3 package_release.py"),
                    *((f"Consumer fixture {i}", "Exercise candidate tools against the consumer fixture")
                      for i in range(4)),
                ]
            ]
        }

    def add_ancestry(self, base, head, ancestor=None):
        self.objects[installer.TOOLS, f"compare/{base}...{head}?per_page=1"] = {
            "merge_base_commit": {"sha": ancestor or base},
        }

    def test_concurrent_adoption_requires_new_publication_even_for_stacked_head(self):
        self.add_preview(self.b_old, ROOT_PIN)
        installer.verify_adopted_source(self.a, ROOT_PIN, self.legacy, "pull_request")
        installer.verify_adopted_source(self.b_old, ROOT_PIN, self.legacy, "pull_request")
        with self.assertRaisesRegex(ValueError, "publish a new preview"):
            installer.verify_adopted_source(self.b_old, A_PIN, self.a, "pull_request")
        self.add_preview(self.b_new, A_PIN)
        installer.verify_adopted_source(self.b_new, A_PIN, self.a, "pull_request")
        installer.verify_adopted_source(self.b_new, A_PIN, self.a, "pull_request")

    def test_reject_wrong_ancestry_target_and_drift_independently(self):
        pull = self.objects[installer.TOOLS, "pulls/11"]
        self.add_ancestry(A, B_NEW, OLD)
        with self.assertRaisesRegex(ValueError, "contain the previous"):
            installer.verify_adopted_source(self.b_new, A_PIN, self.a, "pull_request")
        self.add_ancestry(A, B_NEW)
        pull["base"]["ref"] = "main"
        with self.assertRaisesRegex(ValueError, "exact published head"):
            installer.verify_adopted_source(self.b_new, A_PIN, self.a, "pull_request")
        pull["base"]["ref"] = "dev"
        pull["head"]["sha"] = B_OLD
        with self.assertRaisesRegex(ValueError, "exact published head"):
            installer.verify_adopted_source(self.b_new, A_PIN, self.a, "pull_request")

    def test_ci_requires_the_exact_tested_head_pr_and_successful_package(self):
        endpoint = f"actions/workflows/ci.yml/runs?head_sha={B_NEW}&status=success&per_page=100"
        run = self.objects[installer.TOOLS, endpoint][0]["workflow_runs"][0]
        jobs = self.objects[installer.TOOLS, "actions/runs/11/attempts/1/jobs?per_page=100"]["jobs"]
        for key, value in (("head_sha", B_OLD), ("head_branch", "other"),
                           ("path", ".github/workflows/other.yml"),
                           ("pull_requests", [{"number": 12, "head": {"sha": B_NEW}}])):
            with self.subTest(key=key), patch.dict(run, {key: value}):
                with self.assertRaisesRegex(ValueError, "no successful tools ci.yml"):
                    installer.verify_adopted_source(self.b_new, A_PIN, self.a, "pull_request")
        jobs[1]["steps"][0]["conclusion"] = "skipped"
        with self.assertRaisesRegex(ValueError, "no successful tools ci.yml"):
            installer.verify_adopted_source(self.b_new, A_PIN, self.a, "pull_request")
        jobs[1]["steps"][0]["conclusion"] = "success"
        with patch.dict(run, {"event": "push", "pull_requests": []}):
            installer.verify_adopted_source(self.b_new, A_PIN, self.a, "pull_request")

    def test_legacy_stable_and_dev_and_pinned_digest_and_source(self):
        installer.verify_adopted_source(self.legacy)
        self.add_tag("v0.2.0", OLD)
        self.add_ancestry(OLD, "main")
        installer.verify_adopted_source({"version": "v0.2.0", "sha256": DIGEST})
        self.assertEqual(installer.parse_pin(json.dumps(self.legacy | {"workflow_sha": DEV})),
                         self.legacy | {"workflow_sha": DEV})
        no_source = {key: value for key, value in self.a.items() if key != "source_sha"}
        with self.assertRaisesRegex(ValueError, "full source_sha"):
            installer.verify_adopted_source(no_source)
        with self.assertRaisesRegex(ValueError, "checksum"):
            installer.verify_adopted_source(self.a | {"sha256": "e" * 64}, ROOT_PIN, self.legacy, "pull_request")
        with self.assertRaisesRegex(ValueError, "full source SHA"):
            installer.verify_adopted_source(self.a | {"source_sha": A[:12] + "f" * 28},
                                            ROOT_PIN, self.legacy, "pull_request")

    def test_legacy_parse_and_malformed_previous_pin(self):
        self.assertEqual(installer.parse_pin(json.dumps(self.legacy)), self.legacy)
        for previous_pin in (None, 0, "a" * 39, "A" * 40, "g" * 40):
            with self.subTest(previous_pin=previous_pin), self.assertRaisesRegex(ValueError, "invalid tools release pin"):
                installer.parse_pin(json.dumps(self.legacy | {"previous_pin": previous_pin}))
        duplicate = json.dumps(self.legacy | {"previous_pin": ROOT_PIN})[:-1] + f', "previous_pin":"{A_PIN}"}}'
        with self.assertRaisesRegex(ValueError, "duplicate field"):
            installer.parse_pin(duplicate)


class Installation(unittest.TestCase):
    workspaces = ("lean-inspector", "lean-inspector-reg", "lean-inspector-interface")

    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name) / "checkout"
        self.root.mkdir()
        self.cache = self.root / "build/tools-releases"
        self.other = Path(directory.name) / "unrelated"
        self.other.mkdir()
        self.archive = Path(directory.name) / "tools.tar.gz"
        self.payload = {"tools/Makefile": b"fixture makefile\n"}
        for workspace in self.workspaces:
            config = "lakefile.lean" if workspace == "lean-inspector" else "lakefile.toml"
            self.payload[f"tools/{workspace}/{config}"] = b"fixture config\n"
            self.payload[f"tools/{workspace}/lake-manifest.json"] = b'{"version":"1.3.0","packages":[]}\n'
        with tarfile.open(self.archive, "w:gz") as archive:
            for name, content in self.payload.items():
                entry = tarfile.TarInfo(name)
                entry.size = len(content)
                archive.addfile(entry, io.BytesIO(content))
        self.pin = {"version": "v0.1.0", "sha256": installer.digest(self.archive)}
        pin_path = self.root / installer.PIN
        pin_path.parent.mkdir()
        pin_path.write_text(json.dumps(self.pin))
        self.omega = {"url": "https://github.com/the-omega-institute/omegamath", "type": "git",
                      "subDir": None, "scope": "the-omega-institute", "rev": A, "name": "omegamath",
                      "manifestFile": "lake-manifest.json", "inputRev": "v0.1.0", "inherited": False,
                      "configFile": "lakefile.toml"}
        self.write_manifest(self.omega)

    def write_manifest(self, omega):
        entries = [{"name": "mathlib", "type": "git", "rev": OLD}]
        if omega is not None:
            entries.append(omega)
        (self.root / "lake-manifest.json").write_text(json.dumps({
            "version": "1.3.0", "packagesDir": ".lake/packages", "packages": entries,
        }))

    def override(self, workspace):
        return self.root / "tools" / workspace / ".lake/package-overrides.json"

    def run_installer(self, *args):
        with (patch.object(installer, "ROOT", self.root), patch.object(installer, "CACHE", self.cache),
              patch.object(sys, "argv", ["install-tools.py", *args]),
              patch.object(installer.subprocess, "check_output", return_value=b"") as commands,
              patch.object(installer, "urlopen", side_effect=AssertionError("unexpected download")),
              chdir(self.other)):
            installer.main()
        commands.assert_called_once_with(["git", "-C", self.root, "ls-files", "--", "tools"])

    def assert_release_bytes(self):
        for name, content in self.payload.items():
            self.assertEqual((self.root / name).read_bytes(), content)
        self.assertEqual((self.root / "tools" / installer.STAMP).read_text(), self.pin["sha256"] + "\n")

    def assert_overrides(self, omega):
        expected = {"version": "1.3.0", "packages": [omega | {"inherited": True}]}
        for workspace in self.workspaces:
            path = self.override(workspace)
            self.assertEqual(json.loads(path.read_bytes()), expected)
        self.assert_release_bytes()
        self.assertFalse((self.root / ".lake/packages/omegamath").exists())

    def test_fresh_installs_exact_overrides_before_package_checkout(self):
        self.run_installer("--archive", str(self.archive))
        self.assert_overrides(self.omega)
        self.assertFalse((self.other / "tools").exists())
        manifest = json.loads((self.root / "lake-manifest.json").read_bytes())
        self.assertEqual(manifest["packages"][-1], self.omega)

    def test_valid_installation_refreshes_overrides_and_preserves_build_files(self):
        self.run_installer("--archive", str(self.archive))
        self.assert_overrides(self.omega)
        build = self.override(self.workspaces[0]).parent / "existing-build"
        build.write_bytes(b"saved compiler output")
        self.override(self.workspaces[1]).unlink()
        updated = self.omega | {"rev": B_NEW, "inputRev": "v0.1.1"}
        self.write_manifest(updated)
        with patch.object(installer, "unpack", side_effect=AssertionError("valid tools should be reused")):
            self.run_installer()
        self.assert_overrides(updated)
        self.assertEqual(build.read_bytes(), b"saved compiler output")
        self.assertEqual(list(self.cache.glob("previous-*")), [])

    def test_protected_base_without_omega_and_stale_override(self):
        self.write_manifest(None)
        self.run_installer("--archive", str(self.archive))
        self.assert_release_bytes()
        self.assertTrue(all(not self.override(workspace).exists() for workspace in self.workspaces))
        self.write_manifest(self.omega)
        self.run_installer()
        self.assert_overrides(self.omega)
        self.write_manifest(None)
        with patch.object(installer, "unpack", side_effect=AssertionError("valid tools should be reused")):
            self.run_installer()
        self.assertTrue(all(not self.override(workspace).exists() for workspace in self.workspaces))
        self.assert_release_bytes()

    def test_sparse_bootstrap_without_manifest(self):
        manifest = self.root / "lake-manifest.json"
        manifest.unlink()
        self.run_installer("--archive", str(self.archive))
        self.assert_release_bytes()
        self.assertTrue(all(not self.override(workspace).exists() for workspace in self.workspaces))
        self.write_manifest(self.omega)
        self.run_installer()
        self.assert_overrides(self.omega)
        manifest.unlink()
        with patch.object(installer, "unpack", side_effect=AssertionError("valid tools should be reused")):
            self.run_installer()
        self.assert_overrides(self.omega)

    def test_rejects_ambiguous_or_unpinned_omega(self):
        path = self.root / "lake-manifest.json"
        for entries in ([self.omega, self.omega], [self.omega | {"rev": A[:12]}],
                        [self.omega | {"type": "path"}]):
            with self.subTest(entries=entries):
                path.write_text(json.dumps({"version": "1.3.0", "packages": entries}))
                with self.assertRaisesRegex(ValueError, "omegamath"):
                    self.run_installer("--archive", str(self.archive))
                self.assertFalse((self.root / "tools").exists())

    def test_cache_revision_only_caches_the_historical_release(self):
        with (patch.object(installer, "ROOT", self.root), patch.object(installer, "CACHE", self.cache),
              patch.object(sys, "argv", ["install-tools.py", "--cache-revision", OLD, "--archive", str(self.archive)]),
              patch.object(installer.subprocess, "check_output", side_effect=[
                  (ROOT_PIN + "\n").encode(),
                  f"100644 blob {A_PIN}\t{installer.PIN}\n".encode(),
                  json.dumps(self.pin).encode(),
              ]) as commands, chdir(self.other)):
            installer.main()
        self.assertEqual(commands.call_args_list, [
            call(["git", "-C", self.root, "rev-parse", "--verify", "--end-of-options", OLD + "^{tree}"]),
            call(["git", "-C", self.root, "ls-tree", "--full-tree", ROOT_PIN, "--", installer.PIN]),
            call(["git", "-C", self.root, "cat-file", "blob", A_PIN]),
        ])
        self.assertFalse((self.root / "tools").exists())
        self.assertEqual(installer.digest(self.cache / (self.pin["sha256"] + ".tar.gz")), self.pin["sha256"])

    def test_failed_atomic_replace_preserves_existing_override(self):
        self.run_installer("--archive", str(self.archive))
        self.assert_overrides(self.omega)
        override = self.override(self.workspaces[0])
        before = override.read_bytes()
        self.write_manifest(self.omega | {"rev": B_NEW})
        with patch.object(installer.os, "replace", side_effect=OSError("fixture replacement failure")):
            with self.assertRaisesRegex(OSError, "fixture replacement failure"):
                self.run_installer()
        self.assertEqual(override.read_bytes(), before)
        self.assertEqual(list(override.parent.iterdir()), [override])


class ConsumerGit(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.repo = Path(directory.name)
        self.git("init", "-b", "dev")
        self.git("config", "user.email", "test@example.invalid")
        self.git("config", "user.name", "Test")
        self.lock = self.repo / installer.PIN
        self.lock.parent.mkdir()
        (self.repo / ".gitattributes").write_bytes((installer.ROOT / ".gitattributes").read_bytes())
        self.before_pin = self.commit()
        self.original_pin = {"version": "v0.1.0", "sha256": DIGEST}
        self.original = self.commit(self.original_pin)
        self.baseline = self.blob(self.original)
        self.a = self.original_pin | {"version": "v0.1.1", "previous_pin": self.baseline}
        self.b = self.original_pin | {"sha256": "b" * 64, "previous_pin": self.baseline}

    def git(self, *args, check=True):
        return subprocess.run(["git", "-C", self.repo, *args], capture_output=True, text=True, check=check)

    def commit(self, lock=None):
        if lock is not None:
            self.lock.write_text(json.dumps(lock, indent=2) + "\n")
        self.git("add", "-A")
        self.git("commit", "--allow-empty", "-m", "Fixture")
        return self.git("rev-parse", "HEAD").stdout.strip()

    def blob(self, commit):
        entry = self.git("ls-tree", commit, "--", installer.PIN).stdout
        return entry.split()[2] if entry else None

    def checkout(self, commit):
        self.git("switch", "--detach", commit)

    def merge(self, ref, *, check=True):
        return self.git("merge", "--no-ff", "-m", "Fixture merge", ref, check=check)

    def api(self, repo, endpoint, **kwargs):
        if endpoint.startswith("compare/"):
            self.assertEqual(kwargs, {"paginate": True})
            base, head = endpoint.split("/")[1].split("?")[0].split("...")
            commits = self.git("rev-list", f"{base}..{head}").stdout.splitlines()
            count = len(commits)
            return [{"base_commit": {"sha": base}, "ahead_by": count,
                     "commits": [{"sha": commit} for commit in page]}
                    for page in (commits[:1], commits[1:]) if page] or [
                        {"base_commit": {"sha": base}, "ahead_by": 0, "commits": []}
                    ]
        if endpoint == "git/ref/heads/dev":
            return {"object": {"sha": self.dev}}
        if endpoint == f"contents/{installer.PIN}?ref={self.dev}":
            return {"sha": self.blob(self.dev)}
        self.fail(f"unexpected API call {repo}/{endpoint}")

    def graphql(self, *args):
        def commit_node(commit):
            tree = self.git("rev-parse", f"{commit}^{{tree}}").stdout.strip()
            return {"oid": commit, "tree": {"oid": tree}}

        query = args[-1]
        objects = {}
        for key, oid in re.findall(r'(o\d+):object\(oid:"([0-9a-f]{40})"\)', query):
            if "... on Commit" in query:
                parents = self.git("show", "-s", "--format=%P", oid).stdout.split()
                objects[key] = commit_node(oid) | {
                    "parents": {"nodes": [commit_node(parent) for parent in parents],
                                "totalCount": len(parents), "pageInfo": {"hasNextPage": False}},
                }
            elif "... on Tree" in query:
                entries = []
                for record in self.git("ls-tree", "-z", oid).stdout.split("\0")[:-1]:
                    fields, name = record.split("\t", 1)
                    mode, _, target = fields.split()
                    entries.append({"nameRaw": base64.b64encode(name.encode()).decode(),
                                    "mode": int(mode, 8), "oid": target})
                objects[key] = {"oid": oid, "entries": entries}
            else:
                self.fail("unexpected GraphQL object selection")
        self.assertTrue(objects)
        return {"data": {"repository": objects}}

    def verify(self, *, event="pull_request", checkout=None, graphql=None):
        with (patch.object(installer, "ROOT", checkout or self.repo),
              patch.object(installer, "api", side_effect=self.api),
              patch.object(installer, "github", side_effect=graphql or self.graphql),
              patch.object(installer, "verify_adopted_source") as source):
            installer.verify_adoption(event, installer.CONSUMER)
            return source

    def test_parallel_disjoint_edits_conflict_as_one_lock_after_both_pass(self):
        a = self.commit(self.a)
        self.checkout(self.original)
        b = self.commit(self.b)
        self.dev = self.original
        for branch in (a, b):
            self.checkout(self.original)
            self.merge(branch)
            self.verify().assert_called_once()
        self.checkout(a)
        merge = self.merge(b, check=False)
        self.assertEqual(merge.returncode, 1, merge.stderr)
        self.assertIn(f"Cannot merge binary files: {installer.PIN}", merge.stdout + merge.stderr)

    def test_clean_stacked_merge_would_reuse_stale_approval(self):
        a = self.commit(self.a)
        # The side parent carries the third pin, so a first-parent scan misses it.
        self.checkout(self.original)
        self.commit(self.b)
        self.git("merge", "--no-ff", "-s", "ours", "-m", "Fixture side merge", a)
        b = self.git("rev-parse", "HEAD").stdout.strip()
        self.checkout(self.original)
        self.dev = self.original
        self.merge(b)
        with self.assertRaisesRegex(ValueError, "intermediate pin edits"):
            self.verify()
        self.git("branch", "tested-merge")
        with tempfile.TemporaryDirectory() as path:
            self.git("clone", "--depth=2", "--branch=tested-merge", self.repo.as_uri(), path)
            shallow = Path(path)
            with patch.object(installer, "ROOT", shallow):
                self.assertNotIn(a, installer.git("rev-list", "HEAD").decode().split())
            with self.assertRaisesRegex(ValueError, "intermediate pin edits"):
                self.verify(checkout=shallow)
        # After A lands as a merge commit, Git takes A as the merge base.
        # Even with -merge, it now merges B cleanly.
        self.checkout(self.original)
        self.merge(a)
        self.dev = self.git("rev-parse", "HEAD").stdout.strip()
        self.assertEqual(self.git("merge-base", self.dev, b).stdout.strip(), a)
        self.merge(b)
        with self.assertRaisesRegex(ValueError, "previous_pin must match"):
            self.verify()
        self.checkout(self.dev)
        refreshed = self.commit(self.b | {"previous_pin": self.blob(self.dev)})
        self.checkout(self.dev)
        self.merge(refreshed)
        self.verify().assert_called_once()
        self.verify().assert_called_once()

    def test_pin_neutral_head_with_intermediate_change_is_rejected(self):
        a = self.commit(self.a)
        b = self.commit(self.original_pin)
        self.checkout(self.original)
        self.dev = self.original
        self.merge(b)
        with self.assertRaisesRegex(ValueError, "intermediate pin edits"):
            self.verify()
        self.checkout(self.original)
        self.merge(a)
        self.merge(b)
        self.assertEqual(self.blob("HEAD"), self.baseline)

    def test_rollback_has_new_generation_and_stale_consumer_conflicts(self):
        a = self.commit(self.a)
        rollback = self.commit(self.original_pin | {"previous_pin": self.blob(a)})
        self.assertNotEqual(self.blob(rollback), self.baseline)
        self.dev = a
        self.checkout(a)
        self.merge(rollback)
        self.verify().assert_called_once()
        self.checkout(self.original)
        stale = self.commit(self.b)
        self.checkout(rollback)
        self.assertEqual(self.merge(stale, check=False).returncode, 1)

    def test_unrelated_updates_preserve_eligibility_and_pin(self):
        a = self.commit(self.a)
        self.checkout(self.original)
        (self.repo / "unrelated").write_text("change")
        unrelated = self.commit()
        self.dev = unrelated
        self.merge(a)
        self.verify().assert_called_once()
        self.checkout(a)
        self.dev = a
        self.merge(unrelated)
        self.verify().assert_not_called()

    def test_content_pr_can_merge_dev_across_a_tools_adoption(self):
        adopted = self.commit(self.a)
        next_adoption = self.commit(self.b | {"previous_pin": self.blob(adopted)})
        self.checkout(self.original)
        (self.repo / "content").write_text("content before adoption")
        self.commit()
        self.merge(adopted)
        (self.repo / "content").write_text("content after adoption")
        content = self.commit()
        self.checkout(next_adoption)
        self.dev = next_adoption
        self.merge(content)
        self.verify().assert_not_called()

    def test_content_pr_can_inherit_absence_before_merging_the_first_pin(self):
        self.checkout(self.before_pin)
        self.lock.parent.mkdir()
        (self.lock.parent / "notes.文").write_text("branch started before tools were pinned")
        (self.lock.parent / "notes").mkdir()
        (self.lock.parent / "notes" / "content").touch()
        self.commit()
        self.commit()
        self.commit()
        self.merge(self.original)
        refreshed = self.git("rev-parse", "HEAD").stdout.strip()
        self.checkout(self.original)
        self.merge(refreshed)
        self.verify().assert_not_called()

    def test_history_rejects_incomplete_or_mismatched_git_objects(self):
        first = self.commit()
        head = self.commit()
        tree = self.git("rev-parse", f"{head}:Meta").stdout.strip()
        self.checkout(self.original)
        self.merge(head)

        def corrupt(query, field, value):
            def response(*args):
                result = self.graphql(*args)
                if query == "errors" and "... on Commit" in args[-1]:
                    result["errors"] = [{"type": "NOT_FOUND"}]
                for key, obj in result["data"]["repository"].items():
                    if query == "tree" and obj["oid"] == tree:
                        if field == "entries" and value == "duplicate":
                            obj["entries"].append(obj["entries"][0])
                        else:
                            obj[field] = value
                    if query == "parents" and obj["oid"] == head:
                        obj["parents"][field] = value
                    if query == "commit" and obj["oid"] == first:
                        result["data"]["repository"][key] = value
                return result
            return response

        for query, field, value, message in (
            ("errors", "", None, "could not inspect"),
            ("commit", "", None, "missing or mismatched"),
            ("parents", "nodes", [], "incomplete consumer parents"),
            ("parents", "pageInfo", {"hasNextPage": True}, "incomplete consumer parents"),
            ("parents", "nodes", [{"oid": first, "tree": {"oid": tree}}], "inconsistent consumer commit tree"),
            ("tree", "oid", ROOT_PIN, "missing or mismatched"),
            ("tree", "entries", None, "missing entries"),
            ("tree", "entries", [], "incomplete or inconsistent entries"),
            ("tree", "entries", "duplicate", "malformed entries"),
        ):
            with self.subTest(query=query, field=field, value=value), self.assertRaisesRegex(ValueError, message):
                self.verify(graphql=corrupt(query, field, value))

    def test_history_rejects_nonregular_pin(self):
        self.lock.unlink()
        self.lock.symlink_to("other.json")
        self.commit()
        self.lock.unlink()
        candidate = self.commit(self.original_pin)
        self.checkout(self.original)
        self.merge(candidate)
        with self.assertRaisesRegex(ValueError, "must be a regular file"):
            self.verify()

    def test_missing_wrong_and_stale_predecessors_are_rejected(self):
        for edited in (self.original_pin | {"version": "v0.1.2"}, self.a | {"previous_pin": ROOT_PIN}):
            self.checkout(self.original)
            candidate = self.commit(edited)
            self.checkout(self.original)
            self.dev = self.original
            self.merge(candidate)
            with self.assertRaisesRegex(ValueError, "previous_pin must match"):
                self.verify()
            with self.assertRaisesRegex(ValueError, "previous_pin must match"):
                self.verify(event="push")
        self.checkout(self.original)
        candidate = self.commit(self.b)
        self.checkout(self.original)
        newer = self.commit(self.a)
        self.dev = newer
        self.checkout(self.original)
        self.merge(candidate)
        with self.assertRaisesRegex(ValueError, "consumer dev changed"):
            self.verify()

    def test_missing_intermediate_pin_and_truncated_compare_are_rejected(self):
        self.lock.unlink()
        self.commit()
        candidate = self.commit(self.b)
        self.checkout(self.original)
        self.dev = self.original
        self.merge(candidate)
        with self.assertRaisesRegex(ValueError, "intermediate pin edits"):
            self.verify()
        with patch.object(installer, "api", return_value=[
            {"base_commit": {"sha": self.original}, "ahead_by": 2, "commits": [{"sha": candidate}]},
        ]):
            with self.assertRaisesRegex(ValueError, "incomplete consumer PR commit range"):
                installer.pr_only_commits(installer.CONSUMER, self.original, candidate)


if __name__ == "__main__":
    unittest.main()
