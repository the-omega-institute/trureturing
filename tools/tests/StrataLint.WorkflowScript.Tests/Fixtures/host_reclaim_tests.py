"""Real Git and filesystem contracts for conservative host artifact reclamation."""

import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import socket
import stat
import subprocess
import sys
import tempfile
import time
import types
import unittest
from unittest.mock import patch

ROOT = Path(sys.argv.pop(1)).resolve()
sys.path.insert(0, str(ROOT / "tools/scripts/worktree"))
import lean_cache_release as release

spec = importlib.util.spec_from_file_location("host_cleanup", ROOT / "tools/scripts/host-cleanup.py")
cleanup = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cleanup)


class HostReclaimTests(unittest.TestCase):
    def setUp(self):
        self.workspace = tempfile.TemporaryDirectory(prefix="host reclaim with spaces ")
        self.addCleanup(self.workspace.cleanup)
        self.root = Path(self.workspace.name).resolve()
        self.now = 1700100000
        self.cutoff = self.now - 24 * 3600
        clock = patch.object(time, "time", return_value=self.now)
        clock.start()
        self.addCleanup(clock.stop)
        self.main = self.root / "main"
        self.main.mkdir()
        self.git(self.main, "init", "--initial-branch=dev")
        self.git(self.main, "config", "user.name", "Reclaim Tests")
        self.git(self.main, "config", "user.email", "reclaim@example.invalid")
        (self.main / "source").write_text("retained\n")
        (self.main / ".gitignore").write_text(".lake/\n")
        self.git(self.main, "add", ".")
        self.git(self.main, "commit", "-m", "Retain baseline")

    def git(self, root, *args):
        return subprocess.run(["git", "-C", str(root), *map(str, args)], check=True,
                              capture_output=True, text=True).stdout.strip()

    def clone(self, name="candidate"):
        target = self.root / "artifacts" / name
        self.git(self.main, "clone", "--no-hardlinks", self.main, target)
        self.git(target, "config", "user.name", "Reclaim Tests")
        self.git(target, "config", "user.email", "reclaim@example.invalid")
        return target

    def age(self, root):
        for directory, names, files in os.walk(root, followlinks=False):
            for path in [Path(directory), *(Path(directory) / name for name in names + files)]:
                os.utime(path, (self.cutoff - 10, self.cutoff - 10), follow_symlinks=False)

    def clean(self, target, delete=True):
        return cleanup.clean_candidate(target, self.cutoff, [], delete=delete, repository=self.main)

    def make_endpoint(self, path, kind):
        if kind == "fifo":
            os.mkfifo(path)
        else:
            temporary = self.root / "socket"
            with socket.socket(socket.AF_UNIX) as handle:
                handle.bind(str(temporary))
            temporary.rename(path)

    def lsof_process(self, pid):
        run = subprocess.run
        def observe(command, **kwargs):
            if command[0] == "lsof":
                command = [*command, "-p", str(pid)]
            return run(command, **kwargs)
        return patch.object(cleanup.subprocess, "run", side_effect=observe)

    def test_case_inventory_lists_every_case_without_running_git(self):
        environment = dict(os.environ, PATH="")
        result = subprocess.run([sys.executable, "-B", __file__, str(ROOT), "--list-tests"],
                                capture_output=True, text=True, env=environment)
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        expected = ["HostReclaimTests." + name
                    for name in unittest.defaultTestLoader.getTestCaseNames(type(self))]
        self.assertEqual(expected, json.loads(result.stdout))
        self.assertEqual("", result.stderr)

    def test_empty_git_skeleton_is_an_ordinary_artifact(self):
        target = self.root / "skeleton"
        (target / ".git/objects/pack").mkdir(parents=True)
        self.age(target)
        result = cleanup.clean_candidate(target, self.cutoff, [], delete=True)
        self.assertEqual("removed", result["action"], result)
        self.assertFalse(target.exists())

    def test_retained_repository_is_removed_and_main_survives(self):
        target = self.clone()
        self.age(target)
        self.assertEqual("would_remove", self.clean(target, False)["action"])
        self.assertEqual("removed", self.clean(target)["action"])
        self.assertTrue((self.main / "source").exists())

    def test_main_direct_alternate_dependency_retains_candidate(self):
        self.check_main_alternate_dependency(False)

    def test_main_indirect_alternate_dependency_retains_candidate(self):
        self.check_main_alternate_dependency(True)

    def check_main_alternate_dependency(self, indirect):
        target = self.clone()
        shutil.rmtree(self.main)
        if indirect:
            bridge = self.root / "bridge"
            self.git(target, "clone", "--shared", target, bridge)
            self.git(bridge, "clone", "--shared", bridge, self.main)
        else:
            self.git(target, "clone", "--shared", target, self.main)
        self.git(self.main, "cat-file", "-e", "HEAD")
        self.age(target)
        result = self.clean(target)
        self.assertEqual("kept", result["action"], result)
        self.assertEqual("repository_source_dependency", result["reason"], result)
        self.assertTrue(target.exists())
        self.git(self.main, "cat-file", "-e", "HEAD")

    def test_unrelated_main_alternate_does_not_block_reclamation(self):
        target = self.clone()
        backing = self.clone("backing")
        (self.main / ".git/objects/info/alternates").write_text(str(backing / ".git/objects") + "\n")
        self.age(target)
        self.assertEqual("removed", self.clean(target)["action"])
        self.git(self.main, "cat-file", "-e", "HEAD")

    def test_main_alternate_symlink_dependency_retains_candidate(self):
        target = self.clone()
        alias = self.root / "object alias"
        alias.symlink_to(target / ".git/objects", target_is_directory=True)
        (self.main / ".git/objects/info/alternates").write_text(str(alias) + "\n")
        self.age(target)
        result = self.clean(target)
        self.assertEqual("repository_source_dependency", result["reason"], result)
        self.assertTrue(target.exists())

    def test_main_alternate_created_before_deletion_retains_candidate(self):
        target = self.clone()
        self.age(target)
        def activity():
            (self.main / ".git/objects/info/alternates").write_text(str(target / ".git/objects") + "\n")
            return set()
        result = cleanup.clean_candidate(target, self.cutoff, [], True, repository=self.main, activity=activity)
        self.assertEqual("changed", result["reason"], result)
        self.assertTrue(target.exists())

    def test_main_alternate_alias_inside_candidate_retains_candidate(self):
        self.check_source_alternate_metadata_dependency(False)

    def test_main_alternates_file_inside_candidate_retains_candidate(self):
        self.check_source_alternate_metadata_dependency(True)

    def check_source_alternate_metadata_dependency(self, linked_file):
        target = self.clone()
        backing = self.clone("backing")
        shutil.rmtree(self.main)
        self.git(backing, "clone", "--shared", backing, self.main)
        alternates = self.main / ".git/objects/info/alternates"
        if linked_file:
            listing = target / ".git/alternate-list"
            listing.write_text(str(backing / ".git/objects") + "\n")
            alternates.unlink()
            alternates.symlink_to(listing)
        else:
            alias = target / ".git/object-alias"
            alias.symlink_to(backing / ".git/objects", target_is_directory=True)
            alternates.write_text(str(alias) + "\n")
        self.git(self.main, "cat-file", "-e", "HEAD")
        self.age(target)
        result = self.clean(target)
        self.assertEqual("repository_source_dependency", result["reason"], result)
        self.assertTrue(target.exists())
        self.git(self.main, "cat-file", "-e", "HEAD")

    def test_main_shallow_tip_does_not_certify_missing_ancestors(self):
        target = self.clone()
        (target / "source").write_text("next commit")
        self.git(target, "commit", "-am", "Advance candidate")
        ancestor = self.git(target, "rev-parse", "HEAD^")
        self.git(target, "remote", "remove", "origin")
        shutil.rmtree(self.main)
        self.git(target, "clone", "--depth=1", target.as_uri(), self.main)
        self.git(target, "reflog", "expire", "--expire=all", "--all")
        missing = subprocess.run(["git", "-C", str(self.main), "cat-file", "-e", ancestor],
                                 capture_output=True)
        self.assertNotEqual(0, missing.returncode)
        self.age(target)
        result = self.clean(target)
        self.assertEqual("repository_unverifiable", result["reason"], result)
        self.assertTrue(target.exists())
        self.git(target, "cat-file", "-e", ancestor)

    def test_main_partial_clone_retains_independent_repository(self):
        self.check_incomplete_main("extensions.partialclone", "origin")

    def test_main_promisor_remote_retains_independent_repository(self):
        self.check_incomplete_main("remote.origin.promisor", "true")

    def check_incomplete_main(self, key, value):
        target = self.clone()
        self.git(self.main, "config", key, value)
        self.age(target)
        result = self.clean(target)
        self.assertEqual("repository_unverifiable", result["reason"], result)
        self.assertTrue(target.exists())

    def test_main_promisor_pack_retains_independent_repository(self):
        target = self.clone()
        self.git(self.main, "repack", "-ad")
        pack = next((self.main / ".git/objects/pack").glob("*.pack"))
        pack.with_suffix(".promisor").touch()
        self.age(target)
        result = self.clean(target)
        self.assertEqual("repository_unverifiable", result["reason"], result)
        self.assertTrue(target.exists())

    def test_unique_dirty_stash_dangling_and_unfinished_repositories_are_retained(self):
        for kind, expected in (("unique", "repository_unique_commits"),
                               ("dirty", "repository_dirty"), ("stash", "repository_stash"),
                               ("dangling", "repository_unique_commits"),
                               ("reflog", "repository_unique_commits"),
                               ("operation", "repository_operation"), ("lock", "repository_lock")):
            with self.subTest(kind=kind):
                target = self.clone(kind)
                baseline = self.git(target, "rev-parse", "HEAD")
                if kind in ("unique", "dangling", "reflog"):
                    (target / "source").write_text(kind)
                    self.git(target, "commit", "-am", kind)
                    if kind != "unique":
                        self.git(target, "reset", "--hard", baseline)
                    if kind == "dangling":
                        self.git(target, "reflog", "expire", "--expire=all", "--all")
                elif kind in ("dirty", "stash"):
                    (target / "untracked").write_text("private")
                    if kind == "stash":
                        self.git(target, "stash", "push", "-u")
                else:
                    (target / ".git" / ("MERGE_HEAD" if kind == "operation" else "index.lock")).write_text(baseline)
                self.age(target)
                result = self.clean(target)
                self.assertEqual(expected, result["reason"], result)
                self.assertTrue(target.exists())

    def test_external_shallow_partial_and_alternate_repositories_are_retained(self):
        for kind in ("external", "shallow", "partial", "alternates"):
            with self.subTest(kind=kind):
                target = self.clone(kind)
                if kind == "external":
                    metadata = self.root / "external.git"
                    (target / ".git").rename(metadata)
                    (target / ".git").write_text("gitdir: " + str(metadata) + "\n")
                elif kind == "shallow":
                    (target / ".git/shallow").write_text(self.git(target, "rev-parse", "HEAD") + "\n")
                elif kind == "partial":
                    self.git(target, "config", "remote.origin.promisor", "true")
                else:
                    (target / ".git/objects/info/alternates").write_text(str(self.main / ".git/objects") + "\n")
                self.age(target)
                result = self.clean(target)
                self.assertEqual("repository_unverifiable", result["reason"], result)
                self.assertTrue(target.exists())

    def test_repository_with_its_own_external_worktree_is_retained(self):
        target = self.clone()
        external = self.root / "external worktree"
        self.git(target, "worktree", "add", "-b", "attached", external)
        (external / "source").write_text("staged version")
        self.git(external, "add", "source")
        self.age(target)
        result = self.clean(target)
        self.assertEqual("repository_unverifiable", result["reason"], result)
        self.assertTrue(self.git(external, "ls-files", "--stage", "source"))

    def test_indirect_external_alternates_are_retained(self):
        target = self.clone()
        internal = target / ".git/objects/internal"
        (internal / "info").mkdir(parents=True)
        (internal / "pack").mkdir()
        (target / ".git/objects/info/alternates").write_text(str(internal) + "\n")
        (internal / "info/alternates").write_text(str(self.main / ".git/objects") + "\n")
        self.age(target)
        result = self.clean(target)
        self.assertEqual("repository_unverifiable", result["reason"], result)
        self.assertTrue(target.exists())

    def test_candidates_inside_repository_preserve_tracked_and_private_files(self):
        target = self.clone()
        private = target / "private"
        private.write_text("uncommitted content")
        self.age(target)
        for path in (target / "source", private):
            result = self.clean(path)
            self.assertEqual("repository_unverifiable", result["reason"], result)
            self.assertTrue(path.exists())
        (target / "source").write_text("modified tracked content")
        self.age(target)
        self.run_sweep(artifact_root=target)
        self.assertEqual("modified tracked content", (target / "source").read_text())
        self.assertTrue(private.exists())

    def test_external_registered_worktree_build_is_preserved(self):
        target = self.clone()
        external = target / "external worktree"
        self.git(target, "worktree", "add", "-b", "attached", external)
        build = external / ".lake/build"
        build.mkdir(parents=True)
        (build / "generated").write_text("cache")
        self.age(external)
        result = cleanup.clean_generated_build(external / ".lake", self.cutoff, [],
                                               self.main, True, lambda: set())
        self.assertEqual("protected", result["reason"], result)
        self.run_sweep()
        self.assertTrue(build.exists())

    def test_nested_project_tracked_build_and_local_edits_are_retained(self):
        target = self.clone()
        build = target / "subproject/.lake/build"
        build.mkdir(parents=True)
        source = build / "source.lean"
        source.write_text("tracked source")
        self.git(target, "add", "-f", "subproject/.lake/build/source.lean")
        self.git(target, "commit", "-m", "Track nested source")
        source.write_text("private local edits")
        self.age(target)
        self.run_sweep()
        self.assertTrue(source.exists())
        self.assertEqual("private local edits", source.read_text())

    def test_retained_tip_scale_uses_bounded_git_object_and_ancestry_queries(self):
        count = 13692
        records = []
        for index in range(count):
            name = "tip-" + str(index)
            records.append("commit refs/heads/scale\nmark :" + str(index + 1) + "\ncommitter Test <test@example.invalid> "
                           "1700000000 +0000\ndata " + str(len(name)) + "\n" + name + "\n\n")
        marks = self.root / "marks"
        subprocess.run(["git", "-C", str(self.main), "fast-import", "--quiet", "--export-marks=" + str(marks)],
                       input="".join(records), text=True, capture_output=True, check=True)
        tips = sorted(("refs/heads/tip-" + row.split()[0][1:], row.split()[1])
                      for row in marks.read_text().splitlines())
        (self.main / ".git/packed-refs").write_text("# pack-refs with: peeled fully-peeled sorted\n" +
            "".join(oid + " " + name + "\n" for name, oid in tips))
        target = self.clone()
        self.age(target)
        run = cleanup.subprocess.run
        commands = []
        def observed(*args, **kwargs):
            commands.append(args[0])
            if (sum("cat-file" in command for command in commands) > 2
                    or sum("merge-base" in command for command in commands) > 2):
                raise AssertionError("retained tip certification exceeds the bounded Git command budget")
            return run(*args, **kwargs)
        with patch.object(cleanup.subprocess, "run", side_effect=observed):
            result = self.clean(target, False)
        self.assertEqual("would_remove", result["action"], result)
        self.assertLessEqual(sum("cat-file" in command for command in commands), 2)
        self.assertLessEqual(sum("merge-base" in command for command in commands), 2)

    def test_corrupt_reflog_and_main_dangling_objects_do_not_certify_retention(self):
        target = self.clone()
        (target / ".git/logs/HEAD").write_text("corrupt\n")
        self.age(target)
        self.assertEqual("repository_unverifiable", self.clean(target)["reason"])
        target = self.clone("main-dangling")
        (target / "source").write_text("unique")
        self.git(target, "commit", "-am", "Unretained")
        oid = self.git(target, "rev-parse", "HEAD")
        self.git(self.main, "fetch", target, oid)
        self.age(target)
        self.assertEqual("repository_unique_commits", self.clean(target)["reason"])

    def test_nested_repository_requires_its_own_retention_proof(self):
        parent = self.root / "parent"
        parent.mkdir()
        safe = self.clone("safe")
        safe.rename(parent / "safe")
        unsafe = self.clone("unsafe")
        (unsafe / "source").write_text("unique")
        self.git(unsafe, "commit", "-am", "Unique nested history")
        unsafe.rename(parent / "unsafe")
        self.age(parent)
        self.assertEqual("repository_unique_commits", self.clean(parent)["reason"])
        self.assertTrue((parent / "safe").exists())

    def test_repository_changed_before_delete_is_retained(self):
        target = self.clone()
        self.age(target)
        inspect = cleanup.inspect_candidate
        calls = 0
        def raced(*args, **kwargs):
            nonlocal calls
            calls += 1
            if calls == 2:
                (target / "source").write_text("concurrent work")
            return inspect(*args, **kwargs)
        with patch.object(cleanup, "inspect_candidate", side_effect=raced):
            result = self.clean(target)
        self.assertEqual("changed", result["reason"])
        self.assertTrue(target.exists())

    def test_bare_repository_is_preserved(self):
        bare = self.root / "bare"
        self.git(self.main, "clone", "--bare", self.main, bare)
        self.age(bare)
        self.assertEqual("repository_unverifiable", self.clean(bare)["reason"])

    def test_tracked_build_is_preserved(self):
        target = self.clone()
        build = target / ".lake/build"
        build.mkdir(parents=True)
        (build / "source").write_text("tracked source")
        self.git(target, "add", "-f", ".lake/build/source")
        self.git(target, "commit", "-m", "Track source in build")
        self.age(target)
        self.run_sweep()
        self.assertTrue(build.exists())

    def test_build_tracked_after_first_check_is_preserved(self):
        target = self.clone()
        build = target / ".lake/build"
        build.mkdir(parents=True)
        (build / "generated").write_text("source")
        self.age(target)
        inspect = cleanup.inspect_candidate
        calls = 0
        def track(*args, **kwargs):
            nonlocal calls
            calls += 1
            if calls == 2:
                self.git(target, "add", "-f", ".lake/build/generated")
            return inspect(*args, **kwargs)
        with patch.object(cleanup, "inspect_candidate", side_effect=track):
            result = cleanup.clean_generated_build(target / ".lake", self.cutoff, [], self.main, True, lambda: set())
        self.assertEqual("changed", result["reason"], result)
        self.assertTrue(build.exists())

    @unittest.skipUnless(sys.platform == "darwin" and shutil.which("lsof"), "macOS lsof")
    def test_real_lsof_observes_live_fifo_and_socket_handles(self):
        with self.lsof_process(os.getpid()):
            self.check_live_fifo_and_socket_handles()

    def check_live_fifo_and_socket_handles(self):
        for kind in ("fifo", "socket"):
            endpoint = self.root / kind
            if kind == "fifo":
                os.mkfifo(endpoint)
                handle = os.open(endpoint, os.O_RDONLY | os.O_NONBLOCK)
                close = lambda: os.close(handle)
            else:
                handle = socket.socket(socket.AF_UNIX)
                handle.bind(str(endpoint))
                close = handle.close
            self.age(self.root)
            try:
                self.assertEqual("protected", cleanup.clean_candidate(endpoint, self.cutoff, [], True)["reason"])
            finally:
                close()
            self.assertEqual("removed", cleanup.clean_candidate(endpoint, self.cutoff, [], True)["action"])

    def test_tag_objects_and_safe_nested_repositories_are_reclaimable(self):
        self.git(self.main, "tag", "-a", "retained", "-m", "Retained tag")
        first = self.clone("first")
        second = self.clone("second")
        parent = self.root / "artifacts"
        self.age(parent)
        self.assertEqual("removed", self.clean(parent)["action"])
        self.assertFalse(first.exists())
        self.assertFalse(second.exists())

    def test_registration_and_activity_changes_before_delete_are_retained(self):
        for change in ("registration", "activity"):
            target = self.clone(change)
            self.age(target)
            if change == "registration":
                with patch.object(cleanup, "registered_worktrees", side_effect=[[self.main], [target], [self.main, target]]):
                    result = self.clean(target)
            else:
                result = cleanup.clean_candidate(target, self.cutoff, [], delete=True, repository=self.main,
                                                 activity=lambda: {target / "source"})
            self.assertEqual("changed", result["reason"], result)
            self.assertTrue(target.exists())

    def run_sweep(self, trees=(), artifact_root=None, expected_exit=0, active=()):
        options = cleanup.argparse.Namespace(repository=self.main, base="dev",
            codex_home=self.root / "codex", sshx_home=self.root / "sshx",
            tmp_root=[artifact_root or self.root / "artifacts"], min_age_hours=24, delete=True, verbose=True)
        output = io.StringIO()
        registrations = cleanup.registered_worktrees
        with patch.object(cleanup, "clean_worktrees", return_value=0), \
             (patch.object(cleanup, "active_paths", wraps=cleanup.active_paths) if active is None
              else patch.object(cleanup, "active_paths", return_value=set(active))), \
             patch.object(cleanup, "registered_worktrees", side_effect=lambda source:
                 [self.main, *trees] if source.resolve() == self.main else registrations(source)), \
             contextlib.redirect_stdout(output):
            self.assertEqual(expected_exit, cleanup.run_clean(options), output.getvalue())
        return [json.loads(line) for line in output.getvalue().splitlines()]

    def test_artifact_root_inside_cache_uses_guarded_owners(self):
        project = self.root / "artifacts/project"
        lake = project / ".lake"
        for name in (".release-token", ".release-backup-token", "packages", "build"):
            (lake / name).mkdir(parents=True)
            (lake / name / "source").write_text("keep")
        self.age(project)
        with release.cache_guard(project):
            self.run_sweep(artifact_root=lake)
        self.assertEqual(4, len(list(lake.iterdir())))
        self.run_sweep(artifact_root=lake)
        self.assertTrue((lake / ".release-token/source").exists())
        self.assertTrue((lake / ".release-backup-token/source").exists())
        self.assertTrue((lake / "packages/source").exists())
        self.assertFalse((lake / "build").exists())

    def test_ipc_candidates_inside_repository_are_preserved(self):
        target = self.clone()
        endpoints = [target / kind for kind in ("fifo", "socket")]
        for endpoint in endpoints:
            self.make_endpoint(endpoint, endpoint.name)
        self.age(target)
        with patch.object(cleanup.sys, "platform", "darwin"):
            rows = self.run_sweep(artifact_root=target)
        reasons = {row.get("path"): row.get("reason") for row in rows}
        for endpoint in endpoints:
            self.assertTrue(endpoint.exists())
            self.assertEqual("repository_unverifiable", reasons.get(str(endpoint)))

    def test_host_sweep_ipc_activity_protects_fifo_and_socket_endpoints(self):
        artifacts = self.root / "artifacts"
        artifacts.mkdir()
        endpoints, active = [], []
        for kind in ("fifo", "socket"):
            for state in ("idle", "active"):
                endpoint = artifacts / (kind + "-" + state)
                self.make_endpoint(endpoint, kind)
                endpoints.append(endpoint)
                if state == "active":
                    active.append(endpoint)
        self.age(artifacts)
        with patch.object(cleanup.sys, "platform", "darwin"):
            rows = self.run_sweep(active=active)
        items = {row.get("path"): row for row in rows}
        for endpoint in endpoints:
            self.assertEqual(endpoint in active, endpoint.exists())
            self.assertEqual("kept" if endpoint in active else "removed", items[str(endpoint)]["action"])
            self.assertEqual("protected" if endpoint in active else None, items[str(endpoint)]["reason"])

    def test_ipc_candidates_inside_registered_worktree_are_preserved(self):
        target = self.root / "registered worktree"
        self.git(self.main, "worktree", "add", "-b", "registered", target)
        self.assertTrue((target / ".git").is_file())
        endpoints = [target / kind for kind in ("fifo", "socket")]
        for endpoint in endpoints:
            self.make_endpoint(endpoint, endpoint.name)
        self.age(target)
        with patch.object(cleanup.sys, "platform", "darwin"):
            rows = self.run_sweep([target], artifact_root=target)
        reasons = {row.get("path"): row.get("reason") for row in rows}
        for endpoint in endpoints:
            self.assertTrue(endpoint.exists())
            self.assertEqual("protected", reasons.get(str(endpoint)))
        self.assertTrue((target / "source").exists())

    def test_partial_removal_reports_failed_summary(self):
        target = self.root / "artifacts/ordinary"
        target.mkdir(parents=True)
        (target / "first").write_text("artifact")
        self.age(target)
        def partial(path):
            (path / "first").unlink()
            raise FileNotFoundError("a later child vanished")
        with patch.object(cleanup, "remove_tree", side_effect=partial):
            result = self.clean(target)
        self.assertEqual("failed", result["action"], result)
        self.assertEqual("vanished", result["reason"], result)
        (target / "first").write_text("artifact")
        self.age(target)
        with patch.object(cleanup, "remove_tree", side_effect=partial):
            rows = self.run_sweep(expected_exit=1)
        self.assertEqual("failed", rows[-1]["status"], rows)

    def test_retained_or_recent_repository_reclaims_only_old_build(self):
        for kind in ("dirty", "recent"):
            target = self.clone(kind)
            build = target / ".lake/build"
            build.mkdir(parents=True)
            (build / "generated").write_text("cache")
            packages = target / ".lake/packages"
            packages.mkdir()
            (packages / "dependency").write_text("keep")
            self.age(target)
            if kind == "dirty":
                (target / "source").write_text("private")
                self.age(target)
            else:
                os.utime(target / "source", (self.now, self.now))
            self.run_sweep()
            self.assertFalse(build.exists())
            self.assertTrue(packages.exists())
            self.assertTrue((target / ".git").exists())

    def test_build_cache_lock_and_registered_tree_protection(self):
        target = self.clone()
        build = target / ".lake/build"
        build.mkdir(parents=True)
        (build / "generated").write_text("cache")
        self.age(target)
        with release.cache_guard(target):
            self.run_sweep()
        self.assertTrue(build.exists())
        self.run_sweep([target])
        self.assertTrue(build.exists())

    def test_fifo_and_socket_require_observable_inactivity(self):
        for kind in ("fifo", "socket"):
            target = self.root / kind
            if kind == "fifo":
                os.mkfifo(target)
            else:
                handle = socket.socket(socket.AF_UNIX)
                handle.bind(str(target))
                handle.close()
            self.age(target.parent)
            for platform, active, action, reason in (("linux", False, "kept", "ipc_activity_unobservable"),
                    ("darwin", True, "kept", "protected"), ("darwin", False, "removed", None)):
                with self.subTest(kind=kind, platform=platform, active=active), \
                     patch.object(cleanup.sys, "platform", platform), \
                     patch.object(cleanup.subprocess, "run", return_value=subprocess.CompletedProcess(
                         [], 0 if active else 1, "n" + str(target) + "\n" if active else "", "")):
                    result = cleanup.clean_candidate(target, self.cutoff, [], delete=True)
                self.assertEqual((action, reason), (result["action"], result["reason"]), result)

    def test_staging_inventory_shape_age_lock_and_backup_exclusion(self):
        lake = self.main / ".lake"
        stage = lake / ".release-token/build"
        stage.mkdir(parents=True)
        (stage / "generated").write_text("cache")
        backup = lake / ".release-backup-token"
        backup.mkdir()
        malformed = lake / ".release-invalid"
        malformed.mkdir()
        (malformed / "source").write_text("keep")
        (lake / ".release-file").write_text("keep")
        self.age(lake)
        with release.cache_guard(self.main):
            rows = release.clean_staging(lake, self.cutoff, now=self.now, delete=True)
        self.assertTrue(stage.exists())
        self.assertTrue(any(row["reason"] == "cache_busy" for row in rows))
        rows = release.clean_staging(lake, self.cutoff, now=self.now, delete=True)
        self.assertFalse(stage.parent.exists())
        self.assertTrue(backup.exists())
        self.assertTrue(malformed.exists())
        self.assertTrue((lake / ".release-file").exists())
        recent = lake / ".release-recent"
        recent.mkdir()
        os.utime(recent, (self.now, self.now))
        release.clean_staging(lake, self.cutoff, now=self.now, delete=True)
        self.assertTrue(recent.exists())

    def test_staging_age_uses_caller_time_despite_wall_clock_changes(self):
        lake = self.main / ".lake"
        old = lake / ".release-old"
        recent = lake / ".release-recent"
        old.mkdir(parents=True)
        recent.mkdir()
        self.age(lake)
        os.utime(recent, (self.cutoff + 1, self.cutoff + 1))
        with patch.object(release.time, "time", side_effect=AssertionError("unexpected wall clock read")):
            try:
                rows = release.clean_staging(lake, now=self.now)
            except TypeError as error:
                self.fail("staging cleanup must accept caller time: " + str(error))
        items = {row["path"]: row for row in rows}
        self.assertEqual("removed", items[str(old)]["action"])
        self.assertEqual("recent", items[str(recent)]["reason"])
        self.assertFalse(old.exists())
        self.assertTrue(recent.exists())

    def test_staging_nested_git_and_changed_snapshot_are_retained(self):
        lake = self.main / ".lake"
        stage = lake / ".release-token/build"
        (stage / ".git").mkdir(parents=True)
        (stage / ".git/HEAD").write_text("recovery history")
        self.age(lake)
        rows = release.clean_staging(lake, self.cutoff, now=self.now)
        self.assertTrue(stage.exists())
        self.assertEqual("repository", rows[0]["reason"])
        shutil.rmtree(stage / ".git")
        self.age(lake)
        observe = release.staging_snapshot
        calls = 0
        def changed(*args):
            nonlocal calls
            calls += 1
            if calls == 2:
                (stage / "new").write_text("concurrent")
            return observe(*args)
        with patch.object(release, "staging_snapshot", side_effect=changed):
            rows = release.clean_staging(lake, self.cutoff, now=self.now)
        self.assertEqual("changed", rows[0]["reason"])
        self.assertTrue(stage.exists())

    def test_staging_parent_flags_are_preserved(self):
        lake = self.main / ".lake"
        stage = lake / ".release-token"
        stage.mkdir(parents=True)
        self.age(lake)
        lstat = Path.lstat
        def flagged(path):
            info = lstat(path)
            if path != lake:
                return info
            fields = {name: getattr(info, name) for name in dir(info) if name.startswith("st_")}
            return types.SimpleNamespace(**dict(fields, st_flags=stat.UF_IMMUTABLE))
        with patch.object(Path, "lstat", flagged):
            rows = release.clean_staging(lake, self.cutoff, now=self.now, delete=False)
        self.assertEqual("protected_flag", rows[0]["reason"], rows)

    def test_vanished_staging_entry_does_not_abort_other_cleanup(self):
        lake = self.main / ".lake"
        vanished = lake / ".release-a"
        retained = lake / ".release-b"
        vanished.mkdir(parents=True)
        retained.mkdir()
        self.age(lake)
        lstat = Path.lstat
        def disappear(path):
            if path == vanished:
                raise FileNotFoundError(str(path))
            return lstat(path)
        with patch.object(Path, "lstat", disappear):
            rows = release.clean_staging(lake, self.cutoff, now=self.now)
        self.assertTrue(any(row["reason"] == "vanished" for row in rows), rows)
        self.assertFalse(retained.exists())

    def test_repository_ipc_and_staging_keep_a_full_day_minimum(self):
        target = self.clone()
        recent = self.now - 3600
        self.age(target)
        os.utime(target / "source", (recent, recent))
        result = cleanup.clean_candidate(target, self.now, [], delete=True, repository=self.main)
        self.assertEqual("recent", result["reason"])
        fifo = self.root / "fifo"
        os.mkfifo(fifo)
        os.utime(fifo, (recent, recent))
        with patch.object(cleanup.sys, "platform", "darwin"), \
             patch.object(cleanup.subprocess, "run", return_value=subprocess.CompletedProcess([], 1, "", "")):
            result = cleanup.clean_candidate(fifo, self.now, [], True)
        self.assertEqual("recent", result["reason"])

    def test_codex_repository_and_special_file_rules_remain_unchanged(self):
        codex = self.root / "codex"
        skeleton = codex / "tmp/skeleton"
        (skeleton / ".git").mkdir(parents=True)
        fifo = codex / "tmp/fifo"
        os.mkfifo(fifo)
        self.age(codex)
        rows = self.run_sweep()
        reasons = {row.get("path"): row.get("reason") for row in rows}
        self.assertEqual("repository", reasons.get(str(skeleton)))
        self.assertEqual("special_file", reasons.get(str(fifo)))
        self.assertTrue(skeleton.exists())
        self.assertTrue(fifo.exists())

    def test_ipc_observation_failure_recent_and_activity_are_fail_closed(self):
        endpoint = self.root / "endpoint"
        os.mkfifo(endpoint)
        self.age(self.root)
        with patch.object(cleanup.sys, "platform", "darwin"):
            for observed in (subprocess.CompletedProcess([], 1, "", "cannot inspect"),
                             subprocess.CompletedProcess([], 0, "", "")):
                with patch.object(cleanup.subprocess, "run", return_value=observed):
                    self.assertEqual("ipc_activity_unobservable",
                                     cleanup.clean_candidate(endpoint, self.cutoff, [], True)["reason"])
            with patch.object(cleanup.subprocess, "run", return_value=subprocess.CompletedProcess([], 1, "", "")):
                self.assertEqual("protected", cleanup.clean_candidate(endpoint, self.cutoff, [endpoint], True)["reason"])
                os.utime(endpoint, (self.now, self.now))
                self.assertEqual("recent", cleanup.clean_candidate(endpoint, self.cutoff, [], True)["reason"])

    def test_ipc_batch_reobserves_activity_and_fingerprints_before_unlink(self):
        paths = [self.root / ("fifo-" + str(index)) for index in range(4)]
        for path in paths:
            os.mkfifo(path)
        self.age(self.root)
        calls = 0
        def activity():
            nonlocal calls
            calls += 1
            if calls == 2:
                os.utime(paths[2], (self.now, self.now))
            return {paths[0]} if calls == 1 else {paths[0], paths[1]}
        with patch.object(cleanup.sys, "platform", "darwin"), \
             patch.object(cleanup.subprocess, "run", side_effect=AssertionError("activity is already observed")):
            rows = list(cleanup.clean_ipc_batch(paths, self.cutoff, [], True, activity))
        self.assertEqual(["protected", "changed", "changed", None], [row["reason"] for row in rows])
        self.assertEqual([True, True, True, False], [path.exists() for path in paths])

    def test_ipc_batch_timeout_retains_and_names_every_endpoint(self):
        paths = [self.root / ("fifo-" + str(index)) for index in range(2)]
        for path in paths:
            os.mkfifo(path)
        self.age(self.root)
        def activity():
            raise subprocess.TimeoutExpired(["lsof"], 120)
        try:
            rows = list(cleanup.clean_ipc_batch(paths, self.cutoff, [], True, activity))
        except subprocess.TimeoutExpired as error:
            self.fail("IPC batch must retain endpoints after observer timeout: " + str(error))
        self.assertEqual([str(path) for path in paths], [row["path"] for row in rows])
        self.assertEqual(["ipc_activity_unobservable"] * 2, [row["reason"] for row in rows])
        self.assertTrue(all(path.exists() for path in paths))

    def test_ipc_batch_recheck_timeout_retains_remaining_endpoints(self):
        paths = [self.root / ("fifo-" + str(index)) for index in range(2)]
        for path in paths:
            os.mkfifo(path)
        self.age(self.root)
        calls = 0
        def activity():
            nonlocal calls
            calls += 1
            if calls > 1:
                raise subprocess.TimeoutExpired(["lsof"], 120)
            return set()
        try:
            rows = list(cleanup.clean_ipc_batch(paths, self.cutoff, [], True, activity))
        except subprocess.TimeoutExpired as error:
            self.fail("IPC recheck must retain endpoints after observer timeout: " + str(error))
        self.assertEqual(["ipc_activity_unobservable"] * 2, [row["reason"] for row in rows])
        self.assertTrue(all(path.exists() for path in paths))

    def test_host_sweep_ipc_timeout_retains_each_endpoint_and_continues(self):
        artifacts = self.root / "artifacts"
        artifacts.mkdir()
        endpoints = [artifacts / ("fifo-" + str(index)) for index in range(2)]
        for endpoint in endpoints:
            os.mkfifo(endpoint)
        ordinary = artifacts / "ordinary"
        ordinary.write_text("old artifact")
        self.age(artifacts)
        def observe(*args, **kwargs):
            if kwargs.get("strict_ipc"):
                raise subprocess.TimeoutExpired(["lsof"], 120)
            return set()
        with patch.object(cleanup.sys, "platform", "darwin"), \
             patch.object(cleanup, "active_paths", side_effect=observe):
            rows = self.run_sweep(active=None)
        items = {row.get("path"): row for row in rows}
        for endpoint in endpoints:
            self.assertEqual("ipc_activity_unobservable", items[str(endpoint)]["reason"])
            self.assertTrue(endpoint.exists())
        self.assertFalse(ordinary.exists())
        self.assertEqual("succeeded", rows[-1]["status"])

    def test_relative_named_socket_observation_cannot_certify_inactivity(self):
        endpoint = self.root / "endpoint"
        self.make_endpoint(endpoint, "socket")
        self.age(self.root)
        with patch.object(cleanup.sys, "platform", "darwin"), \
             patch.object(cleanup.subprocess, "run", return_value=subprocess.CompletedProcess(
                 [], 0, "p123\nf4\ntunix\nnendpoint\n", "")):
            result = cleanup.clean_candidate(endpoint, self.cutoff, [], True)
        self.assertEqual("ipc_activity_unobservable", result["reason"], result)
        self.assertTrue(endpoint.exists())

    def test_nonipc_lsof_observation_preserves_warning_handling(self):
        endpoint = self.root / "observed"
        observed = subprocess.CompletedProcess([], 0, "p123\nf4\ntREG\nn" + str(endpoint) + "\n", "warning")
        with patch.object(cleanup.subprocess, "run", return_value=observed):
            try:
                paths = cleanup.macos_active_paths()
            except OSError as error:
                self.fail("ordinary activity observations retain their warning policy: " + str(error))
        self.assertIn(endpoint, paths)
        with patch.object(cleanup.subprocess, "run", return_value=observed):
            with self.assertRaisesRegex(OSError, "ipc_activity_unobservable"):
                cleanup.macos_active_paths(strict_ipc=True)

    def test_escaped_absolute_socket_observation_retains_endpoint(self):
        endpoint = self.root / "endpoint\\name"
        self.make_endpoint(endpoint, "socket")
        self.age(self.root)
        escaped = str(endpoint).replace("\\", "\\\\")
        with patch.object(cleanup.sys, "platform", "darwin"), \
             patch.object(cleanup.subprocess, "run", return_value=subprocess.CompletedProcess(
                 [], 0, "p123\nf4\ntunix\nn" + escaped + "\n", "")):
            result = cleanup.clean_candidate(endpoint, self.cutoff, [], True)
        self.assertIn(result["reason"], ("protected", "ipc_activity_unobservable"), result)
        self.assertTrue(endpoint.exists())

    def test_unnamed_sockets_do_not_block_idle_ipc_reclamation(self):
        endpoint = self.root / "endpoint"
        os.mkfifo(endpoint)
        self.age(self.root)
        rows = "p123\nf4\ntunix\nn->0xabcdef\nf5\ntunix\nn\nf6\ntIPv4\nn127.0.0.1:8000\n"
        with patch.object(cleanup.sys, "platform", "darwin"), \
             patch.object(cleanup.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, rows, "")):
            result = cleanup.clean_candidate(endpoint, self.cutoff, [], True)
        self.assertEqual("removed", result["action"], result)

    @unittest.skipUnless(sys.platform == "darwin" and shutil.which("lsof"), "macOS lsof")
    def test_real_unnamed_sockets_do_not_block_idle_ipc_reclamation(self):
        endpoint = self.root / "endpoint"
        os.mkfifo(endpoint)
        self.age(self.root)
        first, second = socket.socketpair()
        try:
            with self.lsof_process(os.getpid()):
                result = cleanup.clean_candidate(endpoint, self.cutoff, [], True)
            self.assertEqual("removed", result["action"], result)
        finally:
            first.close()
            second.close()

    @unittest.skipUnless(sys.platform == "darwin" and shutil.which("lsof"), "macOS lsof")
    def test_real_relative_socket_survives_full_host_sweep(self):
        self.check_live_socket_sweep("endpoint", True)

    @unittest.skipUnless(sys.platform == "darwin" and shutil.which("lsof"), "macOS lsof")
    def test_real_escaped_socket_survives_full_host_sweep(self):
        self.check_live_socket_sweep("endpoint\\name", False)

    def check_live_socket_sweep(self, name, relative):
        workspace = tempfile.TemporaryDirectory(prefix="ipc with spaces ", dir="/tmp")
        self.addCleanup(workspace.cleanup)
        artifacts = Path(workspace.name).resolve()
        endpoint = artifacts / name
        program = '''import json, os, socket, sys
directory, name, relative = json.loads(sys.stdin.readline())
os.chdir(directory)
handle = socket.socket(socket.AF_UNIX)
handle.bind(name if relative else os.path.join(directory, name))
handle.listen()
os.chdir("/")
print("ready", flush=True)
sys.stdin.read()
'''
        child = subprocess.Popen([sys.executable, "-B", "-c", program],
                                 stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        try:
            child.stdin.write(json.dumps([str(artifacts), name, relative]) + "\n")
            child.stdin.flush()
            self.assertEqual("ready\n", child.stdout.readline())
            self.age(artifacts)
            with self.lsof_process(child.pid):
                rows = self.run_sweep(artifact_root=artifacts, active=None)
            self.assertEqual("succeeded", rows[-1]["status"], rows)
            self.assertTrue(endpoint.exists(), rows)
            with socket.socket(socket.AF_UNIX) as client:
                client.connect(str(endpoint))
        finally:
            child.communicate("", timeout=30)

    def test_later_ipc_endpoint_opened_after_an_unlink_is_retained(self):
        paths = [self.root / ("fifo-" + str(index)) for index in range(2)]
        for path in paths:
            os.mkfifo(path)
        self.age(self.root)
        handles = []
        self.addCleanup(lambda: [os.close(handle) for handle in handles])
        unlink = Path.unlink
        def opened_after_first(path, *args, **kwargs):
            unlink(path, *args, **kwargs)
            if path == paths[0]:
                handles.append(os.open(paths[1], os.O_RDONLY | os.O_NONBLOCK))
        with patch.object(cleanup.sys, "platform", "darwin"), patch.object(Path, "unlink", opened_after_first):
            rows = list(cleanup.clean_ipc_batch(paths, self.cutoff, [], True,
                                              lambda: {paths[1]} if handles else set()))
        self.assertEqual(["removed", "kept"], [row["action"] for row in rows])
        self.assertTrue(paths[1].exists())

    def test_nested_ipc_tree_shares_complete_lsof_observations(self):
        root = self.root / "nested ipc"
        root.mkdir()
        for index in range(8):
            os.mkfifo(root / ("fifo-" + str(index)))
        self.age(root)
        with patch.object(cleanup.sys, "platform", "darwin"), \
             patch.object(cleanup.subprocess, "run", return_value=subprocess.CompletedProcess([], 1, "", "")) as run:
            result = cleanup.clean_candidate(root, self.cutoff, [], True)
        self.assertEqual("removed", result["action"], result)
        self.assertLessEqual(run.call_count, 2)

    def test_registered_staging_is_a_narrow_cleanup_exception(self):
        target = self.clone()
        for root in (self.main, target):
            stage = root / ".lake/.release-token/build"
            stage.mkdir(parents=True)
            (stage / "generated").write_text("cache")
            self.age(root / ".lake")
        self.run_sweep([target])
        for root in (self.main, target):
            self.assertFalse((root / ".lake/.release-token").exists())
            self.assertTrue((root / "source").exists())

    def test_fetch_entry_uses_the_same_staging_cleanup(self):
        with patch.object(release, "clean_staging", return_value=[]) as clean, \
             patch.object(release, "release_key", return_value="key"), \
             patch.object(release, "snapshot_candidates", return_value=[]), \
             patch.object(release, "receipt"):
            with release.cache_guard(self.main):
                release.fetch_locked(self.main, "partition", 60)
        clean.assert_called_once()
        self.assertEqual(self.main / ".lake", clean.call_args.args[0])
        self.assertEqual(self.now, clean.call_args.kwargs["now"])

    def test_host_sweep_keeps_its_programs_after_source_worktree_disposal(self):
        copied = self.root / "copied/tools"
        scripts = copied / "scripts"
        scripts.mkdir(parents=True)
        shutil.copy(ROOT / "tools/scripts/host-cleanup.py", scripts / "host-cleanup.py")
        shutil.copytree(ROOT / "tools/scripts/worktree", scripts / "worktree")
        shutil.copytree(ROOT / "tools/scripts/report", scripts / "report")
        shutil.copytree(ROOT / "tools/lean-inspector", copied / "lean-inspector")
        stage = self.main / ".lake/.release-token/build"
        stage.mkdir(parents=True)
        self.age(self.main / ".lake")
        program = '''import importlib.util, pathlib, shutil, sys
spec = importlib.util.spec_from_file_location("cleanup", sys.argv[1])
cleanup = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cleanup)
main = pathlib.Path(sys.argv[2])
cleanup.registered_worktrees = lambda root: [main]
cleanup.active_paths = lambda *args, **kwargs: set()
def dispose(*args, **kwargs):
    shutil.rmtree(pathlib.Path(sys.argv[1]).parent)
    return 0
cleanup.clean_worktrees = dispose
options = cleanup.argparse.Namespace(repository=main, base="dev", codex_home=main/"codex",
    sshx_home=main/"sshx", tmp_root=[main/"artifacts"], min_age_hours=24, delete=True, verbose=True)
raise SystemExit(cleanup.run_clean(options))
'''
        result = subprocess.run([sys.executable, "-B", "-c", program, str(scripts / "host-cleanup.py"), str(self.main)],
                                capture_output=True, text=True)
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertFalse(stage.parent.exists())

    def test_fetch_reports_staging_removal_failures(self):
        failure = dict(path=str(self.main / ".lake/.release-token"), action="failed",
                       reason="unreadable", detail="removal failed", apparent_bytes=0)
        for entry in ("production", "verification"):
            output = io.StringIO()
            with patch.object(release, "clean_staging", return_value=[failure]), \
                 patch.object(release, "release_key", return_value="key"), \
                 patch.object(release, "prefix", return_value="verification-"), \
                 patch.object(release, "snapshot_candidates", return_value=[]), \
                 patch.object(release, "restore_snapshot"), contextlib.redirect_stdout(output):
                if entry == "production":
                    with release.cache_guard(self.main):
                        release.fetch_locked(self.main, "partition", 60)
                else:
                    release.fetch_verification(self.main, "partition", {"workflow_run_id": "1", "workflow_run_attempt": "1"})
            rows = [json.loads(line.split(" ", 1)[1]) for line in output.getvalue().splitlines()]
            self.assertTrue(any(failure in row.get("items", []) for row in rows), rows)

    def test_vanished_preselection_does_not_abort_the_artifact_sweep(self):
        missing = self.root / "artifacts/missing"
        old = self.root / "artifacts/old"
        old.parent.mkdir()
        old.write_text("artifact")
        self.age(old.parent)
        with patch.object(cleanup, "candidates", return_value=iter([("tmp", missing), ("tmp", old)])):
            rows = self.run_sweep()
        self.assertFalse(old.exists())
        self.assertTrue(any(row.get("reason") == "vanished" for row in rows))


if __name__ == "__main__":
    if sys.argv[1:] == ["--list-tests"]:
        print(json.dumps(["HostReclaimTests." + name
                          for name in unittest.defaultTestLoader.getTestCaseNames(HostReclaimTests)]))
    else:
        unittest.main()
