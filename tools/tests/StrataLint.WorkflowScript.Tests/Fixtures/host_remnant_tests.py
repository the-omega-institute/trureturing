"""Sibling remnant eligibility, activity and cleanup-entry contracts."""

import contextlib
import errno
import io
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import types
import unittest
from unittest.mock import patch

import host_reclaim_tests as fixtures

cleanup, ROOT = fixtures.cleanup, fixtures.ROOT
fixture_active_paths = fixtures.fixture_active_paths


class HostRemnantTests(unittest.TestCase):
    setUp = fixtures.HostReclaimTests.setUp
    git = fixtures.HostReclaimTests.git
    age = fixtures.HostReclaimTests.age
    remnant = fixtures.HostReclaimTests.remnant
    clean_remnant = fixtures.HostReclaimTests.clean_remnant
    run_sweep = fixtures.HostReclaimTests.run_sweep

    def test_remnant_shape_and_unique_bytes_are_retained(self):
        for name, relative, content, reason in (
                ("source", "D5/Unique.lean", b"unique", "unknown_top_level"),
                ("unknown", "notes", b"unique", "unknown_top_level"),
                ("lake", ".lake/packages/source", b"unique", "lake_content"),
                ("unique", "Blueprint/Unique.md", b"unique", "blueprint_unrecoverable")):
            with self.subTest(name=name):
                target = self.remnant(name, blueprint=False)
                path = target / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(content)
                self.age(target)
                result = self.clean_remnant(target)
                self.assertEqual(("kept", reason), (result["action"], result["reason"]), result)
                self.assertEqual(content, path.read_bytes())

    def test_remnant_git_boundaries_are_retained(self):
        for name, boundary in (("clone", ".git/HEAD"), ("foreign", ".git"),
                               ("nested", ".lake/build/nested/.git"),
                               ("bare", ".lake/build/bare/HEAD")):
            with self.subTest(name=name):
                target = self.remnant(name, blueprint=False)
                marker = target / boundary
                marker.parent.mkdir(parents=True, exist_ok=True)
                marker.write_text("gitdir: elsewhere" if name == "foreign" else "ref: refs/heads/dev")
                if name == "bare":
                    for entry in ("objects", "refs"):
                        (marker.parent / entry).mkdir()
                self.age(target)
                result = self.clean_remnant(target)
                self.assertEqual(("kept", "repository"), (result["action"], result["reason"]), result)
                self.assertTrue(marker.exists())

    def test_remnant_registered_overlap_is_retained(self):
        target = self.remnant(blueprint=False)
        for registered in (target, target / ".lake/build", self.root):
            with self.subTest(registered=registered), \
                 patch.object(cleanup, "registered_worktrees", return_value=[self.main, registered]):
                result = self.clean_remnant(target)
                self.assertEqual(("kept", "protected"), (result["action"], result["reason"]))
        self.assertTrue(target.exists())

    def test_remnant_dangling_and_blob_only_refs_do_not_certify_bytes(self):
        target = self.remnant(blueprint=False)
        path = target / "Blueprint/Unique.md"
        path.parent.mkdir()
        path.write_text("only in a dangling commit")
        (self.main / "Blueprint").mkdir()
        shutil.copyfile(path, self.main / "Blueprint/Unique.md")
        baseline = self.git(self.main, "rev-parse", "HEAD")
        self.git(self.main, "add", "Blueprint")
        self.git(self.main, "commit", "-m", "Dangling blueprint")
        oid = self.git(self.main, "rev-parse", "HEAD:Blueprint/Unique.md")
        self.git(self.main, "reset", "--hard", baseline)
        self.git(self.main, "update-ref", "refs/tags/blob-only", oid)
        self.age(target)
        result = self.clean_remnant(target)
        self.assertEqual(("kept", "blueprint_unrecoverable"), (result["action"], result["reason"]), result)
        self.assertTrue(path.exists())

    def test_remnant_historical_ref_bytes_dry_run_and_delete(self):
        target = self.remnant()
        self.git(self.main, "branch", "retained-blueprint")
        self.git(self.main, "rm", "Blueprint/Retained.md")
        self.git(self.main, "commit", "-m", "Remove current blueprint")
        dry = self.clean_remnant(target, delete=False)
        self.assertEqual("would_remove", dry["action"], dry)
        self.assertTrue(target.exists())
        deleted = self.clean_remnant(target)
        self.assertEqual("removed", deleted["action"], deleted)
        self.assertFalse(target.exists())

    def test_remnant_missing_or_corrupt_recovery_blob_is_retained(self):
        import zlib
        for corruption in ("missing", "corrupt"):
            with self.subTest(corruption=corruption):
                target = self.remnant(corruption)
                oid = self.git(self.main, "rev-parse", "HEAD:Blueprint/Retained.md")
                blob = self.main / ".git/objects" / oid[:2] / oid[2:]
                original = blob.read_bytes()
                if corruption == "missing":
                    blob.unlink()
                else:
                    blob.write_bytes(zlib.compress(b"blob 25\0different retained bytes\n"))
                self.age(target)
                try:
                    result = self.clean_remnant(target)
                    self.assertEqual("kept", result["action"], result)
                    self.assertIn(result["reason"], ("recovery_unverifiable", "blueprint_unrecoverable"))
                    self.assertTrue(target.exists())
                finally:
                    blob.write_bytes(original)

    def linux_activity_sweep(self, unavailable=None):
        target = self.remnant(blueprint=False)
        owned, peer = (self.root / "proc" / name for name in ("123", "124"))
        for process in (owned, peer):
            (process / "fd").mkdir(parents=True)
            (process / "status").write_text("State: S (sleeping)\nThreads: 1\n")
            (process / "cwd").symlink_to(target / ".lake/build", target_is_directory=True)
            (process / "fd/0").symlink_to(target / ".lake/build/object")
        iterdir, readlink, run = Path.iterdir, os.readlink, subprocess.run
        observed = []
        denied = peer if unavailable == "peer" else owned if unavailable == "owned" else None
        def inventory(path):
            # Both processes reach production observation; no PID allowlist is applied.
            return iter([owned, peer]) if path == Path("/proc") else iterdir(path)
        def observe(path):
            observed.append(path)
            if denied is not None and path == denied / "cwd":
                raise PermissionError(errno.EACCES, "Permission denied", str(path))
            return readlink(path)
        def processes(arguments, **kwargs):
            if arguments[0] == "ps":
                self.assertEqual(["ps", "-axo", "uid=,args="], arguments)
                return subprocess.CompletedProcess(arguments, 0, "", "")
            return run(arguments, **kwargs)
        with patch.object(cleanup.sys, "platform", "linux"), \
             patch.object(Path, "iterdir", inventory), \
             patch.object(os, "readlink", observe), \
             patch.object(cleanup.subprocess, "run", side_effect=processes):
            rows = self.run_sweep(active=None, expected_exit=1 if denied else 0)
        self.assertIn(owned / "cwd", observed)
        if unavailable != "owned":
            self.assertIn(owned / "fd/0", observed)
            self.assertIn(peer / "cwd", observed)
        if denied is not None:
            summary = rows[-1]
            self.assertEqual(("failed", "not_started"), (summary["status"], summary["artifact_sweep"]))
            self.assertIn("linux_activity_unavailable", summary["inventory_error"])
            self.assertIn(str(denied), summary["inventory_error"])
            self.assertIn('"boundary": "cwd"', summary["inventory_error"])
        else:
            self.assertIn(peer / "fd/0", observed)
            item = next(row for row in rows if row.get("path") == str(target))
            self.assertEqual(("kept", "protected"), (item["action"], item["reason"]), item)
        self.assertEqual(b"regenerable", (target / ".lake/build/object").read_bytes())

    def test_linux_observer_fails_closed_for_unreadable_same_uid_peer(self):
        self.linux_activity_sweep("peer")

    def test_linux_observer_fails_closed_for_unreadable_owned_process(self):
        self.linux_activity_sweep("owned")

    def test_linux_observer_observes_both_readable_same_uid_processes(self):
        self.linux_activity_sweep()

    def test_remnant_actual_cwd_and_open_file_are_retained(self):
        for handle in ("cwd", "open"):
            with self.subTest(handle=handle):
                target = self.remnant(handle, blueprint=False)
                program = ("import sys; " + ("f=open(sys.argv[1], 'rb'); " if handle == "open" else "") +
                           "print('ready', flush=True); sys.stdin.read()")
                process = subprocess.Popen([sys.executable, "-u", "-c", program,
                                            str(target / ".lake/build/object")],
                                           cwd=target / ".lake/build" if handle == "cwd" else self.root,
                                           stdin=subprocess.PIPE, stdout=subprocess.PIPE)
                try:
                    self.assertEqual(b"ready\n", process.stdout.readline())
                    active = fixture_active_paths(self.root / "codex", [process.pid], scopes=[target])
                    result = cleanup.clean_candidate(target, self.cutoff, active, delete=True,
                                                     repository=self.main, remnant=True)
                    self.assertEqual(("kept", "protected"), (result["action"], result["reason"]), result)
                    self.assertTrue(target.exists())
                finally:
                    process.communicate(timeout=10)

    def test_remnant_build_only_and_empty_directories_are_reclaimed(self):
        for name in ("build", "empty"):
            target = self.remnant(name, blueprint=False)
            if name == "empty":
                shutil.rmtree(target / ".lake")
                self.age(target)
            result = self.clean_remnant(target)
            self.assertEqual("removed", result["action"], result)
            self.assertFalse(target.exists())

    def test_remnant_main_identity_failure_has_named_closed_result(self):
        target = self.remnant(blueprint=False)
        preservation, _ = cleanup.worktree_modules()
        git = preservation.git
        def unverifiable(root, *args, **kwargs):
            if args == ("rev-parse", "--show-toplevel"):
                raise RuntimeError("main identity unavailable")
            return git(root, *args, **kwargs)
        with patch.object(preservation, "git", side_effect=unverifiable):
            with self.assertRaisesRegex(OSError, "main_checkout_unverifiable"):
                list(cleanup.remnant_candidates(self.main, [self.main]))
        self.assertTrue(target.exists())

    def test_remnant_symlinks_special_files_recent_and_activity_are_retained(self):
        for name in ("root-link", "internal-link", "fifo", "recent", "activity"):
            with self.subTest(name=name):
                target = self.remnant(name, blueprint=False)
                if name == "root-link":
                    link = target.with_name(target.name + "-alias")
                    link.symlink_to(target, target_is_directory=True)
                    target = link
                elif name == "internal-link":
                    (target / ".lake/build/link").symlink_to(self.main)
                elif name == "fifo":
                    os.mkfifo(target / ".lake/build/pipe")
                self.age(target) if name != "root-link" else None
                if name == "recent":
                    os.utime(target / ".lake/build/object", (self.cutoff + 1, self.cutoff + 1))
                protected = [target / ".lake/build"] if name == "activity" else []
                result = cleanup.clean_candidate(target, self.cutoff, protected, delete=True,
                                                 repository=self.main, remnant=True)
                reason = {"root-link": "symlink", "internal-link": "symlink", "fifo": "special_file",
                          "recent": "recent", "activity": "protected"}[name]
                self.assertEqual(("kept", reason), (result["action"], result["reason"]), result)
                self.assertTrue(target.exists())

    def test_remnant_owner_mount_flags_and_readability_guards(self):
        target = self.remnant(blueprint=False)
        probe = target / ".lake/build/object"
        lstat, scandir = Path.lstat, os.scandir
        for guard, reason in (("owner", "not_owned"), ("mount", "mount"),
                              ("flags", "protected_flag"), ("read", "unreadable")):
            def altered(path):
                info = lstat(path)
                if path != probe:
                    return info
                fields = {name: getattr(info, name) for name in dir(info) if name.startswith("st_")}
                changes = {"owner": dict(st_uid=os.getuid() + 1), "mount": dict(st_dev=info.st_dev + 1),
                           "flags": dict(st_flags=stat.UF_IMMUTABLE), "read": {}}[guard]
                return types.SimpleNamespace(**dict(fields, **changes))
            def unreadable(path):
                if guard == "read" and Path(path) == probe.parent:
                    raise PermissionError("unreadable remnant")
                return scandir(path)
            with self.subTest(guard=guard), patch.object(Path, "lstat", altered), \
                 patch.object(os, "scandir", unreadable):
                result = self.clean_remnant(target)
            self.assertEqual(("kept", reason), (result["action"], result["reason"]), result)
            self.assertTrue(probe.exists())

    def test_remnant_rechecks_fingerprint_activity_registration_and_refs(self):
        for change in ("bytes", "activity", "registration", "refs"):
            with self.subTest(change=change):
                target = self.remnant(change)
                if change == "refs":
                    content = b"only the latest commit retains these bytes"
                    (self.main / "Blueprint/Retained.md").write_bytes(content)
                    self.git(self.main, "commit", "-am", "Retain distinct recovery bytes")
                    (target / "Blueprint/Retained.md").write_bytes(content)
                    self.age(target)
                registrations = cleanup.registered_worktrees
                def fresh():
                    if change == "bytes":
                        (target / "Blueprint/Retained.md").write_bytes(b"unique concurrent bytes")
                    if change == "registration":
                        registered.return_value = [self.main, target]
                        registered.side_effect = None
                    if change == "refs":
                        self.git(self.main, "reset", "--hard", "HEAD~1")
                    return {target / ".lake/build"} if change == "activity" else set()
                with patch.object(cleanup, "registered_worktrees", side_effect=registrations) as registered:
                    result = self.clean_remnant(target, activity=fresh)
                self.assertEqual(("kept", "changed"), (result["action"], result["reason"]), result)
                self.assertTrue(target.exists())

    def test_remnant_unrelated_ref_updates_do_not_block_recoverable_bytes(self):
        target = self.remnant()
        def fresh():
            self.git(self.main, "commit", "--allow-empty", "-m", "Unrelated retained work")
            return set()
        result = self.clean_remnant(target, activity=fresh)
        self.assertEqual("removed", result["action"], result)
        self.assertFalse(target.exists())

    def test_remnant_recovery_ref_disappearing_during_final_read_is_retained(self):
        target = self.remnant()
        run = subprocess.run
        reads = 0
        def raced(arguments, **kwargs):
            nonlocal reads
            result = run(arguments, **kwargs)
            if arguments[-2:] == ["cat-file", "--batch"]:
                reads += 1
                if reads == 2:
                    self.git(self.main, "reset", "--hard", "HEAD~1")
            return result
        with patch.object(cleanup.subprocess, "run", side_effect=raced):
            result = self.clean_remnant(target)
        self.assertEqual(2, reads)
        self.assertEqual("kept", result["action"], result)
        self.assertTrue(target.exists())

    def test_remnant_concurrent_save_during_final_recovery_read_is_retained(self):
        target = self.remnant()
        path = target / "Blueprint/Retained.md"
        unique = b"unique ordinary concurrent save\n"
        program = ("import pathlib, sys; print('ready', flush=True); "
                   "pathlib.Path(sys.stdin.readline().rstrip(\"\\n\")).write_bytes(" + repr(unique) + "); "
                   "print('saved', flush=True)")
        environment = dict(os.environ, CLEAN_TMP_ROOT=str(self.root / "tmp"),
                           CODEX_HOME=str(self.root / "codex"), SSHX_HOME=str(self.root / "sshx"))
        process = subprocess.Popen([sys.executable, "-u", "-c", program,
                                    str(path.relative_to(self.root))], cwd=self.root,
                                   stdin=subprocess.PIPE, stdout=subprocess.PIPE, env=environment)
        run = subprocess.run
        reads = 0
        def raced(arguments, **kwargs):
            nonlocal reads
            result = run(arguments, **kwargs)
            if arguments[-2:] == ["cat-file", "--batch"]:
                reads += 1
                if reads == 2:
                    isolated = next(target.parent.glob(target.name + "-cleanup-*"))
                    current = isolated / path.relative_to(target)
                    process.stdin.write(os.fsencode(str(current.relative_to(self.root))) + b"\n")
                    process.stdin.flush()
                    self.assertEqual(b"saved\n", process.stdout.readline())
                    self.assertGreater(current.stat().st_mtime, self.cutoff)
                    oid = run(["git", "-C", str(self.main), "hash-object", "--stdin"],
                              input=unique, capture_output=True, check=True).stdout.strip()
                    self.assertNotEqual(0, run(["git", "-C", str(self.main), "cat-file", "-e", oid],
                                              capture_output=True).returncode)
            return result
        def activity():
            observed = fixture_active_paths(self.root / "codex", [process.pid], scopes=[target])
            self.assertNotIn(target, cleanup.ProtectedPaths(observed))
            return observed
        try:
            self.assertEqual(b"ready\n", process.stdout.readline())
            with patch.dict(os.environ, environment), patch.object(cleanup.subprocess, "run", side_effect=raced):
                result = cleanup.clean_candidate(target, self.cutoff, activity(), delete=True,
                                                 repository=self.main, remnant=True, activity=activity)
            self.assertEqual(2, reads)
            self.assertEqual(("kept", "changed"), (result["action"], result["reason"]), result)
            self.assertEqual(unique, path.read_bytes())
        finally:
            process.communicate(timeout=10)

    def test_remnant_build_changes_during_final_recovery_read_are_retained(self):
        for change in ("content", "metadata"):
            with self.subTest(change=change):
                target = self.remnant(change)
                path = target / ".lake/build/object"
                run = subprocess.run
                reads = 0
                def raced(arguments, **kwargs):
                    nonlocal reads
                    result = run(arguments, **kwargs)
                    if arguments[-2:] == ["cat-file", "--batch"]:
                        reads += 1
                        if reads == 2:
                            isolated = next(target.parent.glob(target.name + "-cleanup-*"))
                            current = isolated / path.relative_to(target)
                            if change == "content":
                                current.write_bytes(b"ordinary concurrent build save")
                            else:
                                current.chmod(current.stat().st_mode ^ stat.S_IXUSR)
                    return result
                with patch.object(cleanup.subprocess, "run", side_effect=raced):
                    result = self.clean_remnant(target)
                self.assertEqual(2, reads)
                self.assertEqual(("kept", "changed"), (result["action"], result["reason"]), result)
                self.assertTrue(path.exists())

    def test_remnant_sweep_uses_main_inventory_and_reports_without_verbose(self):
        target = self.remnant()
        clone = self.root / (self.main.name + "-clone")
        self.git(self.main, "clone", "--no-hardlinks", self.main, clone)
        foreign = self.root / (self.main.name + "-foreign")
        self.git(clone, "worktree", "add", "-b", "foreign", foreign)
        registered = self.root / (self.main.name + "-registered")
        self.git(self.main, "worktree", "add", "-b", "registered", registered)
        source = self.root / (self.main.name + "-source")
        (source / "D5").mkdir(parents=True)
        (source / "D5/Only.lean").write_text("unique source")
        for path in (clone, foreign, registered, source):
            self.age(path)
        excluded = self.root / "unrelated-old"
        excluded.mkdir()
        nested = self.root / "container" / (self.main.name + "-nested")
        nested.mkdir(parents=True)
        self.age(excluded)
        self.age(nested.parent)
        lane = self.root / "arbitrary linked name"
        self.git(self.main, "worktree", "add", "-b", "linked", lane)
        options = cleanup.argparse.Namespace(repository=lane, base="dev", codex_home=self.root / "codex",
            sshx_home=self.root / "sshx", tmp_root=[self.root / "tmp"], min_age_hours=24,
            delete=False, verbose=False)
        for delete in (False, True):
            options.delete = delete
            output = io.StringIO()
            with patch.object(cleanup, "clean_worktrees", return_value=0), \
                 patch.object(cleanup, "active_paths", return_value=set()), contextlib.redirect_stdout(output):
                self.assertEqual(0, cleanup.run_clean(options), output.getvalue())
            rows = [json.loads(line) for line in output.getvalue().splitlines()]
            item = next(row for row in rows if row.get("path") == str(target))
            self.assertEqual("worktree_remnant", item["category"])
            self.assertEqual("removed" if delete else "would_remove", item["action"])
            self.assertEqual(1, rows[-1]["counts"]["worktree_remnant:" + item["action"]])
            self.assertTrue(excluded.exists())
            self.assertTrue(nested.exists())
            scanned = {row["path"] for row in rows if row.get("category") == "worktree_remnant"}
            self.assertNotIn(str(excluded), scanned)
            self.assertNotIn(str(nested), scanned)
            self.assertTrue(lane.exists())
            actions = {row["path"]: (row["action"], row["reason"]) for row in rows if "path" in row}
            for path, reason in ((clone, "repository"), (foreign, "repository"),
                                 (registered, "protected"), (source, "unknown_top_level")):
                self.assertEqual(("kept", reason), actions[str(path)], rows)
                self.assertTrue(path.exists())

    def test_remnant_make_dispatch_and_disposition_from_linked_worktree_with_spaces(self):
        """Cover make dispatch and disposition; production activity has separate integration cases."""
        target = self.remnant()
        scripts = self.main / "tools/scripts"
        scripts.mkdir(parents=True)
        shutil.copyfile(ROOT / "tools/Makefile", self.main / "tools/Makefile")
        source = (ROOT / "tools/scripts/host-cleanup.py").read_text()
        entry = '\nif __name__ == "__main__":\n    sys.exit(main())\n'
        self.assertTrue(source.endswith(entry))
        # This copied entry isolates dispatch from unrelated host processes.
        (scripts / "host-cleanup.py").write_text(source[:-len(entry)] + '''
if __name__ == "__main__":
    from unittest.mock import patch
    with patch("__main__.active_paths", return_value=set()):
        sys.exit(main())
''')
        shutil.copytree(ROOT / "tools/scripts/worktree", scripts / "worktree",
                        ignore=shutil.ignore_patterns("__pycache__"))
        shutil.copytree(ROOT / "tools/scripts/report", scripts / "report",
                        ignore=shutil.ignore_patterns("__pycache__"))
        shutil.copytree(ROOT / "tools/lean-inspector", self.main / "tools/lean-inspector",
                        ignore=shutil.ignore_patterns("__pycache__"))
        (scripts / "clean-lanes.sh").write_text("#!/bin/bash\nexit 0\n")
        self.git(self.main, "add", "tools")
        self.git(self.main, "commit", "-m", "Retain production entry")
        lane = self.root / "arbitrary linked with spaces"
        self.git(self.main, "worktree", "add", "-b", "entry", lane)
        environment = dict(os.environ, TMPDIR=str(self.root / "tmp"))
        (self.root / "tmp").mkdir()
        arguments = ["make", "--no-print-directory", "-C", str(lane / "tools"), "clean-all", "BASE=dev",
                     "CLEAN_CODEX_HOME=" + str(self.root / "codex"),
                     "CLEAN_SSHX_HOME=" + str(self.root / "sshx"),
                     "CLEAN_TMP_ROOT=" + str(self.root / "tmp"), "CLEAN_MIN_AGE_HOURS=24"]
        for delete in (False, True):
            result = subprocess.run([*arguments, "FORCE=" + str(int(delete))], cwd=self.root,
                                    env=environment, capture_output=True, text=True, timeout=60)
            self.assertEqual(0, result.returncode, result.stdout + result.stderr)
            rows = [json.loads(line) for line in result.stdout.splitlines()]
            item = next(row for row in rows if row.get("path") == str(target))
            self.assertEqual("removed" if delete else "would_remove", item["action"], rows)
            self.assertEqual(not delete, target.exists())

    def test_remnant_main_checkout_name_preserves_trailing_spaces(self):
        renamed = self.main.with_name("main with trailing space ")
        self.main.rename(renamed)
        self.main = renamed
        target = self.remnant(blueprint=False)
        rows = self.run_sweep(artifact_root=self.root / "tmp")
        self.assertIn((str(target), "removed"),
                      {(row.get("path"), row.get("action")) for row in rows})
        self.assertFalse(target.exists())


if __name__ == "__main__":
    if sys.argv[1:] == ["--list-tests"]:
        print(json.dumps(["HostRemnantTests." + name
                          for name in unittest.defaultTestLoader.getTestCaseNames(HostRemnantTests)]))
    else:
        unittest.main()
