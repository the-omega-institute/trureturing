"""Git, filesystem and cache-guard contracts for host artifact reclamation."""

import contextlib
import errno
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


def fixture_active_paths(codex, pids, scopes=()):
    """Use the production observer on fixture-owned processes only."""
    pids = {str(pid) for pid in pids}
    selection = ",".join(sorted(pids))
    iterdir, run = Path.iterdir, subprocess.run
    def inventory(path):
        entries = iterdir(path)
        return (entry for entry in entries if entry.name in pids) if path == Path("/proc") else entries
    def observe(arguments, **kwargs):
        if arguments[0] == "ps":
            arguments = ["ps", "-p", selection, "-o", arguments[-1]]
        elif arguments[0] == "lsof":
            arguments = [*arguments, "-p", selection]
        return run(arguments, **kwargs)
    with patch.object(Path, "iterdir", inventory), \
         patch.object(cleanup.subprocess, "run", side_effect=observe):
        return cleanup.active_paths(codex, scopes=scopes)


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

    def remnant(self, name="old", blueprint=True):
        target = self.root / (self.main.name + "-" + name)
        (target / ".lake/build").mkdir(parents=True)
        (target / ".lake/build/object").write_bytes(b"regenerable")
        if blueprint:
            source = self.main / "Blueprint/Retained.md"
            source.parent.mkdir(exist_ok=True)
            source.write_bytes(b"retained blueprint\x00bytes\n")
            self.git(self.main, "add", "Blueprint")
            self.git(self.main, "commit", "--allow-empty", "-m", "Retain blueprint")
            (target / "Blueprint").mkdir()
            shutil.copyfile(source, target / "Blueprint/Retained.md")
        self.age(target)
        return target

    def clean_remnant(self, target, delete=True, **kwargs):
        return cleanup.clean_candidate(target, self.cutoff, [], delete=delete,
                                       repository=self.main, remnant=True, **kwargs)

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

    def test_fixture_activity_isolates_peers_and_fails_closed_for_owned_process(self):
        target = self.remnant(blueprint=False)
        owned, peer = (self.root / "proc" / name for name in ("123", "124"))
        for process in (owned, peer):
            (process / "fd").mkdir(parents=True)
            (process / "status").write_text("State: S (sleeping)\nThreads: 1\n")
        (owned / "cwd").symlink_to(target / ".lake/build", target_is_directory=True)
        (owned / "fd/0").symlink_to(target / ".lake/build/object")
        iterdir, readlink = Path.iterdir, os.readlink
        def inventory(path):
            return iter([peer, owned]) if path == Path("/proc") else iterdir(path)
        def observe(arguments, **kwargs):
            self.assertEqual(["ps", "-p", owned.name, "-o", "uid=,pid=,args="], arguments)
            return subprocess.CompletedProcess(arguments, 0, "", "")
        for unavailable in (peer, owned):
            with self.subTest(unavailable=unavailable.name):
                def denied(path):
                    if path == unavailable / "cwd":
                        raise PermissionError(errno.EACCES, "Permission denied", str(path))
                    return readlink(path)
                with patch.object(cleanup.sys, "platform", "linux"), \
                     patch.object(Path, "iterdir", inventory), \
                     patch.object(os, "readlink", denied), \
                     patch.object(cleanup.subprocess, "run", side_effect=observe):
                    def activity():
                        return fixture_active_paths(self.root / "codex", [int(owned.name)], scopes=[target])
                    if unavailable == peer:
                        active = activity()
                        self.assertIn((target / ".lake/build").resolve(), active)
                        self.assertIn((target / ".lake/build/object").resolve(), active)
                        result = cleanup.clean_candidate(target, self.cutoff, active, delete=True,
                                                         repository=self.main, remnant=True, activity=activity)
                        self.assertEqual(("kept", "protected"), (result["action"], result["reason"]), result)
                    else:
                        result = self.clean_remnant(target, activity=activity)
                        self.assertEqual("failed", result["action"], result)
                        self.assertIn("linux_activity_unavailable", result["reason"])
                        self.assertIn('"boundary": "cwd"', result["reason"])
                self.assertEqual(b"regenerable", (target / ".lake/build/object").read_bytes())

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
            self.assertTrue(lane.exists())
            actions = {row["path"]: (row["action"], row["reason"]) for row in rows if "path" in row}
            for path, reason in ((clone, "repository"), (foreign, "repository"),
                                 (registered, "protected"), (source, "unknown_top_level")):
                self.assertEqual(("kept", reason), actions[str(path)], rows)
                self.assertTrue(path.exists())

    def test_remnant_make_entry_from_linked_worktree_with_spaces(self):
        target = self.remnant()
        scripts = self.main / "tools/scripts"
        scripts.mkdir(parents=True)
        shutil.copyfile(ROOT / "tools/Makefile", self.main / "tools/Makefile")
        source = (ROOT / "tools/scripts/host-cleanup.py").read_text()
        entry = '\nif __name__ == "__main__":\n    sys.exit(main())\n'
        self.assertTrue(source.endswith(entry))
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

    def test_case_inventory_lists_every_case_without_running_git(self):
        environment = dict(os.environ, PATH="")
        result = subprocess.run([sys.executable, "-B", __file__, str(ROOT), "--list-tests"],
                                capture_output=True, text=True, env=environment)
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        expected = ["HostReclaimTests." + name
                    for name in unittest.defaultTestLoader.getTestCaseNames(type(self))]
        self.assertEqual(expected, json.loads(result.stdout))
        self.assertEqual("", result.stderr)

    def test_old_git_directory_and_gitdir_file_are_ordinary_candidates(self):
        for marker in ("skeleton", "directory", "gitdir-file", "bare"):
            with self.subTest(marker=marker):
                if marker == "skeleton":
                    target = self.root / "artifacts/skeleton"
                    (target / ".git/objects/pack").mkdir(parents=True)
                    self.age(target)
                    self.assertEqual("removed", self.clean(target)["action"])
                    continue
                if marker == "bare":
                    target = self.root / "artifacts/bare"
                    self.git(self.main, "clone", "--bare", self.main, target)
                    self.age(target)
                    self.assertEqual("removed", self.clean(target)["action"])
                    continue
                target = self.clone(marker)
                (target / "source").write_text("temporary unique content")
                self.git(target, "commit", "-am", "Temporary commit")
                if marker == "gitdir-file":
                    metadata = self.root / "external.git"
                    (target / ".git").rename(metadata)
                    (target / ".git").write_text("gitdir: " + str(metadata) + "\n")
                self.age(target)
                result = self.clean(target)
                self.assertEqual("removed", result["action"], "[FAIL] old_repository_is_ordinary: " + str(result))
                self.assertFalse(target.exists())
                if marker == "gitdir-file":
                    self.assertTrue(metadata.exists())

    def test_repository_with_git_activity_inside_24_hours_is_retained(self):
        target = self.clone()
        self.age(target)
        os.utime(target / ".git/logs/HEAD", (self.cutoff + 1, self.cutoff + 1))
        result = self.clean(target)
        self.assertEqual(("kept", "recent"), (result["action"], result["reason"]))
        self.assertTrue(target.exists())

    def test_registered_worktree_is_retained_as_an_artifact(self):
        target = self.root / "artifacts/registered"
        self.git(self.main, "worktree", "add", "-b", "registered", target)
        self.age(target)
        result = self.clean(target)
        self.assertEqual(("kept", "protected"), (result["action"], result["reason"]))
        self.assertTrue((target / ".git").is_file())

    def test_staging_on_another_device_is_retained(self):
        lake = self.main / ".lake"
        stage = lake / ".release-token/build"
        stage.mkdir(parents=True)
        (stage / "generated").write_text("cache")
        self.age(lake)
        lstat = Path.lstat
        def mounted(path):
            info = lstat(path)
            if path != lake and lake not in path.parents:
                return info
            fields = {name: getattr(info, name) for name in dir(info) if name.startswith("st_")}
            return types.SimpleNamespace(**dict(fields, st_dev=info.st_dev + 1))
        with patch.object(Path, "lstat", mounted):
            rows = release.clean_staging(lake, now=self.now)
            self.assertEqual(("kept", "mount"), (rows[0]["action"], rows[0]["reason"]),
                             "[FAIL] cross_device_staging: " + str(rows))
        self.assertTrue(stage.exists())

    def test_nested_repositories_are_ordinary_candidates(self):
        parent = self.root / "parent"
        parent.mkdir()
        safe = self.clone("safe")
        safe.rename(parent / "safe")
        unsafe = self.clone("unsafe")
        (unsafe / "source").write_text("unique")
        self.git(unsafe, "commit", "-am", "Unique nested history")
        unsafe.rename(parent / "unsafe")
        self.age(parent)
        self.assertEqual("removed", self.clean(parent)["action"])
        self.assertFalse(parent.exists())

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

    def test_activity_changes_before_delete_are_retained(self):
        target = self.clone("activity")
        self.age(target)
        result = cleanup.clean_candidate(target, self.cutoff, [], delete=True,
                                         activity=lambda: {target / "source"}, refresh_activity=True)
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
              else patch.object(cleanup, "active_paths", return_value=set(active))) as activity, \
             patch.object(cleanup, "registered_worktrees", side_effect=lambda source:
                 [self.main, *trees] if source.resolve() == self.main else registrations(source)) as listed, \
             contextlib.redirect_stdout(output):
            self.assertEqual(expected_exit, cleanup.run_clean(options), output.getvalue())
        self.sweep_calls = (listed.call_count, activity.call_count)
        return [json.loads(line) for line in output.getvalue().splitlines()]

    def test_artifact_root_inside_cache_uses_guarded_owners(self):
        project = self.root / "artifacts/project"
        lake = project / ".lake"
        for name in (".release-token", ".release-backup-token", "packages"):
            (lake / name).mkdir(parents=True)
            (lake / name / "source").write_text("keep")
        self.age(project)
        with release.cache_guard(project):
            self.run_sweep(artifact_root=lake)
        self.assertEqual(3, len(list(lake.iterdir())))
        self.run_sweep(artifact_root=lake)
        self.assertTrue((lake / ".release-token/source").exists())
        self.assertTrue((lake / ".release-backup-token/source").exists())
        self.assertTrue((lake / "packages/source").exists())

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

    def test_staging_changed_snapshot_is_retained(self):
        lake = self.main / ".lake"
        stage = lake / ".release-token/build"
        stage.mkdir(parents=True)
        (stage / "generated").write_text("cache")
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

    def test_old_temporary_fifo_and_socket_are_removed(self):
        artifacts = self.root / "artifacts"
        artifacts.mkdir()
        fifo = artifacts / "clr-debug-pipe-1-1-in"
        os.mkfifo(fifo)
        endpoint = artifacts / "dotnet-diagnostic-1-1-socket"
        previous = os.getcwd()
        os.chdir(artifacts)
        try:
            with socket.socket(socket.AF_UNIX) as listener:
                listener.bind(endpoint.name)
        finally:
            os.chdir(previous)
        self.age(artifacts)
        recent = artifacts / "recent-fifo"
        os.mkfifo(recent)
        os.utime(recent, (self.cutoff + 1, self.cutoff + 1))
        rows = self.run_sweep()
        reasons = {row.get("path"): (row.get("action"), row.get("reason")) for row in rows}
        self.assertFalse(os.path.lexists(fifo) or os.path.lexists(endpoint),
                         "[FAIL] old_temporary_special_entries_removed: " + str(reasons))
        self.assertEqual(("kept", "recent"), reasons.get(str(recent)))
        self.assertTrue(os.path.lexists(recent))

    def test_temporary_sweep_reads_registrations_and_activity_once(self):
        calls = []
        for count in (1, 5):
            artifacts = self.root / ("artifacts-" + str(count))
            artifacts.mkdir()
            for index in range(count):
                (artifacts / ("old-" + str(index))).write_text("artifact")
            self.age(artifacts)
            self.run_sweep(artifact_root=artifacts)
            self.assertEqual([], list(artifacts.iterdir()))
            calls.append(self.sweep_calls)
        self.assertEqual(calls[0], calls[1], "[FAIL] temporary_checks_scale_with_candidates")

    def test_registered_worktree_under_temporary_root_stays_protected(self):
        target = self.root / "artifacts/registered"
        self.git(self.main, "worktree", "add", "-b", "registered", target)
        (target / "source").write_text("uncommitted work")
        self.age(target)
        rows = self.run_sweep(trees=(target,))
        self.assertEqual("uncommitted work", (target / "source").read_text())
        self.assertIn((str(target), "kept", "protected"),
                      {(row.get("path"), row.get("action"), row.get("reason")) for row in rows})

    def test_temporary_artifact_active_at_sweep_start_is_retained(self):
        held = self.root / "artifacts/held"
        held.mkdir(parents=True)
        (held / "log").write_text("open")
        self.age(held.parent)
        rows = self.run_sweep(active={held / "log"})
        self.assertTrue((held / "log").exists(), rows)
        self.assertIn((str(held), "kept", "protected"),
                      {(row.get("path"), row.get("action"), row.get("reason")) for row in rows})

    def test_lsof_observation_preserves_warning_handling(self):
        endpoint = self.root / "observed"
        observed = subprocess.CompletedProcess([], 0, "p123\nf4\ntREG\nn" + str(endpoint) + "\n", "warning")
        with patch.object(cleanup.subprocess, "run", return_value=observed):
            try:
                paths = cleanup.macos_active_paths()
            except OSError as error:
                self.fail("ordinary activity observations retain their warning policy: " + str(error))
        self.assertIn(endpoint, paths)

    def test_scoped_macos_observation_does_not_resolve_unrelated_paths(self):
        scope = self.root / "scope"
        endpoint = scope / "observed"
        unrelated = Path("/unrelated-observation")
        rows = "p123\nf4\ntREG\nn" + str(endpoint) + "\nf5\ntREG\nn" + str(unrelated / "file") + "\n"
        run = lambda command, **kwargs: subprocess.CompletedProcess(
            command, 0, rows if command[0] == "lsof" else "", "")
        resolve = Path.resolve
        def restricted(path, *args, **kwargs):
            if path == unrelated:
                raise AssertionError("an unrelated observation must be filtered before filesystem access")
            return resolve(path, *args, **kwargs)
        with patch.object(cleanup.sys, "platform", "darwin"), \
             patch.object(cleanup.subprocess, "run", side_effect=run), \
             patch.object(Path, "resolve", restricted):
            paths = cleanup.active_paths(self.root / "codex", scopes=[scope])
        self.assertIn(endpoint, paths)
        self.assertNotIn(unrelated / "file", paths)

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

    def test_unreadable_recent_artifact_does_not_abort_the_sweep(self):
        blocked = self.root / "artifacts/TemporaryItems"
        blocked.mkdir(parents=True)
        os.utime(blocked, (self.cutoff + 1, self.cutoff + 1))
        old = self.root / "artifacts/old"
        old.write_text("artifact")
        os.utime(old, (self.cutoff - 10, self.cutoff - 10))
        iterdir = Path.iterdir
        def restricted(path):
            if path == blocked:
                raise PermissionError(errno.EPERM, "Operation not permitted", str(path))
            return iterdir(path)
        with patch.object(cleanup, "candidates", return_value=iter([("tmp", blocked), ("tmp", old)])), \
             patch.object(Path, "iterdir", restricted):
            rows = self.run_sweep()
        self.assertFalse(old.exists(), rows)
        self.assertTrue(blocked.exists())
        self.assertIn(("lean_staging", str(blocked), "kept", "unreadable"),
                      {(row.get("category"), row.get("path"), row.get("action"), row.get("reason")) for row in rows})
        self.assertIsNone(rows[-1]["inventory_error"], rows)


if __name__ == "__main__":
    if sys.argv[1:] == ["--list-tests"]:
        print(json.dumps(["HostReclaimTests." + name
                          for name in unittest.defaultTestLoader.getTestCaseNames(HostReclaimTests)]))
    else:
        unittest.main()
