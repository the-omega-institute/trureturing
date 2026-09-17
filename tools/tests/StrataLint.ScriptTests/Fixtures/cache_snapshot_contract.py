"""Actions snapshot publication, material restoration, and rollback contracts."""
import builtins
import contextlib
import errno
import hashlib
import importlib
import io
import json
import os
import pathlib
import shutil
import signal
import subprocess
import sys
import unittest
from unittest import mock

from cache_fixture import CACHE, REPO, REV, CacheFixture
from cache_snapshot_noop import NoopSnapshotCases


class SnapshotContracts(NoopSnapshotCases, CacheFixture, unittest.TestCase):
    def restore_owner(self):
        sys.path.insert(0, str(CACHE.parent))
        return importlib.import_module("lean_actions")

    def test_layer_filter_cannot_expand_registered_stage_scope(self):
        owner = self.restore_owner()
        sys.path.insert(0, str(REPO / "tools/scripts/workflow"))
        plan = importlib.import_module("ci_plan")
        for selected in (False, True):
            with self.subTest(selected=selected):
                argv = [str(CACHE), "snapshot", "--repository", str(self.root),
                        "--stage", "current", "--layer", "current", "--bounded-cache"]
                with mock.patch.dict(os.environ, dict(self.env, CANDIDATE_SHA=REV,
                        CI_PLAN_PATH="build/ci/plan.json", CI_CHANGES_PATH="build/ci/changes.json")), \
                     mock.patch.object(sys, "argv", argv), \
                     mock.patch.object(plan, "git", return_value=(REV + "\n").encode()), \
                     mock.patch.object(plan, "validate_plan", return_value={}), \
                     mock.patch.object(plan, "stage_requirements", return_value={
                         "cache_layers": ["current", "project"] if selected else ["project"]}), \
                     mock.patch.object(owner, "actions_keys", wraps=owner.actions_keys) as keys, \
                     mock.patch.object(owner, "snapshot", wraps=owner.snapshot) as snapshot, \
                     contextlib.redirect_stdout(io.StringIO()) as receipts:
                    self.assertEqual(0, owner.main())
                self.assertIn("current_ready=false", receipts.getvalue())
                self.assertIn("save_timeout_minutes=1", receipts.getvalue())
                if selected:
                    self.assertEqual(["current"], snapshot.call_args.args[2])
                    self.assertEqual(1, keys.call_count)
                else:
                    snapshot.assert_not_called()
                    keys.assert_not_called()
                self.assertFalse((self.root / "build/lean-cache").exists())

    def test_bounded_snapshot_publishes_only_after_worker_and_save_window(self):
        owner = self.restore_owner()
        from cache_deadline import CacheDeadline
        source, cached, _ = self.restore_fixture("project", {"a.olean": b"accepted"})
        before = (cached / "manifest.json").read_bytes()
        (source / "a.olean").write_bytes(b"new source")
        for cutoff in (None, 100, 164, 400):
            with self.subTest(cutoff=cutoff), mock.patch.dict(os.environ, self.env), \
                 contextlib.redirect_stdout(io.StringIO()) as receipts:
                (self.root / "outputs").unlink(missing_ok=True)
                deadline = CacheDeadline(cutoff, reason="unavailable" if cutoff is None else "available",
                                         monotonic=lambda: 100)
                owner.snapshot(self.root, owner.actions_keys(self.root), ["project"], deadline=deadline)
                outputs = (self.root / "outputs").read_text().splitlines()
                self.assertEqual(["project_ready=" + str(cutoff == 400).lower(),
                                  "save_timeout_minutes=" + ("4" if cutoff == 400 else "1")], outputs)
                self.assertFalse(list(cached.parent.glob(".snapshot-*")))
                if cutoff == 400:
                    self.assertEqual(b"new source", (cached / "data/a.olean").read_bytes())
                else:
                    self.assertEqual(before, (cached / "manifest.json").read_bytes())
                    expected = "unavailable" if cutoff is None else "insufficient-cache-window"
                    self.assertIn('"reason": "' + expected + '"', receipts.getvalue())
                    self.assertIn('"remaining_seconds": ' + str(0 if cutoff is None else cutoff - 100),
                                  receipts.getvalue())

    def test_bounded_snapshot_timeout_and_signals_clean_only_owned_staging(self):
        owner = self.restore_owner()
        from cache_deadline import CacheDeadline
        source, cached, _ = self.restore_fixture("project", {"a.olean": b"accepted"})
        before = (cached / "manifest.json").read_bytes()
        sibling = cached.parent / ".snapshot-other-owner"
        sibling.mkdir()
        (sibling / "material").write_bytes(b"concurrent snapshot")
        for cancellation in ("timeout", signal.SIGTERM, signal.SIGINT, "late", "leader-exited"):
            process = mock.Mock(pid=12345)
            process.poll.return_value = None
            deadline = CacheDeadline(400, monotonic=lambda: 100)

            def start(command, **kwargs):
                self.assertNotIn("GITHUB_OUTPUT", kwargs["env"])
                self.assertTrue(kwargs["start_new_session"])
                staged = pathlib.Path(command[command.index("--snapshot-directory") + 1])
                (staged / "partial").write_bytes(b"unfinished new material")
                if cancellation == "late":
                    (staged / "manifest.json").write_text(json.dumps({"files": []}))
                return process

            def interrupted(*, timeout):
                self.assertEqual(235, timeout)
                if cancellation == "timeout":
                    raise subprocess.TimeoutExpired("snapshot", timeout)
                if cancellation == "late":
                    deadline.cutoff = 100
                    process.poll.return_value = 0
                    return 0
                if cancellation == "leader-exited":
                    process.poll.return_value = 7
                    return 7
                signal.getsignal(cancellation)(cancellation, None)

            calls = []
            def wait(*, timeout=None):
                calls.append(timeout)
                return interrupted(timeout=timeout) if len(calls) == 1 else 0
            process.wait.side_effect = wait
            with self.subTest(cancellation=cancellation), mock.patch.dict(os.environ, self.env), \
                 mock.patch.object(owner.subprocess, "Popen", side_effect=start), \
                 mock.patch.object(owner.os, "killpg") as kill, \
                 contextlib.redirect_stdout(io.StringIO()) as receipts:
                if cancellation in (signal.SIGTERM, signal.SIGINT):
                    with self.assertRaises(SystemExit) as raised:
                        owner.snapshot(self.root, owner.actions_keys(self.root), ["project"], deadline=deadline)
                    self.assertEqual(128 + cancellation, raised.exception.code)
                else:
                    owner.snapshot(self.root, owner.actions_keys(self.root), ["project"], deadline=deadline)
                kill.assert_called_once_with(process.pid, signal.SIGKILL)
                self.assertNotIn("project_ready=true", receipts.getvalue())
                self.assertIn("project_ready=false", receipts.getvalue())
                self.assertIn("save_timeout_minutes=1", receipts.getvalue())
                self.assertEqual(before, (cached / "manifest.json").read_bytes())
                self.assertEqual([sibling], list(cached.parent.glob(".snapshot-*")))
                self.assertEqual(b"concurrent snapshot", (sibling / "material").read_bytes())

    def test_bounded_snapshot_cleans_descendants_after_worker_exits(self):
        owner = self.restore_owner()
        from cache_deadline import CacheDeadline
        hooks = self.root / "hooks"
        hooks.mkdir()
        channel = self.root / "descendant-ready"
        os.mkfifo(channel)
        (hooks / "sitecustomize.py").write_text('''
import os, pathlib, subprocess, sys
if pathlib.Path(sys.argv[0]).name == "lean_actions.py":
    subprocess.Popen([sys.executable, "-c", "import signal,sys; channel=open(sys.argv[1], 'wb', buffering=0); channel.write(b'x'); signal.pause()", os.environ["DESCENDANT_CHANNEL"]])
    os._exit(7)
''')
        launch = subprocess.Popen
        streams = []

        def exited_worker(command, **kwargs):
            process = launch(command, **kwargs)
            stream = channel.open("rb", buffering=0)
            streams.append(stream)
            self.assertEqual(b"x", stream.read(1))
            # The actual worker is gone; its descendant still holds the pipe.
            self.assertEqual(7, process.wait())
            return process

        with mock.patch.dict(os.environ, dict(self.env, PYTHONPATH=str(hooks), DESCENDANT_CHANNEL=str(channel))), \
             mock.patch.object(owner.subprocess, "Popen", side_effect=exited_worker), \
             contextlib.redirect_stdout(io.StringIO()) as receipts:
            owner.snapshot(self.root, owner.actions_keys(self.root), ["project"],
                           deadline=CacheDeadline(400, monotonic=lambda: 100))
        self.assertIn("project_ready=false", receipts.getvalue())
        for stream in streams:
            # EOF proves the surviving descendant was also killed. The native
            # test runner's hang guard handles a regression without timing the verdict.
            self.assertEqual(b"", stream.read())
            stream.close()

    def test_snapshot_publication_failure_restores_previous_seed(self):
        owner = self.restore_owner()
        source, cached, _ = self.restore_fixture("project", {"a.olean": b"accepted"})
        before = {path.relative_to(cached).as_posix(): path.read_bytes()
                  for path in cached.rglob("*") if path.is_file()}
        (source / "a.olean").write_bytes(b"new source")
        rename = pathlib.Path.rename

        def fail_install(path, target):
            if path.name.startswith(".snapshot-") and target == cached:
                raise OSError("injected snapshot publication failure")
            return rename(path, target)

        with mock.patch.dict(os.environ, self.env), mock.patch.object(pathlib.Path, "rename", fail_install), \
             contextlib.redirect_stdout(io.StringIO()) as receipts:
            owner.snapshot(self.root, owner.actions_keys(self.root), ["project"])
        self.assertIn("project_ready=false", receipts.getvalue())
        self.assertEqual(before, {path.relative_to(cached).as_posix(): path.read_bytes()
                                 for path in cached.rglob("*") if path.is_file()})
        self.assertFalse(list(cached.parent.glob(".snapshot-*")))

    def test_large_layer_snapshot_copies_and_hashes_in_one_read(self):
        owner = self.restore_owner()
        material = {"a.olean": bytes(range(251)) * 9000, "nested/z.olean": b"last material"}
        for layer, target in (("dependency", ".lake/packages"), ("project", ".lake/build")):
            with self.subTest(layer=layer):
                source = self.root / target
                for name, data in material.items():
                    path = source / name
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_bytes(data)
                    path.chmod(0o640)
                    os.utime(path, (1_600_000_000, 1_600_000_000))
                observed = {"source": 0, "staged": 0}

                class CountReads:
                    def __init__(self, stream, area):
                        self.stream, self.area = stream, area

                    def __enter__(self):
                        return self

                    def __exit__(self, *args):
                        return self.stream.__exit__(*args)

                    def __getattr__(self, name):
                        return getattr(self.stream, name)

                    def read(self, size=-1):
                        data = self.stream.read(size)
                        observed[self.area] += len(data)
                        return data

                def instrument(open_file):
                    def opened(file, mode="r", *args, **kwargs):
                        stream = open_file(file, mode, *args, **kwargs)
                        path = pathlib.Path(file) if not isinstance(file, int) else None
                        if path is not None and "r" in mode:
                            if path.is_relative_to(source):
                                return CountReads(stream, "source")
                            if path.is_relative_to(self.root / "build/lean-cache") and path.suffix == ".olean":
                                return CountReads(stream, "staged")
                        return stream
                    return opened

                with mock.patch.dict(os.environ, self.env), \
                     mock.patch.object(io, "open", side_effect=instrument(io.open)), \
                     mock.patch.object(builtins, "open", side_effect=instrument(builtins.open)), \
                     mock.patch.object(shutil, "_HAS_FCOPYFILE", False, create=True), \
                     mock.patch.object(shutil, "_USE_CP_SENDFILE", False, create=True), \
                     contextlib.redirect_stdout(io.StringIO()) as receipts:
                    owner.snapshot(self.root, owner.actions_keys(self.root), [layer])
                self.assertIn('"status": "snapshot"', receipts.getvalue())
                self.assertEqual({"source": sum(map(len, material.values())), "staged": 0}, observed)
                cached = self.root / "build/lean-cache" / layer
                expected = [{"path": name, "sha256": hashlib.sha256(data).hexdigest(), "mode": 0o640}
                            for name, data in sorted(material.items())]
                self.assertEqual(expected, json.loads((cached / "manifest.json").read_text())["files"])
                for name, data in material.items():
                    destination = cached / "data" / name
                    self.assertEqual(data, destination.read_bytes())
                    self.assertEqual(0o640, destination.stat().st_mode & 0o777)
                    self.assertEqual(1_600_000_000, destination.stat().st_mtime)
                    self.assertNotEqual((source / name).stat().st_ino, destination.stat().st_ino)
                (source / "a.olean").write_bytes(b"source changed")
                self.assertEqual(material["a.olean"], (cached / "data/a.olean").read_bytes())

    def test_execution_snapshot_consumes_the_exporters_inventory(self):
        owner = self.restore_owner()
        for layer in ("engineering", "current"):
            with self.subTest(layer=layer):
                payload = b"already inventoried native transport material"
                inventory = [{"path": "material", "sha256": hashlib.sha256(payload).hexdigest(), "mode": 0o640}]

                def exported(root, selected, keys, destination):
                    self.assertEqual(layer, selected)
                    destination.mkdir()
                    (destination / "material").write_bytes(payload)
                    (destination / "material").chmod(0o640)
                    return inventory

                with mock.patch.dict(os.environ, self.env), \
                     mock.patch.object(owner, "snapshot_execution", side_effect=exported), \
                     mock.patch.object(owner, "files", side_effect=AssertionError("export material was read twice")), \
                     contextlib.redirect_stdout(io.StringIO()) as receipts:
                    owner.snapshot(self.root, owner.actions_keys(self.root), [layer])
                self.assertIn('"status": "snapshot"', receipts.getvalue())
                cached = self.root / "build/lean-cache" / layer
                self.assertEqual(inventory, json.loads((cached / "manifest.json").read_text())["files"])
                self.assertEqual(payload, (cached / "data/material").read_bytes())

    def test_snapshot_late_read_failure_keeps_published_material_and_source(self):
        owner = self.restore_owner()
        for layer in ("dependency", "project"):
            with self.subTest(layer=layer):
                source, cached, _ = self.restore_fixture(layer, {"a.olean": b"accepted", "z.olean": b"last"})
                before = {path.relative_to(cached).as_posix(): path.read_bytes()
                          for path in cached.rglob("*") if path.is_file()}
                (source / "a.olean").write_bytes(b"new source")
                def fail_late(open_file):
                    def opened(path, mode="r", *args, **kwargs):
                        if pathlib.Path(path) == source / "z.olean" and mode == "rb":
                            raise OSError("injected late source read failure")
                        return open_file(path, mode, *args, **kwargs)
                    return opened

                with mock.patch.dict(os.environ, self.env), \
                     mock.patch.object(io, "open", side_effect=fail_late(io.open)), \
                     mock.patch.object(builtins, "open", side_effect=fail_late(builtins.open)), \
                     contextlib.redirect_stdout(io.StringIO()) as receipts:
                    owner.snapshot(self.root, owner.actions_keys(self.root), [layer])
                self.assertIn(layer + "_ready=false", receipts.getvalue())
                self.assertEqual(before, {path.relative_to(cached).as_posix(): path.read_bytes()
                                         for path in cached.rglob("*") if path.is_file()})
                self.assertEqual(b"new source", (source / "a.olean").read_bytes())
                self.assertFalse(list(cached.parent.glob(".snapshot-*")))

    def check_private_seed_copy_rejects_late_changes_without_replacing_target(self):
        owner = self.restore_owner()
        with mock.patch.dict(os.environ, self.env):
            keys = owner.actions_keys(self.root)
        spec = keys["judge"]
        cached = self.root / spec["path"]
        target = self.root / spec["target"]
        target.mkdir()
        (target / "current-only").write_bytes(b"accepted candidate material")
        inventory = []
        for relative, data in (("a.dll", b"first material"), ("nested/z.dll", b"last material")):
            path = cached / "data" / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
            path.chmod(0o640)
            inventory.append({"path": relative, "sha256": hashlib.sha256(data).hexdigest(), "mode": 0o640})
        (cached / "manifest.json").write_text(json.dumps({"schema": "lean-actions-seed-v1",
            "partition": keys["partition"], "layer": "judge", "key": spec["key"], "files": inventory}))
        copy_metadata = shutil.copystat

        def change_next_source(source, destination, **kwargs):
            copy_metadata(source, destination, **kwargs)
            if pathlib.Path(source) == cached / "data/a.dll":
                (cached / "data/nested/z.dll").write_bytes(b"changed during staging")

        with mock.patch.dict(os.environ, self.env), \
             mock.patch.object(shutil, "copystat", side_effect=change_next_source), \
             contextlib.redirect_stdout(io.StringIO()) as receipts:
            owner.restore(self.root, keys, {"judge": spec["key"]}, ["judge"], registry={})
        self.assertIn('"status": "miss"', receipts.getvalue())
        self.assertIn("cache material integrity mismatch: nested/z.dll", receipts.getvalue())
        self.assertEqual(["current-only"], sorted(path.name for path in target.iterdir()))
        self.assertEqual(b"accepted candidate material", (target / "current-only").read_bytes())
        self.assertFalse(list(target.parent.glob(".actions-*")))

    def test_same_filesystem_restore_moves_validated_material_without_copy(self):
        owner = self.restore_owner()
        source, cached, manifest = self.restore_fixture("project", {"a.olean": b"cached", "nested/z.olean": b"tail"})
        identities = {path.relative_to(cached / "data").as_posix():
                      (path.stat().st_dev, path.stat().st_ino)
                      for path in (cached / "data").rglob("*") if path.is_file()}
        with mock.patch.dict(os.environ, self.env), contextlib.redirect_stdout(io.StringIO()) as receipts:
            owner.restore(self.root, owner.actions_keys(self.root), {"project": manifest["key"]}, ["project"])
        self.assertIn('"status": "restored"', receipts.getvalue())
        self.assertFalse((cached / "data").exists())
        self.assertFalse((source / "current-only").exists())
        for relative, inode in identities.items():
            restored = source / relative
            self.assertEqual(inode, (restored.stat().st_dev, restored.stat().st_ino))

    def test_same_filesystem_restore_rejects_extra_member_before_publication(self):
        owner = self.restore_owner()
        source, cached, manifest = self.restore_fixture("project", {"a.olean": b"cached"})
        (cached / "data/extra.olean").write_bytes(b"unregistered")
        before = {path.relative_to(source).as_posix(): path.read_bytes()
                  for path in source.rglob("*") if path.is_file()}
        with mock.patch.dict(os.environ, self.env), contextlib.redirect_stdout(io.StringIO()) as receipts:
            owner.restore(self.root, owner.actions_keys(self.root), {"project": manifest["key"]}, ["project"])
        self.assertIn('"status": "miss"', receipts.getvalue())
        self.assertEqual(before, {path.relative_to(source).as_posix(): path.read_bytes()
                                  for path in source.rglob("*") if path.is_file()})
        self.assertTrue((cached / "data/extra.olean").is_file())

    def test_same_filesystem_restore_allows_unlisted_empty_directory(self):
        owner = self.restore_owner()
        source, cached, manifest = self.restore_fixture("project", {"a.olean": b"cached"})
        (cached / "data/empty-directory").mkdir()
        with mock.patch.dict(os.environ, self.env), contextlib.redirect_stdout(io.StringIO()) as receipts:
            owner.restore(self.root, owner.actions_keys(self.root), {"project": manifest["key"]}, ["project"])
        self.assertIn('"status": "restored"', receipts.getvalue())
        self.assertTrue((source / "empty-directory").is_dir())
        self.assertFalse((cached / "data").exists())

    def test_same_filesystem_restore_rolls_back_install_failure_and_source(self):
        owner = self.restore_owner()
        source, cached, manifest = self.restore_fixture("project", {"a.olean": b"cached"})
        before = {path.relative_to(source).as_posix(): path.read_bytes()
                  for path in source.rglob("*") if path.is_file()}
        original_rename = pathlib.Path.rename
        def fail_install(path, target):
            if path.name == "data" and target == source:
                raise OSError(errno.EIO, "fixture install failure")
            return original_rename(path, target)
        with mock.patch.dict(os.environ, self.env), \
             mock.patch.object(pathlib.Path, "rename", fail_install), \
             contextlib.redirect_stdout(io.StringIO()) as receipts:
            owner.restore(self.root, owner.actions_keys(self.root), {"project": manifest["key"]}, ["project"])
        self.assertIn('"status": "miss"', receipts.getvalue())
        self.assertEqual(before, {path.relative_to(source).as_posix(): path.read_bytes()
                                  for path in source.rglob("*") if path.is_file()})
        self.assertTrue((cached / "data").is_dir())
        self.assertFalse(list(source.parent.glob(".actions-*")))

    def restore_fixture(self, layer, material):
        source = self.root / (".lake/packages" if layer == "dependency" else ".lake/build")
        for relative, data in material.items():
            path = source / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
            path.chmod(0o640)
            os.utime(path, (1_600_000_000, 1_600_000_000))
        snapshot = self.run_tool(CACHE, "snapshot", "--layers", layer)
        self.assertEqual(0, snapshot.returncode, snapshot.stdout + snapshot.stderr)
        self.assertIn('"status": "snapshot"', snapshot.stdout)
        cached = self.root / "build/lean-cache" / layer
        manifest = json.loads((cached / "manifest.json").read_text())
        (source / "current-only").write_bytes(b"current material")
        return source, cached, manifest

    def test_dependency_and_project_restore_read_each_material_once(self):
        owner = self.restore_owner()
        material = {"a.olean": bytes(range(251)) * 9000, "nested/z.olean": b"last material"}
        for layer in ("dependency", "project"):
            with self.subTest(layer=layer):
                source, cached, manifest = self.restore_fixture(layer, material)
                (cached / "data/unlisted").write_bytes(b"unlisted neighbour")
                observed = {relative: 0 for relative in material}

                class CountReads:
                    def __init__(self, stream, name):
                        self.stream, self.name = stream, name

                    def __enter__(self):
                        return self

                    def __exit__(self, *args):
                        return self.stream.__exit__(*args)

                    def __getattr__(self, name):
                        return getattr(self.stream, name)

                    def read(self, size=-1):
                        data = self.stream.read(size)
                        observed[self.name] += len(data)
                        return data

                def instrument(open_file):
                    def opened(file, mode="r", *args, **kwargs):
                        stream = open_file(file, mode, *args, **kwargs)
                        path = pathlib.Path(file) if not isinstance(file, int) else None
                        if path is not None and "r" in mode and path.is_relative_to(cached / "data"):
                            relative = path.relative_to(cached / "data").as_posix()
                            self.assertIn(relative, observed, "unlisted cache material was read")
                            return CountReads(stream, relative)
                        return stream
                    return opened

                # Observe bytes through the portable stream path, including copy2's reads.
                # Fast-copy syscalls bypass Python stream instrumentation.
                original_rename = pathlib.Path.rename
                def force_cross_device(path, target):
                    if path == cached / "data":
                        raise OSError(errno.EXDEV, "fixture cross-device cache")
                    return original_rename(path, target)
                with mock.patch.dict(os.environ, self.env), \
                     mock.patch.object(io, "open", side_effect=instrument(io.open)), \
                     mock.patch.object(builtins, "open", side_effect=instrument(builtins.open)), \
                     mock.patch.object(shutil, "_HAS_FCOPYFILE", False, create=True), \
                     mock.patch.object(shutil, "_USE_CP_SENDFILE", False, create=True), \
                     mock.patch.object(pathlib.Path, "rename", force_cross_device), \
                     contextlib.redirect_stdout(io.StringIO()) as receipts:
                    owner.restore(self.root, owner.actions_keys(self.root), {layer: manifest["key"]}, [layer])
                self.assertIn('"status": "restored"', receipts.getvalue())
                self.assertEqual({name: len(data) for name, data in material.items()}, observed)
                self.assertFalse((source / "current-only").exists())
                self.assertFalse((source / "unlisted").exists())
                for relative, data in material.items():
                    self.assertEqual(data, (source / relative).read_bytes())
                    self.assertEqual(0o640, (source / relative).stat().st_mode & 0o777)
                    self.assertEqual(1_600_000_000, (source / relative).stat().st_mtime)
                (source / "a.olean").write_bytes(b"changed consumer")
                self.assertEqual(material["a.olean"], (cached / "data/a.olean").read_bytes())

    def test_dependency_and_project_reject_late_bad_material_without_installing(self):
        owner = self.restore_owner()
        material = {"a.olean": b"first material", "nested/z.olean": b"last material"}
        for layer in ("dependency", "project"):
            source, cached, manifest = self.restore_fixture(layer, material)
            for failure in ("hash", "mode", "missing", "directory", "symlink", "parent-link",
                            "duplicate", "escape", "backslash", "invalid-sha", "invalid-mode", "empty", "copy-error"):
                with self.subTest(layer=layer, failure=failure):
                    saved = cached / "data/nested/z.olean"
                    inventory = json.loads(json.dumps(manifest))
                    last = inventory["files"][-1]
                    if failure == "hash":
                        saved.write_bytes(b"corrupt")
                    elif failure == "mode":
                        saved.chmod(0o755)
                    elif failure in ("missing", "directory", "symlink"):
                        saved.unlink()
                        if failure == "directory":
                            saved.mkdir()
                        elif failure == "symlink":
                            saved.symlink_to("../a.olean")
                    elif failure == "parent-link":
                        saved.parent.rename(cached / "data/real-nested")
                        saved.parent.symlink_to("real-nested", target_is_directory=True)
                    elif failure == "duplicate":
                        inventory["files"].append(dict(last))
                    elif failure == "escape":
                        last["path"] = "../escaped"
                    elif failure == "backslash":
                        last["path"] = "nested\\z.olean"
                    elif failure == "invalid-sha":
                        last["sha256"] = "broken"
                    elif failure == "invalid-mode":
                        last["mode"] = True
                    elif failure == "empty":
                        inventory["files"] = []
                    (cached / "manifest.json").write_text(json.dumps(inventory))
                    copy_metadata = shutil.copystat

                    def copy_failure(original, destination, **kwargs):
                        if pathlib.Path(original) == saved:
                            raise OSError("injected copy failure after earlier material was staged")
                        return copy_metadata(original, destination, **kwargs)

                    fault = (mock.patch.object(shutil, "copystat", side_effect=copy_failure)
                             if failure == "copy-error" else contextlib.nullcontext())
                    original_rename = pathlib.Path.rename
                    def force_cross_device(path, target):
                        if path == cached / "data":
                            raise OSError(errno.EXDEV, "fixture cross-device cache")
                        return original_rename(path, target)
                    rename_fault = (mock.patch.object(pathlib.Path, "rename", force_cross_device)
                                    if failure == "copy-error" else contextlib.nullcontext())
                    with mock.patch.dict(os.environ, self.env), fault, rename_fault, contextlib.redirect_stdout(io.StringIO()) as receipts:
                        owner.restore(self.root, owner.actions_keys(self.root), {layer: manifest["key"]}, [layer])
                    self.assertIn('"status": "miss"', receipts.getvalue())
                    self.assertEqual(b"current material", (source / "current-only").read_bytes())
                    self.assertEqual(material["a.olean"], (source / "a.olean").read_bytes())
                    self.assertEqual(material["nested/z.olean"], (source / "nested/z.olean").read_bytes())
                    self.assertEqual([], list(source.parent.glob(".actions-*")))
                    if failure == "parent-link":
                        saved.parent.unlink()
                        (cached / "data/real-nested").rename(saved.parent)
                    if saved.is_dir():
                        saved.rmdir()
                    else:
                        saved.unlink(missing_ok=True)
                    saved.write_bytes(material["nested/z.olean"])
                    saved.chmod(0o640)

    def test_dependency_and_project_restore_rolls_back_on_rename_or_exdev(self):
        owner = self.restore_owner()
        material = {"a.olean": b"cached material", "nested/z.olean": b"cached tail"}
        for layer in ("dependency", "project"):
            with self.subTest(layer=layer):
                source, cached, manifest = self.restore_fixture(layer, material)
                target_before = {path.relative_to(source).as_posix(): path.read_bytes()
                                 for path in source.rglob("*") if path.is_file()}
                (source / "private.keep").write_bytes(b"candidate material")
                target_before["private.keep"] = b"candidate material"
                original_rename = pathlib.Path.rename
                for failure, code in (("rename", errno.EIO), ("exdev", errno.EXDEV)):
                    with self.subTest(failure=failure):
                        def fail_install(path, target):
                            if path.name == "data" and target == source:
                                raise OSError(code, "injected " + failure + " during cache install")
                            return original_rename(path, target)

                        with mock.patch.dict(os.environ, self.env), \
                             mock.patch.object(pathlib.Path, "rename", fail_install), \
                             contextlib.redirect_stdout(io.StringIO()) as receipts:
                            owner.restore(self.root, owner.actions_keys(self.root),
                                          {layer: manifest["key"]}, [layer])
                        self.assertIn('"status": "miss"', receipts.getvalue())
                        self.assertEqual(target_before,
                                         {path.relative_to(source).as_posix(): path.read_bytes()
                                          for path in source.rglob("*") if path.is_file()})
                        self.assertEqual([], list(source.parent.glob(".actions-*")))

    def test_corrupt_cache_is_rejected_before_replacing_existing_target(self):
        owner = self.restore_owner()
        for layer in ("dependency", "project"):
            with self.subTest(layer=layer):
                source, cached, manifest = self.restore_fixture(layer, {"a.olean": b"cached"})
                (source / "private.keep").write_bytes(b"candidate material")
                (cached / "data/a.olean").write_bytes(b"corrupt cache")
                with mock.patch.dict(os.environ, self.env), contextlib.redirect_stdout(io.StringIO()) as receipts:
                    owner.restore(self.root, owner.actions_keys(self.root),
                                  {layer: manifest["key"]}, [layer])
                self.assertIn('"status": "miss"', receipts.getvalue())
                self.assertEqual(b"cached", (source / "a.olean").read_bytes())
                self.assertEqual(b"candidate material", (source / "private.keep").read_bytes())
        self.check_private_seed_copy_rejects_late_changes_without_replacing_target()

    def test_dependency_module_and_submodule_seed_round_trip(self):
        self.assert_module_and_submodule_seed_round_trip("dependency")

    def test_project_module_and_submodule_seed_round_trip(self):
        self.assert_module_and_submodule_seed_round_trip("project")

    def assert_module_and_submodule_seed_round_trip(self, layer):
        source = self.root / (".lake/packages" if layer == "dependency" else ".lake/build")
        prefix = "mathlib/.lake/build/lib/lean" if layer == "dependency" else "lib/lean"
        material = {
            prefix + "/Foo.olean": (b"module bytes", 0o640),
            prefix + "/Foo/Bar.olean": (b"submodule bytes", 0o644),
        }
        for relative, (data, mode) in material.items():
            path = source / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
            path.chmod(mode)
        snapshot = self.run_tool(CACHE, "snapshot", "--layers", layer)
        self.assertEqual(0, snapshot.returncode, snapshot.stdout + snapshot.stderr)
        self.assertIn('"status": "snapshot"', snapshot.stdout, snapshot.stdout + snapshot.stderr)
        cached = self.root / "build/lean-cache" / layer
        key = json.loads((cached / "manifest.json").read_text())["key"]
        shutil.rmtree(source)
        restore = self.run_tool(CACHE, "restore", "--layers", layer, "--" + layer + "-key", key)
        self.assertEqual(0, restore.returncode, restore.stdout + restore.stderr)
        self.assertIn('"status": "restored"', restore.stdout, restore.stdout + restore.stderr)
        for relative, (data, mode) in material.items():
            path = source / relative
            self.assertEqual(data, path.read_bytes())
            self.assertEqual(mode, path.stat().st_mode & 0o777)

    def test_internal_dependency_file_links_round_trip_as_private_material(self):
        source, material = self.dependency_files()
        links = {
            "mathlib/scripts/bench/size/run.py": "run",
            "mathlib/scripts/bench/build/fake-root/bin/lean.py": "lean",
            "batteries/docs/README.md": "../README.md",
            "batteries/docs/README.alias": "README.md",
        }
        expected = dict(material)
        for relative, target in links.items():
            path = source / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.symlink_to(target)
            expected[relative] = (path.read_bytes(), path.stat().st_mode & 0o777)
        readiness, receipts = self.snapshot_result()
        self.assertEqual({"dependency_ready": "true", "project_ready": "false"},
                         readiness, receipts)
        self.assertEqual("snapshot", receipts["dependency"]["status"])
        cached = self.root / "build/lean-cache/dependency"
        manifest = json.loads((cached / "manifest.json").read_text())
        self.assertEqual("lean-actions-seed-v1", manifest["schema"])
        self.assertEqual([{"path": relative, "sha256": hashlib.sha256(data).hexdigest(), "mode": mode}
                          for relative, (data, mode) in sorted(expected.items())], manifest["files"])
        self.assertFalse(any(path.is_symlink() for path in (cached / "data").rglob("*")))
        for relative, (data, mode) in expected.items():
            self.assertEqual(data, (source / relative).read_bytes())
            self.assertEqual(mode, (source / relative).stat().st_mode & 0o777)
            self.assertEqual(data, (cached / "data" / relative).read_bytes())
        for relative, target in links.items():
            self.assertTrue((source / relative).is_symlink())
            self.assertEqual(target, os.readlink(source / relative))
        (source / "batteries/README.md").write_bytes(b"changed producer bytes")
        self.assertEqual(expected["batteries/README.md"][0], (cached / "data/batteries/README.md").read_bytes())
        shutil.rmtree(source)
        result = self.run_tool(CACHE, "restore", "--dependency-key", manifest["key"])
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertIn('"status": "restored"', result.stdout)
        self.assertIn("STRATALINT_ACTIONS_CACHE_SEEDED=0", (self.root / "environment").read_text())
        for relative, (data, mode) in expected.items():
            path = source / relative
            self.assertFalse(path.is_symlink())
            self.assertEqual(data, path.read_bytes())
            self.assertEqual(mode, path.stat().st_mode & 0o777)
        (source / "batteries/docs/README.md").write_bytes(b"changed consumer bytes")
        self.assertEqual(b"changed consumer bytes", (source / "batteries/docs/README.md").read_bytes())
        self.assertFalse((cached / "data").exists())

    def test_corrupt_dependency_seed_falls_back_without_replacing_current_material(self):
        source, _ = self.dependency_files()
        shutil.copy2(source / "batteries/README.md", source / "batteries/README.copy")
        readiness, _ = self.snapshot_result()
        self.assertEqual("true", readiness["dependency_ready"])
        cached = self.root / "build/lean-cache/dependency"
        key = json.loads((cached / "manifest.json").read_text())["key"]
        saved = cached / "data/batteries/README.md"
        original, mode = saved.read_bytes(), saved.stat().st_mode & 0o777
        (self.root / "Makefile").write_text("current:\n\t@echo producer >> calls\n\t@exit $${PRODUCER_EXIT:-0}\n")
        for corruption in ("bytes", "mode", "link", "missing", "extra"):
            with self.subTest(corruption=corruption):
                (source / "batteries/README.md").write_bytes(b"current material")
                if corruption == "bytes":
                    saved.write_bytes(b"corrupted bytes")
                elif corruption == "mode":
                    saved.chmod(0o755)
                elif corruption == "link":
                    saved.unlink()
                    saved.symlink_to("README.copy")
                elif corruption == "missing":
                    saved.unlink()
                else:
                    (saved.parent / "extra").write_bytes(b"unlisted")
                for production_exit in ("0", "9"):
                    result = subprocess.run(["bash", "-euc",
                        '"$PYTHON" "$CACHE" restore --repository "$ROOT" --dependency-key "$KEY"; make -C "$ROOT" current'],
                        env=dict(self.env, PYTHON=sys.executable, CACHE=str(CACHE), ROOT=str(self.root),
                                 KEY=key, PRODUCER_EXIT=production_exit), capture_output=True, text=True)
                    self.assertEqual(production_exit == "0", result.returncode == 0, result.stdout + result.stderr)
                    if corruption == "extra":
                        # A same-filesystem move rejects unregistered members
                        # instead of publishing them into the target tree.
                        self.assertIn('"status": "miss"', result.stdout)
                        self.assertEqual(b"current material", (source / "batteries/README.md").read_bytes())
                        self.assertEqual(b"unlisted", (saved.parent / "extra").read_bytes())
                    else:
                        self.assertIn('"layer": "dependency", "reason":', result.stdout)
                        self.assertIn('"status": "miss"', result.stdout)
                        self.assertEqual(b"current material", (source / "batteries/README.md").read_bytes())
                    self.assertNotIn("STRATALINT_ACTIONS_CACHE_SEEDED=1", (self.root / "environment").read_text())
                saved.unlink(missing_ok=True)
                saved.write_bytes(original)
                saved.chmod(mode)
                (saved.parent / "extra").unlink(missing_ok=True)
        self.assertEqual(["producer"] * 10, (self.root / "calls").read_text().splitlines())


if __name__ == "__main__":
    unittest.main()
