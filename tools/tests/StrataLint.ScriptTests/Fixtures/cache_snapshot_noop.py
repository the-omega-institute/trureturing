"""No-op snapshot cases composed into the existing cache contract suite."""
import contextlib
import io
import json
import os
import pathlib
import shutil
from unittest import mock


class NoopSnapshotCases:
    def test_unchanged_restored_layer_skips_snapshot_and_save(self):
        owner = self.restore_owner()
        source, cached, manifest = self.restore_fixture("project", {"a.olean": b"accepted"})
        with mock.patch.dict(os.environ, self.env), contextlib.redirect_stdout(io.StringIO()):
            owner.restore(self.root, owner.actions_keys(self.root), {"project": manifest["key"]}, ["project"])
        before = {path.relative_to(cached).as_posix(): path.read_bytes()
                  for path in cached.rglob("*") if path.is_file()}
        with mock.patch.dict(os.environ, self.env), contextlib.redirect_stdout(io.StringIO()) as receipts:
            owner.snapshot(self.root, owner.actions_keys(self.root), ["project"])
        output = receipts.getvalue()
        self.assertIn('"status": "save-disabled"', output)
        self.assertIn('"reason": "unchanged"', output)
        self.assertIn("project_ready=false", output)
        self.assertEqual(before, {path.relative_to(cached).as_posix(): path.read_bytes()
                                  for path in cached.rglob("*") if path.is_file()})
        self.assertFalse(list(cached.parent.glob(".snapshot-*")))

    def test_corrupt_restored_manifest_falls_through_to_normal_snapshot(self):
        owner = self.restore_owner()
        source, cached, manifest = self.restore_fixture("project", {"a.olean": b"accepted"})
        with mock.patch.dict(os.environ, self.env), contextlib.redirect_stdout(io.StringIO()):
            owner.restore(self.root, owner.actions_keys(self.root), {"project": manifest["key"]}, ["project"])
        manifest["files"][0]["sha256"] = "b" * 64
        (cached / "manifest.json").write_text(json.dumps(manifest))
        with mock.patch.dict(os.environ, self.env), contextlib.redirect_stdout(io.StringIO()) as receipts:
            owner.snapshot(self.root, owner.actions_keys(self.root), ["project"])
        self.assertIn('"status": "snapshot"', receipts.getvalue())
        self.assertIn("project_ready=true", receipts.getvalue())

    def test_dependency_noop_uses_the_current_snapshot_material_policy(self):
        owner = self.restore_owner()
        source, cached, manifest = self.restore_fixture("dependency", {
            "a.olean": b"accepted", "mathlib/.git/config": b"registered snapshot material"})
        with mock.patch.dict(os.environ, self.env), contextlib.redirect_stdout(io.StringIO()):
            owner.restore(self.root, owner.actions_keys(self.root), {"dependency": manifest["key"]}, ["dependency"])
        with mock.patch.dict(os.environ, self.env), contextlib.redirect_stdout(io.StringIO()) as receipts:
            owner.snapshot(self.root, owner.actions_keys(self.root), ["dependency"])
        output = receipts.getvalue()
        self.assertIn('"reason": "unchanged"', output)
        self.assertIn("dependency_ready=false", output)

    def test_failed_dependency_stamp_cannot_authorize_noop_snapshot(self):
        owner = self.restore_owner()
        source, cached, manifest = self.restore_fixture("dependency", {"a.olean": b"accepted"})
        stamp = self.root / ".lake/.stratalint-lean-cache-stamp.json"
        stamp.mkdir()
        with mock.patch.dict(os.environ, self.env), contextlib.redirect_stdout(io.StringIO()) as restored:
            keys = owner.actions_keys(self.root)
            owner.restore(self.root, keys, {"dependency": manifest["key"]}, ["dependency"])
        self.assertIn('"status": "miss"', restored.getvalue())
        self.assertNotIn('"status": "restored"', restored.getvalue())
        self.assertEqual(b"accepted", (source / "a.olean").read_bytes())
        with mock.patch.dict(os.environ, self.env), contextlib.redirect_stdout(io.StringIO()) as receipts:
            owner.snapshot(self.root, keys, ["dependency"])
        self.assertIn('"status": "snapshot"', receipts.getvalue())
        self.assertNotIn('"reason": "unchanged"', receipts.getvalue())
        self.assertIn("dependency_ready=true", receipts.getvalue())
        self.assertEqual(b"accepted", (cached / "data/a.olean").read_bytes())
        self.assertFalse((cached / "restored.json").exists())
        self.assertFalse(list(stamp.parent.glob(".stratalint-lean-cache-stamp.*.tmp")))

    def test_noop_requires_a_successful_restore_in_this_execution(self):
        owner = self.restore_owner()
        for failure in ("never-restored", "corrupt", "missing", "stale-run", "later-miss",
                        "later-missing-key", "manifest-replaced"):
            with self.subTest(failure=failure):
                shutil.rmtree(self.root / ".lake/build", ignore_errors=True)
                shutil.rmtree(self.root / "build/lean-cache/project", ignore_errors=True)
                source, cached, manifest = self.restore_fixture("project", {"a.olean": b"accepted"})
                (source / "current-only").unlink()
                with mock.patch.dict(os.environ, self.env), contextlib.redirect_stdout(io.StringIO()):
                    keys = owner.actions_keys(self.root)
                    if failure in ("corrupt", "missing"):
                        payload = cached / "data/a.olean"
                        if failure == "corrupt":
                            payload.write_bytes(b"corrupt")
                        else:
                            payload.unlink()
                        owner.restore(self.root, keys, {"project": manifest["key"]}, ["project"])
                    elif failure != "never-restored":
                        owner.restore(self.root, keys, {"project": manifest["key"]}, ["project"])
                        if failure == "stale-run":
                            keys["project"]["key"] += "0"
                        elif failure == "later-miss":
                            owner.restore(self.root, keys, {"project": ""}, ["project"])
                        elif failure == "later-missing-key":
                            owner.restore(self.root, keys, {}, ["project"])
                        else:
                            manifest["key"] += "0"
                            (cached / "manifest.json").write_text(json.dumps(manifest))
                with mock.patch.dict(os.environ, self.env), contextlib.redirect_stdout(io.StringIO()) as receipts:
                    owner.snapshot(self.root, keys, ["project"])
                self.assertIn('"status": "snapshot"', receipts.getvalue())
                self.assertIn("project_ready=true", receipts.getvalue())
                self.assertEqual(b"accepted", (cached / "data/a.olean").read_bytes())
                shutil.rmtree(source)
                shutil.rmtree(cached)

    def test_changed_restored_shape_is_snapshotted_in_one_read(self):
        owner = self.restore_owner()
        for change in ("added", "removed", "mode", "bytes"):
            with self.subTest(change=change):
                shutil.rmtree(self.root / ".lake/build", ignore_errors=True)
                shutil.rmtree(self.root / "build/lean-cache/project", ignore_errors=True)
                source, cached, manifest = self.restore_fixture("project", {
                    "a.olean": b"accepted", "z.olean": b"tail"})
                with mock.patch.dict(os.environ, self.env), contextlib.redirect_stdout(io.StringIO()):
                    keys = owner.actions_keys(self.root)
                    owner.restore(self.root, keys, {"project": manifest["key"]}, ["project"])
                if change == "added":
                    (source / "new.olean").write_bytes(b"new")
                elif change == "removed":
                    (source / "z.olean").unlink()
                elif change == "mode":
                    (source / "z.olean").chmod(0o755)
                else:
                    (source / "z.olean").write_bytes(b"changed")
                reads = {}
                original_open = pathlib.Path.open

                def counted(path, mode="r", *args, **kwargs):
                    if mode == "rb" and path.is_relative_to(source):
                        name = path.relative_to(source).as_posix()
                        reads[name] = reads.get(name, 0) + 1
                    return original_open(path, mode, *args, **kwargs)

                with mock.patch.dict(os.environ, self.env), \
                     mock.patch.object(pathlib.Path, "open", counted), \
                     contextlib.redirect_stdout(io.StringIO()) as receipts:
                    owner.snapshot(self.root, keys, ["project"])
                self.assertIn("project_ready=true", receipts.getvalue())
                # Only the smaller changed file needs comparison before
                # copy+hash; larger files are read once by the new snapshot.
                expected = {path.relative_to(source).as_posix():
                            2 if change == "bytes" and path.name == "z.olean" else 1
                            for path in source.rglob("*") if path.is_file()}
                self.assertEqual(expected, reads)
                shutil.rmtree(source)
                shutil.rmtree(cached)

    def test_noop_rejects_symlinks_and_special_material(self):
        owner = self.restore_owner()
        for kind in ("symlink", "fifo"):
            with self.subTest(kind=kind):
                shutil.rmtree(self.root / ".lake/build", ignore_errors=True)
                shutil.rmtree(self.root / "build/lean-cache/project", ignore_errors=True)
                source, cached, manifest = self.restore_fixture("project", {"a.olean": b"accepted"})
                with mock.patch.dict(os.environ, self.env), contextlib.redirect_stdout(io.StringIO()):
                    keys = owner.actions_keys(self.root)
                    owner.restore(self.root, keys, {"project": manifest["key"]}, ["project"])
                if kind == "symlink":
                    (source / "extra").symlink_to("a.olean")
                else:
                    os.mkfifo(source / "extra")
                before = (cached / "manifest.json").read_bytes()
                with mock.patch.dict(os.environ, self.env), contextlib.redirect_stdout(io.StringIO()) as receipts:
                    owner.snapshot(self.root, keys, ["project"])
                self.assertIn('"status": "save-failed"', receipts.getvalue())
                self.assertNotIn('"reason": "unchanged"', receipts.getvalue())
                self.assertIn("project_ready=false", receipts.getvalue())
                self.assertEqual(before, (cached / "manifest.json").read_bytes())

    def test_changed_small_provenance_does_not_reread_large_olean(self):
        owner = self.restore_owner()
        material = {"a.olean": bytes(range(251)) * 9000,
                    "z-report-provenance.json": b'{"candidate":"old"}\n'}
        source, cached, manifest = self.restore_fixture("project", material)
        with mock.patch.dict(os.environ, self.env), contextlib.redirect_stdout(io.StringIO()):
            keys = owner.actions_keys(self.root)
            owner.restore(self.root, keys, {"project": manifest["key"]}, ["project"])
        provenance = b'{"candidate":"new"}\n'
        (source / "z-report-provenance.json").write_bytes(provenance)
        observed = {name: 0 for name in material}
        original_open = pathlib.Path.open

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

        def counted(path, mode="r", *args, **kwargs):
            stream = original_open(path, mode, *args, **kwargs)
            if mode == "rb" and path.is_relative_to(source):
                return CountReads(stream, path.relative_to(source).as_posix())
            return stream

        with mock.patch.dict(os.environ, self.env), \
             mock.patch.object(pathlib.Path, "open", counted), \
             contextlib.redirect_stdout(io.StringIO()) as receipts:
            owner.snapshot(self.root, keys, ["project"])
        self.assertIn("project_ready=true", receipts.getvalue())
        self.assertEqual({"a.olean": len(material["a.olean"]),
                          "z-report-provenance.json": 2 * len(provenance)}, observed)
        self.assertEqual(material["a.olean"], (cached / "data/a.olean").read_bytes())
        self.assertEqual(provenance, (cached / "data/z-report-provenance.json").read_bytes())
