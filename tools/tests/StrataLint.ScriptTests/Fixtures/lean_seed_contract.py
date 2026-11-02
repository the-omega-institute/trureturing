"""Release transport behavior contracts using private local fixtures."""
import json
import hashlib
import os
import platform
import random
import subprocess
import datetime
import shutil
import sys
import tarfile
import unittest

from lean_seed_support import INPUT, OTHER, PUBLISH, REV, ROOT, PartitionFixture, digest, write
from lean_seed_transport import FAKE_GH, ReleaseTransportCases
from lean_release_verification import ReleaseVerificationCases
from lean_release_legacy import ReleaseLegacyCases


class TransportTests(ReleaseLegacyCases, ReleaseVerificationCases, ReleaseTransportCases, unittest.TestCase):
    """Release transport cases exposed under their existing test identity."""

    def local_environment(self, **changes):
        return dict(GITHUB_ACTIONS="false", GITHUB_EVENT_NAME="", GITHUB_REF="", GITHUB_REPOSITORY="",
                    GITHUB_SHA="not-an-input", GITHUB_RUN_ID="", GITHUB_RUN_ATTEMPT="", **changes)

    def three_parts(self, snapshot, packed=None):
        archive = snapshot / "lean-build.tgz"
        packed = archive.read_bytes() if packed is None else packed
        archive.unlink(missing_ok=True)
        manifest = json.loads((snapshot / "manifest.json").read_text())
        width = len(packed) * 2 // 5
        manifest.update(archive_bytes=len(packed), archive_sha256=digest(packed), parts=[])
        for index, start in enumerate(range(0, len(packed), width)):
            chunk = packed[start:start + width]
            name = f"lean-build.tgz.part-{index:02d}"
            (snapshot / name).write_bytes(chunk)
            manifest["parts"].append(dict(name=name, bytes=len(chunk), sha256=digest(chunk)))
        self.assertEqual(3, len(manifest["parts"]))
        self.assertLess(manifest["parts"][-1]["bytes"], width)
        write(snapshot / "manifest.json", json.dumps(manifest))
        return manifest

    def reassembly_probe(self, failure="", append=False):
        probe = self.bin / "sitecustomize.py"
        prefix = probe.read_text() if append else ""
        write(probe, prefix + '''
import errno, json, os, pathlib, shutil, sys, tarfile
if sys.argv[0].endswith("lean_cache_release.py"):
    sys.path.insert(0, os.environ["FAKE_REASSEMBLY_HELPER"])
    import cache_material
    original_open, original_unlink = pathlib.Path.open, pathlib.Path.unlink
    original_copy, original_extract, original_sha = shutil.copyfileobj, tarfile.TarFile.extractall, cache_material.sha
    failure = os.environ["FAKE_REASSEMBLY_FAILURE"]
    sources, validated = {}, {}
    output = None
    def record(**event):
        with open(os.environ["FAKE_REASSEMBLY_LOG"], "a") as log:
            log.write(json.dumps(event) + "\\n")
    def sample(stage, operation):
        files = {p.name: p.stat().st_size for p in stage.glob("lean-build.tgz*") if p.is_file()}
        record(operation=operation, resident=sum(files.values()), files=files)
    def sha(path):
        value = original_sha(path)
        if path.name.startswith("lean-build.tgz.part-") or path.name == "manifest.json":
            validated[path.name] = validated.get(path.name, 0) + 1
            if path.name.endswith("part-02"):
                if failure == "part-digest" or (failure == "asset-digest" and validated[path.name] == 2):
                    return "0" * 64
                if failure == "part-size":
                    with original_open(path, "r+b") as part:
                        part.truncate(path.stat().st_size - 1)
        return value
    class Output:
        def __init__(self, raw, stage): self.raw, self.stage, self.flushed = raw, stage, None
        def __getattr__(self, name): return getattr(self.raw, name)
        def __enter__(self): return self
        def __exit__(self, *args):
            result = self.raw.__exit__(*args)
            sample(self.stage, "close")
            return result
        def write(self, block):
            if failure == "enospc" and len(sources) == 2:
                self.raw.write(block[:1])
                raise OSError(errno.ENOSPC, "injected reassembly enospc")
            result = self.raw.write(block)
            sample(self.stage, "write")
            return result
        def flush(self):
            if failure == "flush" and len(sources) == 2:
                raise OSError(errno.EIO, "injected reassembly flush")
            self.raw.flush()
            self.flushed = self.raw.tell()
            sample(self.stage, "flush")
    def open_path(path, mode="r", *args, **kwargs):
        global output
        raw = original_open(path, mode, *args, **kwargs)
        if path.name == "lean-build.tgz" and mode == "wb" and (path.parent / "manifest.json").is_file():
            output = Output(raw, path.parent)
            return output
        return raw
    def copy(source, target, *args, **kwargs):
        if target is not output:
            return original_copy(source, target, *args, **kwargs)
        sources[pathlib.Path(source.name).name] = source
        if len(sources) == 2 and failure in ("copy", "short", "long"):
            target.write(source.read(1))
            if failure == "copy":
                raise OSError(errno.EIO, "injected reassembly copy")
            if failure == "short": return
        result = original_copy(source, target, *args, **kwargs)
        if len(sources) == 2 and failure == "long": target.write(b"extra")
        return result
    def unlink(path, *args, **kwargs):
        if output is not None and path.parent == output.stage and path.name in sources:
            source = sources[path.name]
            record(operation="unlink", name=path.name, stage=str(path.parent), closed=source.closed,
                   position=output.tell(), flushed=output.flushed, validated=validated.copy())
            sample(path.parent, "before-unlink")
            if failure == "unlink" and len(sources) == 2:
                raise OSError(errno.EIO, "injected reassembly unlink")
        return original_unlink(path, *args, **kwargs)
    def extract(archive, path, *args, **kwargs):
        sample(pathlib.Path(archive.name).parent, "extract")
        return original_extract(archive, path, *args, **kwargs)
    pathlib.Path.open, pathlib.Path.unlink = open_path, unlink
    shutil.copyfileobj, tarfile.TarFile.extractall, cache_material.sha = copy, extract, sha
''')
        log = self.root / "reassembly-events"
        log.unlink(missing_ok=True)
        return dict(PYTHONPATH=str(self.bin), FAKE_REASSEMBLY_HELPER=str(self.publisher.parent),
                    FAKE_REASSEMBLY_LOG=str(log), FAKE_REASSEMBLY_FAILURE=failure)

    def reassembly_events(self):
        log = self.root / "reassembly-events"
        return [json.loads(line) for line in log.read_text().splitlines()] if log.exists() else []

    def assert_reassembly_released(self, manifest):
        events = self.reassembly_events()
        removals = [event for event in events if event["operation"] == "unlink"]
        self.assertEqual([part["name"] for part in manifest["parts"]], [event["name"] for event in removals])
        position = 0
        for event, part in zip(removals, manifest["parts"]):
            position += part["bytes"]
            self.assertTrue(event["closed"])
            self.assertEqual(position, event["position"])
            self.assertEqual(position, event["flushed"])
            self.assertTrue(all(event["validated"][name] == 2
                for name in ["manifest.json", *[part["name"] for part in manifest["parts"]]]))
        size = manifest["archive_bytes"]
        self.assertEqual(size + max(part["bytes"] for part in manifest["parts"]),
                         max(event["resident"] for event in events if "resident" in event))
        extracted = next(event for event in events if event["operation"] == "extract")
        self.assertEqual({"lean-build.tgz": size}, extracted["files"])

    def test_multipart_restore_releases_validated_closed_flushed_parts_before_extraction(self):
        payload = random.Random(31).randbytes(64 * 1024)
        material = self.root / ".lake/build/lib/lean/D5/A.olean"
        material.write_bytes(payload)
        self.assertEqual(0, self.transport("publish").returncode)
        manifest = self.three_parts(next(self.remote.iterdir()))
        shutil.rmtree(self.root / ".lake/build")
        result = self.transport("fetch", **self.reassembly_probe())
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertEqual(payload, material.read_bytes())
        self.assert_reassembly_released(manifest)

    def test_multipart_reassembly_failures_preserve_old_build_and_base(self):
        self.assertEqual(0, self.transport("publish").returncode)
        self.three_parts(next(self.remote.iterdir()))
        write(self.root / ".lake/build/keep.txt", "old build")
        write(self.root / ".lake/lean-report-seed-base.json", "old base")
        lake = self.root / ".lake"
        before = {str(p.relative_to(lake)): p.read_bytes() for p in lake.rglob("*") if p.is_file()}
        staging = self.root / "private fetch staging"
        staging.mkdir()
        for failure in ("copy", "flush", "unlink", "enospc", "short", "long",
                        "part-digest", "part-size", "asset-digest"):
            with self.subTest(failure=failure):
                result = self.transport("fetch", arguments=("--refresh-stale",),
                                        TMPDIR=str(staging), **self.reassembly_probe(failure))
                self.assertEqual(1, result.returncode, result.stdout + result.stderr)
                reason = ("part checksum or size mismatch" if failure.startswith("part-") else
                          "transferred asset digest mismatch" if failure == "asset-digest" else
                          "part copy size mismatch" if failure in ("short", "long") else
                          "injected reassembly " + failure)
                self.assertIn(reason, result.stdout)
                self.assertEqual(before, {str(p.relative_to(lake)): p.read_bytes() for p in lake.rglob("*") if p.is_file()})
                self.assertEqual([], list(staging.iterdir()))
                events = self.reassembly_events()
                self.assertFalse(any(event["operation"] == "extract" for event in events))
                removals = [event for event in events if event["operation"] == "unlink"]
                self.assertEqual(0 if "digest" in failure or failure == "part-size" else
                                 2 if failure == "unlink" else 1, len(removals))

    def test_candidate_multipart_restore_releases_private_parts(self):
        self.candidate_fixture()
        tag = self.candidate_tag()
        manifest = self.three_parts(self.remote / tag)
        shutil.rmtree(self.root / ".lake/build")
        result = self.candidate_transport("fetch", tag, **self.candidate_consumer(), **self.reassembly_probe())
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertEqual("locally-produced-olean", (self.root / ".lake/build/lib/lean/D5/A.olean").read_text())
        self.assertFalse((self.root / "build-runs").exists())
        self.assert_reassembly_released(manifest)

    def test_multipart_release_keeps_archive_hash_and_gzip_footer_validation(self):
        self.assertEqual(0, self.transport("publish").returncode)
        snapshot = next(self.remote.iterdir())
        packed = (snapshot / "lean-build.tgz").read_bytes()
        write(self.root / ".lake/build/keep.txt", "old build")
        write(self.root / ".lake/lean-report-seed-base.json", "old base")
        lake = self.root / ".lake"
        before = {str(p.relative_to(lake)): p.read_bytes() for p in lake.rglob("*") if p.is_file()}
        for failure in ("archive-hash", "truncated-gzip", "crc"):
            with self.subTest(failure=failure):
                damaged = packed[:-8] if failure == "truncated-gzip" else packed
                if failure == "crc":
                    damaged = packed[:-8] + bytes([packed[-8] ^ 1]) + packed[-7:]
                manifest = self.three_parts(snapshot, damaged)
                if failure == "archive-hash":
                    manifest["archive_sha256"] = "0" * 64
                    write(snapshot / "manifest.json", json.dumps(manifest))
                result = self.transport("fetch", arguments=("--refresh-stale",), **self.reassembly_probe())
                self.assertEqual(1, result.returncode, result.stdout + result.stderr)
                self.assertIn({"archive-hash": "archive checksum or size mismatch",
                               "truncated-gzip": "end-of-stream", "crc": "CRC check failed"}[failure], result.stdout)
                self.assertEqual(before, {str(p.relative_to(lake)): p.read_bytes() for p in lake.rglob("*") if p.is_file()})
                self.assertFalse(any(event["operation"] == "extract" for event in self.reassembly_events()))

    def local_assets_fixture(self, multipart=False):
        subprocess.run(["git", "-C", str(self.root), "branch", "-M", "dev"], check=True, capture_output=True)
        self.assertEqual(0, self.transport("publish").returncode)
        snapshot = next(self.remote.iterdir())
        manifest = json.loads((snapshot / "manifest.json").read_text())
        if multipart:
            manifest = self.three_parts(snapshot)
        local = self.root / "local assets ' ; `touch UNEXPECTED`"
        local.mkdir()
        for part in manifest["parts"]:
            (local / part["name"]).write_bytes((snapshot / part["name"]).read_bytes())
        arguments = ("--refresh-stale", "--approved-tag", snapshot.name,
                     "--approved-producer", self.producer_commit, "--local-assets", str(local))
        return snapshot, local, arguments

    def assert_manifest_only_downloaded(self, log):
        calls = [json.loads(line) for line in log.read_text().splitlines()]
        self.assertEqual("api", calls[0][0])
        self.assertFalse(any(call[:2] == ["release", "list"] for call in calls))
        downloads = [call for call in calls if call[:2] == ["release", "download"]]
        self.assertEqual(1, len(downloads))
        self.assertEqual(["manifest.json"], [downloads[0][i + 1] for i, arg in enumerate(downloads[0])
                                            if arg == "--pattern"])

    def local_clone_probe(self, failure=""):
        write(self.bin / "sitecustomize.py", '''
import ctypes, errno, json, os, sys
if os.environ["FAKE_CLONE_FAILURE"] == "platform":
    sys.platform = "unsupported-local-assets"
original_cdll = ctypes.CDLL
def cdll(*args, **kwargs):
    library = original_cdll(*args, **kwargs)
    native = getattr(library, "fclonefileat", None)
    if os.environ["FAKE_CLONE_FAILURE"] == "capability":
        library.fclonefileat = None
    elif native is not None:
        native.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.c_char_p, ctypes.c_uint]
        native.restype = ctypes.c_int
        def clone(source, directory, name, flags):
            if os.environ["FAKE_CLONE_FAILURE"] == "errno":
                ctypes.set_errno(errno.EXDEV)
                return -1
            result = native(source, directory, name, flags)
            if result == 0:
                target = os.open(name, os.O_RDWR, dir_fd=directory)
                try:
                    source_stat, target_stat = os.fstat(source), os.fstat(target)
                    before = os.read(source, source_stat.st_size)
                    os.write(target, b"private write")
                    os.lseek(source, 0, 0)
                    assert os.read(source, source_stat.st_size) == before, "shared source bytes"
                    os.lseek(target, 0, 0)
                    os.write(target, before)
                    os.ftruncate(target, len(before))
                    with open(os.environ["FAKE_CLONE_LOG"], "a") as log:
                        log.write(json.dumps(dict(name=os.fsdecode(name), source=source_stat.st_ino,
                            target=target_stat.st_ino, links=target_stat.st_nlink)) + "\\n")
                finally:
                    os.close(target)
            return result
        library.fclonefileat = clone
    return library
ctypes.CDLL = cdll
''')
        return dict(PYTHONPATH=str(self.bin), FAKE_CLONE_FAILURE=failure,
                    FAKE_CLONE_LOG=str(self.root / "clone-events"))

    @unittest.skipUnless(sys.platform == "darwin", "native clonefile requires macOS")
    def test_local_assets_native_private_stage_and_make_handoff(self):
        # Both the single-asset and assembled multipart paths use real native clones.
        previous = self.root
        self.root = previous / "checkout with spaces"
        self.root.mkdir()
        for child in previous.iterdir():
            if child != self.root:
                child.rename(self.root / child.name)
        self.remote, self.bin = self.root / "remote", self.root / "bin"
        self.publisher = self.root / "tools/scripts/worktree/lean-cache-publish.sh"
        for multipart in (False, True):
            with self.subTest(multipart=multipart):
                snapshot, local, arguments = self.local_assets_fixture(multipart)
                originals = {p.name: (p.read_bytes(), p.stat()) for p in local.iterdir()}
                write(self.root / ".lake/build/keep.txt", "old cache")
                log = self.root / "local-gh-calls"
                clone_probe = self.local_clone_probe()
                assembly_probe = self.reassembly_probe(append=True)
                environment = self.transport_environment(GITHUB_ACTIONS="false", FAKE_GH_LOG=str(log),
                    **{**clone_probe, **assembly_probe}, LEAN_CACHE_REPOSITORY=str(self.root),
                    LEAN_CACHE_APPROVED_TAG=snapshot.name, LEAN_CACHE_APPROVED_PRODUCER=self.producer_commit,
                    LEAN_CACHE_LOCAL_ASSETS=str(local))
                result = subprocess.run([shutil.which("make"), "-C", str(self.root),
                    "lean-cache-from-github-without-mathlib", "REFRESH_STALE=1"],
                    cwd=str(self.root.parent), env=environment, text=True, capture_output=True)
                self.assertEqual(0, result.returncode, result.stdout + result.stderr)
                self.assertIn('"status":"unpacked"', result.stdout)
                self.assertEqual("locally-produced-olean", (self.root / ".lake/build/lib/lean/D5/A.olean").read_text())
                self.assertFalse((self.root / ".lake/build/keep.txt").exists())
                self.assertFalse((self.root / "UNEXPECTED").exists())
                self.assert_manifest_only_downloaded(log)
                events = [json.loads(line) for line in (self.root / "clone-events").read_text().splitlines()]
                self.assertEqual(sorted(originals), sorted(event["name"] for event in events))
                for event in events:
                    self.assertNotEqual(event["source"], event["target"])
                    self.assertEqual(1, event["links"])
                for path in local.iterdir():
                    content, status = originals[path.name]
                    self.assertEqual(content, path.read_bytes())
                    self.assertEqual((status.st_ino, status.st_mtime_ns), (path.stat().st_ino, path.stat().st_mtime_ns))
                if multipart:
                    self.assert_reassembly_released(json.loads((snapshot / "manifest.json").read_text()))
                    self.assertTrue(all(event["stage"] != str(local) for event in self.reassembly_events()
                                        if event["operation"] == "unlink"))
                else:
                    self.assertFalse(any(event["operation"] == "unlink" for event in self.reassembly_events()))
                    self.assertEqual({"lean-build.tgz": (local / "lean-build.tgz").stat().st_size},
                        next(event["files"] for event in self.reassembly_events() if event["operation"] == "extract"))
                shutil.rmtree(snapshot)
                shutil.rmtree(local)
                log.unlink()
                (self.root / "clone-events").unlink()

    def test_local_assets_require_exact_production_refresh(self):
        log = self.root / "invalid-local-gh-calls"
        for extra in ((), ("--refresh-stale",), ("--approved-tag", "x", "--refresh-stale"),
                      ("--mode", "candidate"), ("--mode", "verification")):
            with self.subTest(extra=extra):
                result = self.transport("fetch", arguments=("--local-assets", str(self.root), *extra), FAKE_GH_LOG=str(log))
                self.assertEqual(1, result.returncode, result.stdout + result.stderr)
                self.assertFalse(log.exists())

    def test_local_assets_still_validate_fresh_remote_identity_and_inventory(self):
        snapshot, local, arguments = self.local_assets_fixture()
        original = (snapshot / "manifest.json").read_bytes()
        for damage in ("producer", "key", "inventory", "manifest-digest", "part-digest", "part-size", "remote"):
            with self.subTest(damage=damage):
                manifest = json.loads(original)
                environment = {}
                if damage == "producer": manifest["producer_commit_sha"] = "f" * 40
                elif damage == "key": manifest["cache_key"]["execution_sha256"] = "0" * 64
                elif damage == "inventory": manifest["parts"][0]["name"] = "unexpected"
                elif damage == "manifest-digest": environment["FAKE_MANIFEST_DIGEST"] = "sha256:" + "0" * 64
                elif damage.startswith("part-"):
                    environment["FAKE_PART_ASSET"] = json.dumps({"digest": "sha256:" + "0" * 64}
                        if damage == "part-digest" else {"size": 1})
                else: environment["FAKE_FAIL"] = "api"
                write(snapshot / "manifest.json", json.dumps(manifest))
                result = self.transport("fetch", arguments=arguments, **environment,
                                        **self.local_clone_probe("errno"))
                self.assertEqual(1, result.returncode, result.stdout + result.stderr)
                self.assertNotIn("local asset clonefile failed", result.stdout)
                self.assertNotIn("local assets require macOS", result.stdout)
                self.assertEqual("locally-produced-olean", (self.root / ".lake/build/lib/lean/D5/A.olean").read_text())
                self.assertFalse((self.root / "clone-events").exists())

    @unittest.skipUnless(sys.platform == "darwin", "native clonefile requires macOS")
    def test_local_assets_invalid_files_fail_without_remote_part_fallback(self):
        snapshot, local, arguments = self.local_assets_fixture(True)
        # The first part is already cloned when the second part fails.
        part = sorted(local.iterdir())[-1]
        original = part.read_bytes()
        staging = self.root / "private fetch staging"
        staging.mkdir()
        write(self.root / ".lake/build/keep.txt", "old cache")
        for damage in ("missing", "size", "hash", "symlink", "directory", "fifo", "source-symlink"):
            with self.subTest(damage=damage):
                log = self.root / "bad-local-gh-calls"
                part.unlink()
                if damage == "size": part.write_bytes(original[:-1])
                elif damage == "hash": part.write_bytes(bytes([original[0] ^ 1]) + original[1:])
                elif damage == "symlink": part.symlink_to(snapshot / part.name)
                elif damage == "directory": part.mkdir()
                elif damage == "fifo": os.mkfifo(part)
                elif damage == "source-symlink":
                    part.write_bytes(original)
                    local.rename(local.with_name("original assets"))
                    local.symlink_to(local.with_name("original assets"), target_is_directory=True)
                result = self.transport("fetch", arguments=arguments, FAKE_GH_LOG=str(log), TMPDIR=str(staging))
                self.assertEqual(1, result.returncode, result.stdout + result.stderr)
                self.assertIn('"status":"miss"', result.stdout)
                self.assertEqual("old cache", (self.root / ".lake/build/keep.txt").read_text())
                self.assertEqual({"build"}, {p.name for p in (self.root / ".lake").iterdir()})
                self.assertEqual([], list(staging.iterdir()))
                self.assert_manifest_only_downloaded(log)
                log.unlink()
                if damage == "source-symlink":
                    local.unlink()
                    local.with_name("original assets").rename(local)
                if part.is_dir(): part.rmdir()
                else: part.unlink(missing_ok=True)
                part.write_bytes(original)

    @unittest.skipUnless(sys.platform == "darwin", "native clonefile requires macOS")
    def test_local_assets_keep_archive_hash_gzip_and_tar_validation(self):
        snapshot, local, arguments = self.local_assets_fixture()
        archive = snapshot / "lean-build.tgz"
        original, manifest_bytes = archive.read_bytes(), (snapshot / "manifest.json").read_bytes()
        for damage, reason in (("archive-hash", "archive checksum or size mismatch"),
                               ("gzip", "end-of-stream"), ("tar", "archive contains an invalid cache member")):
            with self.subTest(damage=damage):
                packed = original
                if damage == "gzip": packed = packed[:-8]
                elif damage == "tar":
                    with tarfile.open(archive, "w:gz") as target:
                        member = tarfile.TarInfo("../outside")
                        member.type = tarfile.DIRTYPE
                        target.addfile(member)
                    packed = archive.read_bytes()
                archive.write_bytes(packed)
                (local / archive.name).write_bytes(packed)
                manifest = json.loads(manifest_bytes)
                manifest.update(archive_bytes=len(packed),
                    archive_sha256="0" * 64 if damage == "archive-hash" else digest(packed),
                    parts=[dict(name=archive.name, bytes=len(packed), sha256=digest(packed))])
                write(snapshot / "manifest.json", json.dumps(manifest))
                log = self.root / "archive-validation-gh-calls"
                result = self.transport("fetch", arguments=arguments, FAKE_GH_LOG=str(log))
                self.assertEqual(1, result.returncode, result.stdout + result.stderr)
                self.assertIn(reason, result.stdout)
                self.assert_manifest_only_downloaded(log)
                self.assertEqual(packed, (local / archive.name).read_bytes())
                self.assertEqual("locally-produced-olean", (self.root / ".lake/build/lib/lean/D5/A.olean").read_text())
                self.assertEqual({"build"}, {p.name for p in (self.root / ".lake").iterdir()})
                log.unlink()

    def test_local_assets_unsupported_platform_is_an_optional_miss(self):
        snapshot, local, arguments = self.local_assets_fixture()
        log = self.root / "unsupported-gh-calls"
        result = self.transport("fetch", arguments=arguments, FAKE_GH_LOG=str(log),
                                **self.local_clone_probe("platform"))
        self.assertEqual(1, result.returncode, result.stdout + result.stderr)
        self.assertIn("local assets require macOS native clonefile", result.stdout)
        self.assert_manifest_only_downloaded(log)
        self.assertFalse((self.root / "clone-events").exists())

    def test_local_assets_optional_clone_library_does_not_affect_remote_fetch(self):
        snapshot, local, arguments = self.local_assets_fixture()
        shutil.rmtree(self.root / ".lake/build")
        write(self.bin / "sitecustomize.py", 'import sys\nsys.modules["ctypes"] = None\n')
        log = self.root / "optional-library-gh-calls"
        environment = dict(PYTHONPATH=str(self.bin), FAKE_GH_LOG=str(log))
        restored = self.transport("fetch", **environment)
        self.assertEqual(0, restored.returncode, restored.stdout + restored.stderr)
        self.assertIn('"status":"unpacked"', restored.stdout)
        calls = [json.loads(line) for line in log.read_text().splitlines()]
        self.assertTrue(any(call[:2] == ["release", "download"] and call[-1] == "lean-build.tgz" for call in calls))
        log.unlink()
        lake = self.root / ".lake"
        before = {str(p.relative_to(lake)): p.read_bytes() for p in lake.rglob("*") if p.is_file()}
        failed = self.transport("fetch", arguments=arguments, **environment)
        self.assertEqual(1, failed.returncode, failed.stdout + failed.stderr)
        self.assertIn('"status":"miss"', failed.stdout)
        self.assertNotIn("Traceback", failed.stderr)
        self.assert_manifest_only_downloaded(log)
        self.assertEqual(before, {str(p.relative_to(lake)): p.read_bytes() for p in lake.rglob("*") if p.is_file()})

    @unittest.skipUnless(sys.platform == "darwin", "native clonefile requires macOS")
    def test_local_assets_clone_failure_and_install_rollback_preserve_source_and_old_cache(self):
        snapshot, local, arguments = self.local_assets_fixture(True)
        originals = {p.name: p.read_bytes() for p in local.iterdir()}
        write(self.root / ".lake/build/keep.txt", "old cache")
        base = self.root / ".lake/build/.release-refreshed-at"
        write(base, "old marker")
        for failure in ("capability", "errno", "install"):
            with self.subTest(failure=failure):
                log = self.root / "failed-local-gh-calls"
                probe = self.installation_probe("install") if failure == "install" else self.local_clone_probe(failure)
                result = self.transport("fetch", arguments=arguments, FAKE_GH_LOG=str(log), **probe)
                self.assertEqual(1, result.returncode, result.stdout + result.stderr)
                reason = {"capability": "native fclonefileat is unavailable", "errno": "local asset clonefile failed",
                          "install": "injected rename failure"}[failure]
                self.assertIn(reason, result.stdout)
                self.assert_manifest_only_downloaded(log)
                self.assertEqual("old cache", (self.root / ".lake/build/keep.txt").read_text())
                self.assertEqual("old marker", base.read_text())
                self.assertEqual({"build"}, {p.name for p in (self.root / ".lake").iterdir()})
                self.assertEqual(originals, {p.name: p.read_bytes() for p in local.iterdir()})
                log.unlink()

    def test_local_make_publication_and_restore_use_current_protected_head(self):
        # Local make callers publish clean protected-dev snapshots with UTC suffixes.
        before = datetime.datetime.now(datetime.timezone.utc)
        result = subprocess.run([shutil.which("make"), "-C", str(self.root), "lean-cache-to-github-without-mathlib"],
            text=True, capture_output=True, env=self.transport_environment(**self.local_environment(),
                FAKE_GH_LOG=str(self.root / "local-gh-calls")))
        after = datetime.datetime.now(datetime.timezone.utc)
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertIn('"status":"published"', result.stdout)
        snapshot = next(self.remote.iterdir())
        prefix = json.loads(self.transport("address").stdout)["release_prefix"]
        suffix = snapshot.name.removeprefix(prefix)
        self.assertRegex(suffix, r"^local-" + self.producer_commit[:12] + r"-[0-9]{8}T[0-9]{12}Z$")
        stamp = suffix.split("-")[-1]
        published_at = datetime.datetime.strptime(stamp, "%Y%m%dT%H%M%S%fZ").replace(tzinfo=datetime.timezone.utc)
        self.assertLessEqual(before, published_at)
        self.assertLessEqual(published_at, after)
        manifest = json.loads((snapshot / "manifest.json").read_text())
        self.assertEqual(self.producer_commit, manifest["producer_commit_sha"])
        self.assertEqual(suffix, manifest["publication_id"])
        self.assertNotIn("workflow_run_id", manifest)
        calls = [json.loads(line) for line in (self.root / "local-gh-calls").read_text().splitlines()]
        self.assertFalse(any(call[0] == "api" and "/actions/" in call[1] for call in calls))
        second = self.transport("publish", **self.local_environment())
        self.assertIn('"status":"published"', second.stdout)
        self.assertEqual(2, len(list(self.remote.iterdir())))
        shutil.rmtree(self.root / ".lake/build")
        restored = self.transport("fetch", **self.local_environment())
        self.assertEqual(0, restored.returncode, restored.stdout + restored.stderr)
        self.assertEqual("locally-produced-olean", (self.root / ".lake/build/lib/lean/D5/A.olean").read_text())

    def test_local_publication_rejects_dirty_unprotected_and_non_dev_content(self):
        # Publication requires clean content from the protected dev history.
        for change in ("tracked", "untracked", "unprotected", "off-dev"):
            with self.subTest(change=change):
                environment = self.local_environment()
                if change == "tracked":
                    write(self.root / "D5/A.lean", "def a := 2\n")
                elif change == "untracked":
                    write(self.root / "untracked-input.lean", "def missing := 1\n")
                elif change == "unprotected":
                    environment["FAKE_DEV_BRANCH"] = json.dumps(dict(name="dev", protected=False, commit=dict(sha=self.producer_commit)))
                else:
                    environment["FAKE_DEV_COMPARE"] = json.dumps(dict(status="diverged", merge_base_commit=dict(sha="f" * 40)))
                result = self.transport("publish", **environment)
                self.assertNotEqual(0, result.returncode, result.stdout + result.stderr)
                self.assertIn('"status":"failed"', result.stdout)
                self.assertEqual([], list(self.remote.iterdir()))
                write(self.root / "D5/A.lean", "def a := 1\n")
                (self.root / "untracked-input.lean").unlink(missing_ok=True)

    def test_local_publication_requires_complete_strict_current_report(self):
        # Publication requires a complete canonical bundle and current sealed inputs.
        report = self.root / ".lake/build/stratalint/raw-lean-report.json"
        originals = {path: path.read_bytes() for path in report.parent.iterdir()}
        for damage in ("missing", "empty-modules", "unknown-field", "noncanonical", "materials", "receipt", "stale"):
            with self.subTest(damage=damage):
                for path, content in originals.items(): path.write_bytes(content)
                environment = self.local_environment(FAKE_REPORT_PRESERVE="1")
                if damage == "missing": report.unlink()
                elif damage in ("empty-modules", "unknown-field", "noncanonical"):
                    data = json.loads(report.read_text())
                    if damage == "empty-modules": data["modules"] = []
                    if damage == "unknown-field": data["unknown"] = True
                    report.write_text((" " if damage == "noncanonical" else "") + json.dumps(data) + "\n")
                    # Keep the integrity seal consistent so the strict row reader, not only the hash guard, rejects it.
                    current_sha = digest(report.read_bytes())
                    report.with_name(report.name + ".sha256").write_text(current_sha + "  " + report.name + "\n")
                    provenance_path = report.with_name(report.name + ".provenance.json")
                    provenance = json.loads(provenance_path.read_text())
                    old_sha = provenance["report_sha256"]
                    provenance["report_sha256"] = current_sha
                    provenance_path.write_text(json.dumps(provenance) + "\n")
                    attestation = report.with_name(report.name + ".input.attestation")
                    attestation.write_text(attestation.read_text().replace(old_sha, current_sha))
                    receipt_path = report.with_name(report.name + ".reuse.json")
                    seal = json.loads(receipt_path.read_text())
                    seal["bundle"] = {suffix: digest(report.with_name(report.name + suffix).read_bytes()) for suffix in seal["bundle"]}
                    receipt_path.write_text(json.dumps(seal) + "\n")
                elif damage == "materials":
                    report.with_name(report.name + ".materials.zip").write_bytes(b"not-a-zip")
                elif damage == "receipt":
                    report.with_name(report.name + ".reuse.json").unlink()
                else:
                    write(self.root / "D5/A.lean", "def a := 2\n")
                    self.commit_fixture()
                result = self.transport("publish", **environment)
                self.assertNotEqual(0, result.returncode, result.stdout + result.stderr)
                self.assertIn('"status":"failed"', result.stdout)
                self.assertEqual([], list(self.remote.iterdir()))

    def test_ci_fetch_never_reads_release_even_when_actions_seed_is_absent(self):
        # CI's ensure fallback must skip Release independently of workflow steps.
        self.assertIn('"status":"published"', self.transport("publish").stdout)
        shutil.rmtree(self.root / ".lake/build")
        log = self.root / "ci-gh-calls"
        result = self.transport("fetch", GITHUB_ACTIONS="true", FAKE_GH_LOG=str(log))
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertIn('"status":"skipped"', result.stdout)
        self.assertFalse(log.exists())
        self.assertFalse((self.root / ".lake/build").exists())

    def test_manifest_full_key_mismatch_stops_before_archive_download(self):
        # Full digest validation guards the shortened name before archive transfer.
        self.assertIn('"status":"published"', self.transport("publish").stdout)
        snapshot = next(self.remote.iterdir())
        manifest = json.loads((snapshot / "manifest.json").read_text())
        manifest["cache_key"]["execution_sha256"] = manifest["cache_key"]["execution_sha256"][:12] + "0" * 52
        write(snapshot / "manifest.json", json.dumps(manifest))
        shutil.rmtree(self.root / ".lake/build")
        log = self.root / "manifest-key-calls"
        result = self.transport("fetch", FAKE_GH_LOG=str(log))
        self.assertEqual(1, result.returncode, result.stdout + result.stderr)
        downloads = [json.loads(line) for line in log.read_text().splitlines() if json.loads(line)[:2] == ["release", "download"]]
        self.assertEqual(1, len(downloads))
        self.assertEqual("manifest.json", downloads[0][-1])
        self.assertFalse((self.root / ".lake/build").exists())

    def test_release_key_derives_format_and_explicit_execution_only(self):
        # Names project only the declared format and explicit execution inputs.
        address = json.loads(self.transport("address").stdout)
        system, machine = platform.system().lower(), platform.machine().lower()
        machine = {"aarch64": "arm64", "x86_64": "x64", "amd64": "x64"}.get(machine, machine)
        host = system + "-" + machine
        family = "darwin-arm64+linux-arm64" if host in ("darwin-arm64", "linux-arm64") else host
        execution = dict(toolchain=(self.root / "lean-toolchain").read_text().strip(),
            tools=["lake", "lean"], platform=family,
            environment={name: "" for name in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "ELAN_TOOLCHAIN", "LEAN_OPTS")})
        expected = hashlib.sha256(json.dumps(execution, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
        self.assertEqual(dict(report_format="stratalint-raw-lean-report-v3", execution_sha256=expected), address["cache_key"])
        self.assertEqual(f"lean-cache-v2-{REV}-{host}-report-stratalint-raw-lean-report-v3-env-{expected[:12]}-",
                         address["release_prefix"])
        write(self.root / "D5/A.lean", "def a := 333\n")
        self.assertEqual(address, json.loads(self.transport("address").stdout))
        owner = self.publisher.with_name("lean_cache_release.py")
        write(owner, owner.read_text() + "\n# implementation-only variation\n")
        self.assertEqual(address, json.loads(self.transport("address").stdout))
        write(self.root / "lean-toolchain", "leanprover/lean4:v4.33.0\n\n")
        self.assertEqual(address, json.loads(self.transport("address").stdout))
        write(self.root / "lean-toolchain", "leanprover/lean4:v4.34.0\n")
        self.assertNotEqual(address["cache_key"], json.loads(self.transport("address").stdout)["cache_key"])
        changed = self.transport("address", ELAN_TOOLCHAIN="other-toolchain")
        self.assertNotEqual(expected, json.loads(changed.stdout)["cache_key"]["execution_sha256"])
        selection = self.root / "tools/scripts/report/lean-report-selection.py"
        write(selection, selection.read_text().replace("stratalint-raw-lean-report-v3", "stratalint-raw-lean-report-test"))
        changed = json.loads(self.transport("address").stdout)
        self.assertEqual("stratalint-raw-lean-report-test", changed["cache_key"]["report_format"])
        self.assertIn("-report-stratalint-raw-lean-report-test-env-", changed["release_prefix"])

    def test_mismatched_key_is_never_selected_or_downloaded(self):
        # Selection filters incompatible names before any snapshot request.
        published = self.transport("publish")
        self.assertIn('"status":"published"', published.stdout)
        original = next(self.remote.iterdir()).name
        shutil.rmtree(self.root / ".lake/build")
        address = json.loads(self.transport("address").stdout)
        wrong = [original.replace(address["cache_key"]["report_format"], "wrong-format"),
                 original.replace(address["cache_key"]["execution_sha256"][:12], "0" * 12),
                 f"lean-cache-v2-{REV}-linux-arm64-123-1"]
        releases = [dict(tagName=tag, createdAt=f"9{index}", isDraft=False) for index, tag in enumerate(wrong)]
        log = self.root / "key-gh-calls"
        missed = self.transport("fetch", FAKE_LIST_JSON=json.dumps(releases), FAKE_GH_LOG=str(log))
        self.assertEqual(1, missed.returncode, missed.stdout + missed.stderr)
        self.assertEqual(["list"], [json.loads(line)[1] for line in log.read_text().splitlines()])
        releases.append(dict(tagName=original, createdAt="1", isDraft=False))
        log.unlink()
        restored = self.transport("fetch", FAKE_LIST_JSON=json.dumps(releases), FAKE_GH_LOG=str(log))
        self.assertEqual(0, restored.returncode, restored.stdout + restored.stderr)
        calls = [json.loads(line) for line in log.read_text().splitlines()]
        self.assertTrue(all(tag not in call for tag in wrong for call in calls[1:]))
        self.assertIn(original, restored.stdout)

    def test_publication_requires_current_report_before_transport(self):
        result = self.transport("publish")
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertEqual(["lean-report LEAN_REPORT_CACHE_MISS_POLICY=reuse-or-build LEAN_REPORT=.lake/build/stratalint/raw-lean-report.json"], (self.root / "build-runs").read_text().splitlines())

    def test_fetch_cannot_widen_partition_compatibility(self):
        self.assertEqual(0, self.transport("publish").returncode)
        shutil.rmtree(self.root / ".lake/build")
        self.manifest["packages"][0]["rev"] = OTHER
        self.save_manifest()
        missed = self.transport("fetch")
        self.assertEqual(1, missed.returncode, missed.stdout + missed.stderr)
        self.assertIn('"status":"miss"', missed.stdout)
        self.assertFalse((self.root / ".lake/build").exists())
        self.manifest["packages"][0]["rev"] = REV
        self.save_manifest()
        restored = self.transport("fetch")
        self.assertEqual(0, restored.returncode, restored.stdout + restored.stderr)
        self.assertEqual("locally-produced-olean", (self.root / ".lake/build/lib/lean/D5/A.olean").read_text())


    def test_malformed_cleanup_metadata_cannot_fail_or_repeat_the_build(self):
        calls = self.root / "build-calls"
        write(self.bin / "make", '#!/bin/sh\necho build >> "$FAKE_BUILD_CALLS"\nexit 0\n')
        malformed = [("FAKE_LIST_JSON", '["invalid"]'),
                     ("FAKE_LIST_JSON", '[{"tagName":12,"createdAt":"today","isDraft":false}]'),
                     ("FAKE_FAIL", "list")]
        for index, (field, value) in enumerate(malformed):
            result = self.transport("publish", str(601 + index), FAKE_BUILD_CALLS=str(calls), **{field: value})
            self.assertEqual(0, result.returncode, result.stdout + result.stderr)
            self.assertIn('"status":"published"', result.stdout)
            self.assertIn('"prune_error":', result.stdout)
        self.assertEqual(["build"] * len(malformed), calls.read_text().splitlines())

    def test_publication_requires_a_current_inspector_report(self):
        write(self.bin / "make", '#!/bin/sh\nexit 0\n')
        report = self.root / ".lake/build/stratalint/raw-lean-report.json"
        report.unlink()
        missing = self.transport("publish")
        self.assertEqual(2, missing.returncode, missing.stdout + missing.stderr)
        self.assertIn('"status":"failed"', missing.stdout.replace(" ", ""))
        self.assertIn("missing bundle member: raw-lean-report.json", missing.stdout)
        self.assertEqual([], list(self.remote.iterdir()))

        write(self.bin / "make", '#!/bin/sh\nmkdir -p .lake/build/stratalint\nprintf \'%s\\n\' \'{"modules":[],"schema":"wrong"}\' > .lake/build/stratalint/raw-lean-report.json\nexit 0\n')
        malformed = self.transport("publish")
        self.assertEqual(2, malformed.returncode, malformed.stdout + malformed.stderr)
        self.assertIn('"status":"failed"', malformed.stdout.replace(" ", ""))
        self.assertIn("reuse receipt bundle mismatch", malformed.stdout)
        self.assertEqual([], list(self.remote.iterdir()))

    def host_platform(self, system, machine):
        # Seed compatibility follows the host that runs the transport.
        write(self.bin / "sitecustomize.py", "import os, platform\n"
              "platform.system = lambda: os.environ['FAKE_PLATFORM_SYSTEM']\n"
              "platform.machine = lambda: os.environ['FAKE_PLATFORM_MACHINE']\n")
        return {"PYTHONPATH": str(self.bin), "FAKE_PLATFORM_SYSTEM": system, "FAKE_PLATFORM_MACHINE": machine}

    def test_arm64_seeds_are_shared_between_linux_and_macos_only(self):
        seed = "locally-produced-olean"
        for publisher, fetcher, run in [(("Linux", "aarch64"), ("Darwin", "arm64"), "123"),
                                        (("Darwin", "arm64"), ("Linux", "aarch64"), "124")]:
            with self.subTest(publisher=publisher, fetcher=fetcher):
                shutil.rmtree(self.remote)
                self.remote.mkdir()
                write(self.root / ".lake/build/lib/lean/D5/A.olean", seed)
                published = self.transport("publish", run, **self.host_platform(*publisher))
                self.assertEqual(0, published.returncode, published.stdout + published.stderr)
                self.assertIn('"status":"published"', published.stdout)
                tag = next(self.remote.iterdir()).name
                # Publication keeps its own platform partition and retention.
                own = "linux-arm64" if publisher[0] == "Linux" else "darwin-arm64"
                self.assertEqual(json.loads(self.transport("address", **self.host_platform(*publisher)).stdout)["release_prefix"] + f"ci-{run}-1", tag)
                shutil.rmtree(self.root / ".lake/build")
                for other in [("Darwin", "x86_64"), ("Linux", "x86_64")]:
                    missed = self.transport("fetch", **self.host_platform(*other))
                    self.assertEqual(1, missed.returncode, missed.stdout + missed.stderr)
                    self.assertIn('"status":"miss"', missed.stdout)
                    self.assertFalse((self.root / ".lake/build").exists())
                restored = self.transport("fetch", **self.host_platform(*fetcher))
                self.assertEqual(0, restored.returncode, restored.stdout + restored.stderr)
                self.assertIn(f'"resolved":"{tag}"', restored.stdout)
                self.assertIn(f'"partition":"{REV}/{own}"', restored.stdout)
                self.assertEqual(seed, (self.root / ".lake/build/lib/lean/D5/A.olean").read_text())


def _all_test_cases():
    return unittest.defaultTestLoader.loadTestsFromTestCase(TransportTests)


if __name__ == "__main__":
    if len(sys.argv) == 2 and sys.argv[1] == "--list":
        for case in _all_test_cases():
            print(case.id().rsplit(".", 1)[-1])
        raise SystemExit(0)
    unittest.main()
