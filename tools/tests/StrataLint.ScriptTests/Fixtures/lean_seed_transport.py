"""Release seed transport cases using a private local GitHub fake."""
import concurrent.futures
import json
import os
import pathlib
import random
import shutil
import subprocess
import tarfile

from lean_seed_support import OTHER, PUBLISH, REV, PartitionFixture, digest, write


class ReleaseTransportCases(PartitionFixture):
    def setUp(self):
        super().setUp()
        self.remote = self.root / "remote"
        self.bin = self.root / "bin"
        self.bin.mkdir()
        self.remote.mkdir()
        write(self.root / ".lake/build/lib/lean/D5/A.olean", "locally-produced-olean")
        write(self.root / ".lake/build/stratalint/raw-lean-report.json",
              '{"modules":[],"schema":"stratalint-raw-lean-report-v2"}\n')
        write(self.bin / "make", '''#!/bin/sh
printf "%s\\n" "$*" >> "$FAKE_BUILD_LOG"
if [ "$*" = "lean-report" ] && [ "${FAKE_BUILD_EXIT:-0}" = "0" ]; then
    mkdir -p .lake/build/stratalint
    printf '%s\\n' '{"modules":[],"schema":"stratalint-raw-lean-report-v2"}' > .lake/build/stratalint/raw-lean-report.json
fi
exit "${FAKE_BUILD_EXIT:-0}"
''')
        write(self.bin / "gh", FAKE_GH)
        helper_dir = self.root / "tools/scripts/worktree"
        helper_dir.mkdir(parents=True, exist_ok=True)
        # Exercise the production shell entry point with its declared transport
        # dependencies in the fixture repository.
        for name in ("lean-cache-publish.sh", "cache_material.py", "lean_cache.py", "lean_cache_release.py"):
            shutil.copy2(PUBLISH.with_name(name), helper_dir / name)
        self.publisher = helper_dir / "lean-cache-publish.sh"
        self.publisher.chmod(0o755)
        for path in self.bin.iterdir():
            path.chmod(0o755)

    def transport_environment(self, run="123", **extra):
        return {**os.environ, "PATH": str(self.bin) + os.pathsep + os.environ["PATH"],
            "HOME": str(self.root), "FAKE_BUILD_LOG": str(self.root / "build-runs"),
            "FAKE_REMOTE": str(self.remote), "GITHUB_SHA": "d" * 40, "GITHUB_RUN_ID": run,
            "GITHUB_RUN_ATTEMPT": "1", "GITHUB_EVENT_NAME": "schedule", "GITHUB_REF": "refs/heads/dev",
            "STRATALINT_CHECK_SUCCEEDED": "true", "STRATALINT_ACTIONS_CACHE_SEEDED": "", **extra}

    def transport(self, verb, run="123", arguments=(), **extra):
        return subprocess.run(["bash", str(self.publisher), verb, "--repository", str(self.root), *arguments],
                              text=True, capture_output=True, env=self.transport_environment(run, **extra))

    def fetch_then_build(self, **extra):
        # Exercise the optional-fetch caller protocol under errexit. Workflow
        # execution itself is verified by a real integration run, not YAML tests.
        return subprocess.run(["bash", "-euo", "pipefail", "-c", '''
if ! "$1" fetch --allow-seed --repository "$2"; then
    printf '%s\\n' 'Release seed unavailable; continuing with the normal Lean build.'
fi
make -C "$2" lean
''', "optional-fetch", str(self.publisher), str(self.root)], text=True, capture_output=True,
            env=self.transport_environment(**extra))

    def deadline_probe(self, seconds, step=0):
        # Keep subprocess's own wait clock real. Only the operation's monotonic
        # clock advances at completed gh calls, independently of machine speed.
        write(self.bin / "sitecustomize.py", '''
import json, os, pathlib, subprocess, time
original = subprocess.run
clock = 0
time.monotonic = lambda: clock
def run(args, *rest, **kwargs):
    global clock
    if args[0] != "gh": return original(args, *rest, **kwargs)
    with (pathlib.Path(os.environ["FAKE_REMOTE"]).parent / "gh-budgets").open("a") as log:
        log.write(json.dumps({"args": args[1:], "timeout": kwargs.get("timeout")}) + "\\n")
    # Infrastructure hang guard for the pre-fix unbounded call. Whether the
    # production owner supplied a timeout, not elapsed time, decides the test.
    kwargs.setdefault("timeout", 1)
    try: return original(args, *rest, **kwargs)
    finally: clock += int(os.environ["FAKE_CLOCK_STEP"])
subprocess.run = run
''')
        (self.root / "gh-budgets").unlink(missing_ok=True)
        return {"PYTHONPATH": str(self.bin), "FAKE_CLOCK_STEP": str(step),
                "STRATALINT_LEAN_CACHE_RELEASE_TIMEOUT_SECONDS": str(seconds)}

    def gh_budgets(self):
        return [json.loads(line) for line in (self.root / "gh-budgets").read_text().splitlines()]

    def installation_probe(self, failure=""):
        # A runner can hold one unpacked build but not a second whole-tree copy.
        # Track file identities and inject filesystem errors in the real restorer.
        write(self.bin / "sitecustomize.py", '''
import errno, json, os, pathlib, shutil, tarfile
def record(**event):
    with pathlib.Path(os.environ["FAKE_INSTALL_LOG"]).open("a") as log:
        log.write(json.dumps(event) + "\\n")
def copytree(source, target, *args, **kwargs):
    record(operation="copytree", source=str(source), target=str(target))
    raise OSError(errno.ENOSPC, "no space for a duplicate unpacked tree")
original_extract, original_rename = tarfile.TarFile.extractall, pathlib.Path.rename
def extract(archive, path, *args, **kwargs):
    record(operation="extract", path=str(path))
    result = original_extract(archive, path, *args, **kwargs)
    for member in archive.getmembers():
        if member.isfile():
            status = (pathlib.Path(path) / member.name).stat()
            record(operation="material", name=member.name, device=status.st_dev, inode=status.st_ino)
    if os.environ["FAKE_INSTALL_FAILURE"] == "extract":
        raise OSError(errno.ENOSPC, "injected extraction failure")
    return result
def rename(source, target):
    record(operation="rename", source=str(source), target=str(target))
    if os.environ["FAKE_INSTALL_FAILURE"] == "rename":
        raise OSError(errno.EIO, "injected rename failure")
    return original_rename(source, target)
shutil.copytree, tarfile.TarFile.extractall, pathlib.Path.rename = copytree, extract, rename
''')
        (self.root / "install-events").unlink(missing_ok=True)
        return {"PYTHONPATH": str(self.bin), "FAKE_INSTALL_LOG": str(self.root / "install-events"),
                "FAKE_INSTALL_FAILURE": failure}

    def installation_events(self):
        return [json.loads(line) for line in (self.root / "install-events").read_text().splitlines()]

    def test_restore_installs_each_extracted_file_once_on_the_target_filesystem(self):
        write(self.root / ".lake/build/lean-inspector/report.zip", "report material")
        self.assertEqual(0, self.transport("publish").returncode)
        shutil.rmtree(self.root / ".lake")
        result = self.transport("fetch", **self.installation_probe())
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertIn('"status":"unpacked"', result.stdout)
        events = self.installation_events()
        self.assertFalse(any(event["operation"] == "copytree" for event in events))
        extracted = next(event for event in events if event["operation"] == "extract")
        self.assertEqual((self.root / ".lake").resolve(), pathlib.Path(extracted["path"]).parent.resolve())
        materials = [event for event in events if event["operation"] == "material"]
        self.assertEqual(3, len(materials))
        for material in materials:
            status = (self.root / ".lake" / material["name"]).stat()
            self.assertEqual((material["device"], material["inode"]), (status.st_dev, status.st_ino))
        self.assertEqual({"build"}, {path.name for path in (self.root / ".lake").iterdir()})

    def test_restore_cleans_its_staging_on_extraction_and_installation_failure(self):
        self.assertEqual(0, self.transport("publish").returncode)
        shutil.rmtree(self.root / ".lake/build")
        write(self.root / ".lake/keep.txt", "existing private material")
        for failure, reason in (("extract", "injected extraction failure"), ("rename", "injected rename failure")):
            with self.subTest(failure=failure):
                result = self.transport("fetch", **self.installation_probe(failure))
                self.assertEqual(1, result.returncode, result.stdout + result.stderr)
                self.assertIn(reason, result.stdout)
                self.assertEqual(["keep.txt"], [path.name for path in (self.root / ".lake").iterdir()])
                self.assertEqual("existing private material", (self.root / ".lake/keep.txt").read_text())

    def test_restore_preserves_nonempty_file_and_symlink_targets(self):
        self.assertEqual(0, self.transport("publish").returncode)
        build = self.root / ".lake/build"
        shutil.rmtree(build)
        write(self.root / "private-build/keep.txt", "private material")
        for kind in ("directory", "file", "symlink"):
            with self.subTest(kind=kind):
                if kind == "directory":
                    write(build / "keep.txt", "private material")
                elif kind == "file":
                    write(build, "private material")
                else:
                    build.symlink_to(self.root / "private-build", target_is_directory=True)
                try:
                    result = self.transport("fetch", **self.installation_probe())
                    self.assertEqual(0, result.returncode, result.stdout + result.stderr)
                    self.assertIn('"status":"skipped"', result.stdout)
                    self.assertEqual(kind == "symlink", build.is_symlink())
                    self.assertEqual("private material", (build if kind == "file" else build / "keep.txt").read_text())
                    self.assertEqual(["build"], [path.name for path in build.parent.iterdir()])
                finally:
                    if kind == "directory": shutil.rmtree(build)
                    else: build.unlink()

    def test_restore_rejects_shared_lake_without_writing_to_its_target(self):
        self.assertEqual(0, self.transport("publish").returncode)
        lake, shared = self.root / ".lake", self.root / "shared-lake"
        lake.rename(shared)
        lake.symlink_to(shared, target_is_directory=True)
        result = self.transport("fetch", **self.installation_probe())
        self.assertEqual(1, result.returncode, result.stdout + result.stderr)
        self.assertIn("shared cache target is forbidden", result.stdout)
        self.assertFalse((self.root / "install-events").exists(), "shared target reached extraction")
        self.assertEqual(["build"], [path.name for path in shared.iterdir()])
        self.assertEqual("locally-produced-olean", (shared / "build/lib/lean/D5/A.olean").read_text())

    def test_restore_member_rejection_and_missing_build_leave_no_staging(self):
        self.assertEqual(0, self.transport("publish").returncode)
        shutil.rmtree(self.root / ".lake/build")
        snapshot = next(self.remote.iterdir())
        for name, kind in (("../outside", tarfile.DIRTYPE), ("/outside", tarfile.DIRTYPE),
                           ("outside", tarfile.DIRTYPE), ("build/link", tarfile.SYMTYPE),
                           ("build/link", tarfile.LNKTYPE), ("report-cache", tarfile.DIRTYPE)):
            with self.subTest(name=name, kind=kind):
                with tarfile.open(snapshot / "lean-build.tgz", "w:gz") as archive:
                    member = tarfile.TarInfo(name)
                    member.type, member.linkname = kind, "outside" if kind in (tarfile.SYMTYPE, tarfile.LNKTYPE) else ""
                    archive.addfile(member)
                packed = (snapshot / "lean-build.tgz").read_bytes()
                manifest = json.loads((snapshot / "manifest.json").read_text())
                manifest.update(archive_sha256=digest(packed), archive_bytes=len(packed),
                    parts=[{"name": "lean-build.tgz", "sha256": digest(packed), "bytes": len(packed)}])
                write(snapshot / "manifest.json", json.dumps(manifest))
                result = self.transport("fetch")
                self.assertEqual(1, result.returncode, result.stdout + result.stderr)
                self.assertIn("invalid cache member", result.stdout)
                self.assertEqual([], list((self.root / ".lake").iterdir()))

    def preparation_deadline_probe(self, phase):
        # Small incompressible material reaches archive hashing and multipart
        # splitting without allocating a production-sized Release asset.
        (self.root / ".lake/build/lib/lean/D5/A.olean").write_bytes(random.Random(31).randbytes(3 * 1024 * 1024))
        owner = self.publisher.with_name("lean_cache_release.py")
        owner.write_text(owner.read_text().replace("CHUNK_BYTES = 1610612736", "CHUNK_BYTES = 2097152"))
        environment = self.deadline_probe(1)
        with (self.bin / "sitecustomize.py").open("a") as fixture:
            fixture.write('''
import tarfile
phase = os.environ["FAKE_PREPARATION_PHASE"]
archive_opens = 0
original_open, original_copy = pathlib.Path.open, tarfile.copyfileobj
class TimedReader:
    def __init__(self, source): self.source = source
    def __getattr__(self, name): return getattr(self.source, name)
    def __enter__(self): return self
    def __exit__(self, *args): return self.source.__exit__(*args)
    def read(self, size=-1):
        global clock
        block = self.source.read(size)
        if block:
            with original_open(pathlib.Path(os.environ["FAKE_REMOTE"]).parent / "preparation-reads", "a") as log:
                log.write(str(len(block)) + "\\n")
            clock = 2
        return block
def open_path(path, mode="r", *args, **kwargs):
    global archive_opens
    source = original_open(path, mode, *args, **kwargs)
    if mode == "rb" and path.name == "lean-build.tgz":
        archive_opens += 1
        if (phase, archive_opens) in (("hash", 1), ("split", 2)): return TimedReader(source)
    if mode == "rb" and path.name == "lean-build.tgz.part-00" and phase == "part-hash":
        return TimedReader(source)
    return source
def copy(source, target, *args, **kwargs):
    if phase == "archive" and str(getattr(source, "name", "")).endswith("A.olean"):
        source = TimedReader(source)
    return original_copy(source, target, *args, **kwargs)
pathlib.Path.open, tarfile.copyfileobj = open_path, copy
''')
        (self.root / "preparation-reads").unlink(missing_ok=True)
        return {**environment, "FAKE_PREPARATION_PHASE": phase}

    def assert_preparation_stopped(self, result, status):
        self.assertEqual(status, result.returncode, result.stdout + result.stderr)
        self.assertIn('"status":"failed"', result.stdout)
        self.assertIn("deadline exhausted", result.stdout)
        consumed = sum(map(int, (self.root / "preparation-reads").read_text().splitlines()))
        self.assertGreater(consumed, 0)
        self.assertLessEqual(consumed, 1024 * 1024, "local preparation continued reading after its deadline")
        self.assertEqual([], list(self.remote.iterdir()))

    def test_publication_deadline_stops_local_archive_hash_and_split_work(self):
        for phase in ("archive", "hash", "split", "part-hash"):
            with self.subTest(phase=phase):
                self.assert_preparation_stopped(self.transport("publish", **self.preparation_deadline_probe(phase)), 0)

    def test_hanging_direct_fetch_is_bounded_and_fallback_preserves_build_exit(self):
        self.assertEqual(0, self.transport("publish").returncode)
        shutil.rmtree(self.root / ".lake/build")
        for operation in ("list", "api", "download"):
            for build_exit in (0, 19):
                with self.subTest(operation=operation, build_exit=build_exit):
                    result = self.fetch_then_build(**self.deadline_probe(1),
                        FAKE_HANG=operation, FAKE_BUILD_EXIT=str(build_exit))
                    self.assertEqual(build_exit, result.returncode, result.stdout + result.stderr)
                    self.assertIn('"status":"miss"', result.stdout)
                    self.assertIn("timed out", result.stdout)
                    self.assertEqual([1] * len(self.gh_budgets()),
                                     [call["timeout"] for call in self.gh_budgets()])
                    self.assertFalse((self.root / ".lake/build").exists())
        self.assertEqual(["lean-report"] + ["-C " + str(self.root) + " lean"] * 6,
                         (self.root / "build-runs").read_text().splitlines())

    def test_fetch_deadline_is_shared_across_snapshots(self):
        for run in (501, 502):
            self.assertEqual(0, self.transport("publish", str(run)).returncode)
        shutil.rmtree(self.root / ".lake/build")
        result = self.fetch_then_build(**self.deadline_probe(3, step=1), FAKE_FAIL="download")
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertIn("deadline exhausted", result.stdout)
        self.assertEqual([3, 2, 1], [call["timeout"] for call in self.gh_budgets()])
        snapshots = [call for call in self.gh_budgets() if call["args"][0] == "api"]
        self.assertEqual(1, len(snapshots))
        self.assertIn("502-1", snapshots[0]["args"][1])
        self.assertFalse((self.root / ".lake/build").exists())

    def test_hanging_publication_and_prune_are_optional_after_real_build(self):
        for run, operation in enumerate(("create", "upload", "edit"), 501):
            with self.subTest(operation=operation):
                result = self.transport("publish", str(run), **self.deadline_probe(1), FAKE_HANG=operation)
                self.assertEqual(0, result.returncode, result.stdout + result.stderr)
                self.assertIn('"status":"failed"', result.stdout)
                self.assertIn("timed out", result.stdout)
                self.assertEqual([1] * len(self.gh_budgets()),
                                 [call["timeout"] for call in self.gh_budgets()])
        for run in range(601, 606):
            self.assertEqual(0, self.transport("publish", str(run)).returncode)
        result = self.transport("publish", "606", **self.deadline_probe(1), FAKE_HANG="delete")
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertIn('"status":"published"', result.stdout)
        self.assertIn("timed out", result.stdout)
        self.assertEqual([1] * len(self.gh_budgets()), [call["timeout"] for call in self.gh_budgets()])
        failed = self.transport("publish", **self.deadline_probe(1), FAKE_HANG="create", FAKE_BUILD_EXIT="19")
        self.assertEqual(19, failed.returncode, failed.stdout + failed.stderr)
        self.assertFalse((self.root / "gh-budgets").exists())

    def test_publication_and_prune_share_one_deadline(self):
        for run in range(501, 506):
            self.assertEqual(0, self.transport("publish", str(run)).returncode)
        result = self.transport("publish", "506", **self.deadline_probe(6, step=1))
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertIn('"status":"published"', result.stdout)
        self.assertIn("deadline exhausted", result.stdout)
        self.assertEqual([6, 5, 4, 3, 2, 1], [call["timeout"] for call in self.gh_budgets()])
        self.assertEqual(["api", "create", "upload", "edit", "api", "list"],
                         [call["args"][0] if call["args"][0] == "api" else call["args"][1]
                          for call in self.gh_budgets()])
        self.assertEqual(6, len(list(self.remote.glob("*/release.json"))))

    def test_invalid_release_budget_is_optional_but_real_build_failure_is_not(self):
        for value in ("0", "-1", "nan", "601"):
            with self.subTest(budget=value):
                environment = {"STRATALINT_LEAN_CACHE_RELEASE_TIMEOUT_SECONDS": value}
                fetched = self.fetch_then_build(**environment)
                self.assertEqual(0, fetched.returncode, fetched.stdout + fetched.stderr)
                self.assertIn("STRATALINT_LEAN_CACHE_RELEASE_TIMEOUT_SECONDS", fetched.stdout)
                published = self.transport("publish", **environment)
                self.assertEqual(0, published.returncode, published.stdout + published.stderr)
                self.assertIn('"status":"failed"', published.stdout)
                self.assertEqual(19, self.transport("publish", **environment, FAKE_BUILD_EXIT="19").returncode)
                self.assertEqual([], list(self.remote.iterdir()))

    def test_optional_fetch_miss_reaches_build_and_preserves_build_failure(self):
        for build_exit in (0, 19):
            with self.subTest(build_exit=build_exit):
                result = self.fetch_then_build(FAKE_BUILD_EXIT=str(build_exit))
                self.assertEqual(build_exit, result.returncode, result.stdout + result.stderr)
                self.assertIn('"status":"miss"', result.stdout)
        self.assertEqual(["-C " + str(self.root) + " lean"] * 2,
                         (self.root / "build-runs").read_text().splitlines())

    def test_optional_fetch_corruption_and_download_failure_reach_build(self):
        self.assertEqual(0, self.transport("publish").returncode)
        shutil.rmtree(self.root / ".lake/build")
        for archive in self.remote.glob("*/lean-build.tgz"):
            write(archive, "corrupt transfer")
        for failure in ("", "download"):
            for build_exit in (0, 19):
                with self.subTest(failure=failure, build_exit=build_exit):
                    result = self.fetch_then_build(FAKE_FAIL=failure, FAKE_BUILD_EXIT=str(build_exit))
                    self.assertEqual(build_exit, result.returncode, result.stdout + result.stderr)
                    self.assertIn('"status":"miss"', result.stdout)
                    self.assertFalse((self.root / ".lake/build").exists())
        self.assertEqual(["lean-report"] + ["-C " + str(self.root) + " lean"] * 4,
                         (self.root / "build-runs").read_text().splitlines())

    def test_optional_fetch_valid_seed_still_reaches_build(self):
        self.assertEqual(0, self.transport("publish").returncode)
        shutil.rmtree(self.root / ".lake/build")
        result = self.fetch_then_build()
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertIn('"status":"unpacked"', result.stdout)
        self.assertEqual(["lean-report", "-C " + str(self.root) + " lean"],
                         (self.root / "build-runs").read_text().splitlines())

    def test_unavailable_lock_is_an_explicit_fetch_miss(self):
        # Built-in fcntl takes precedence over PYTHONPATH on some Python builds.
        write(self.bin / "sitecustomize.py", 'import sys\nsys.modules["fcntl"] = None\n')
        result = self.transport("fetch", PYTHONPATH=str(self.bin))
        self.assertEqual(1, result.returncode, result.stdout + result.stderr)
        self.assertIn('"status":"miss"', result.stdout)
        self.assertIn("fcntl", result.stdout)
        self.assertNotIn("Traceback", result.stderr)

    def test_unavailable_lock_skips_publication_after_build_success(self):
        write(self.bin / "sitecustomize.py", 'import sys\nsys.modules["fcntl"] = None\n')
        result = self.transport("publish", PYTHONPATH=str(self.bin))
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertIn('"status":"skipped"', result.stdout)
        self.assertIn("POSIX cache locking unavailable", result.stdout)
        self.assertNotIn("Traceback", result.stderr)
        self.assertEqual([], list(self.remote.iterdir()))
        failed = self.transport("publish", PYTHONPATH=str(self.bin), FAKE_BUILD_EXIT="19")
        self.assertEqual(19, failed.returncode, failed.stdout + failed.stderr)
        self.assertEqual([], list(self.remote.iterdir()))
        self.assertEqual(["lean-report", "lean-report"], (self.root / "build-runs").read_text().splitlines())

    def test_legacy_fetch_flag_cannot_enable_cross_partition_selection(self):
        self.assertEqual(0, self.transport("publish").returncode)
        shutil.rmtree(self.root / ".lake/build")
        restored = self.transport("fetch", arguments=("--allow-seed",))
        self.assertEqual(0, restored.returncode, restored.stdout + restored.stderr)
        self.assertTrue((self.root / ".lake/build/lib/lean/D5/A.olean").is_file())
        shutil.rmtree(self.root / ".lake/build")
        self.manifest["packages"][0]["rev"] = OTHER
        self.save_manifest()
        self.assertNotEqual(0, self.transport("fetch", arguments=("--allow-seed",)).returncode)
        self.assertFalse((self.root / ".lake/build").exists())

    def test_roundtrip_is_partitioned_and_source_sha_is_provenance_only(self):
        address = self.transport("address")
        self.assertEqual(0, address.returncode, address.stdout + address.stderr)
        report_path = "build/lean-inspector/report.zip"
        write(self.root / ".lake" / report_path, '{"material":"report-seed"}\n')
        saved = self.transport("publish")
        self.assertEqual(0, saved.returncode, saved.stdout + saved.stderr)
        self.assertIn('"status":"published"', saved.stdout.replace(" ", ""))
        snapshot = next(self.remote.iterdir())
        metadata = json.loads((snapshot / "manifest.json").read_text())
        packed = (snapshot / "lean-build.tgz").read_bytes()
        self.assertEqual(digest(packed), metadata["archive_sha256"])
        self.assertEqual(len(packed), metadata["archive_bytes"])
        self.assertEqual([{"name": "lean-build.tgz", "sha256": digest(packed), "bytes": len(packed)}], metadata["parts"])
        with tarfile.open(snapshot / "lean-build.tgz") as archive:
            self.assertEqual(b"locally-produced-olean", archive.extractfile("build/lib/lean/D5/A.olean").read())
            self.assertEqual(b'{"material":"report-seed"}\n', archive.extractfile(report_path).read())
        shutil.rmtree(self.root / ".lake/build")
        write(self.root / "D5/A.lean", "def a := 333\n")
        restored = self.transport("fetch", GITHUB_SHA="e"*40)
        self.assertEqual(0, restored.returncode, restored.stdout + restored.stderr)
        self.assertEqual("locally-produced-olean", (self.root / ".lake/build/lib/lean/D5/A.olean").read_text())
        self.assertEqual('{"material":"report-seed"}\n', (self.root / ".lake" / report_path).read_text())
        self.assertIn('"mode":"partition"', restored.stdout.replace(" ", ""))

    def test_missing_corrupt_and_cross_partition_are_misses_without_target_writes(self):
        missing = self.transport("fetch")
        self.assertNotEqual(0, missing.returncode)
        self.assertEqual(0, self.transport("publish").returncode)
        shutil.rmtree(self.root / ".lake/build")
        self.manifest["packages"][0]["rev"] = OTHER
        self.save_manifest()
        self.assertNotEqual(0, self.transport("fetch").returncode)
        self.assertFalse((self.root / ".lake/build").exists())
        self.manifest["packages"][0]["rev"] = REV
        self.save_manifest()
        for archive in self.remote.glob("*/lean-build.tgz"):
            write(archive, "corrupt transfer")
        self.assertNotEqual(0, self.transport("fetch").returncode)
        self.assertFalse((self.root / ".lake/build").exists())

    def test_failed_save_never_publishes_a_usable_partial_snapshot(self):
        result = self.transport("publish", FAKE_FAIL="upload")
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertIn('"status":"failed"', result.stdout.replace(" ", ""))
        shutil.rmtree(self.root / ".lake/build")
        self.assertNotEqual(0, self.transport("fetch").returncode)
        self.assertFalse((self.root / ".lake/build").exists())

    def test_failed_github_command_preserves_stderr_and_exit_in_receipt(self):
        diagnostic = "HTTP 422: fixture rejection\n具体原因: invalid fixture target\n"
        result = self.transport("publish", FAKE_FAIL="create", FAKE_FAIL_STDERR=diagnostic)
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        report = json.loads(next(line.removeprefix("LEAN_CACHE_PUBLISH ")
                                 for line in result.stdout.splitlines() if line.startswith("LEAN_CACHE_PUBLISH ")))
        self.assertEqual("failed", report["status"])
        self.assertIn("'gh', 'release', 'create'", report["reason"])
        self.assertIn("exit status 23", report["reason"])
        self.assertTrue(report["reason"].endswith("stderr: " + diagnostic), report)
        self.assertEqual([], list(self.remote.iterdir()))

    def test_failed_github_command_without_stderr_reports_explicit_fallback(self):
        result = self.transport("publish", FAKE_FAIL="create")
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        report = json.loads(next(line.removeprefix("LEAN_CACHE_PUBLISH ")
                                 for line in result.stdout.splitlines() if line.startswith("LEAN_CACHE_PUBLISH ")))
        self.assertEqual("failed", report["status"])
        self.assertIn("exit status 23", report["reason"])
        self.assertIn("stderr: <empty>", report["reason"])
        self.assertEqual([], list(self.remote.iterdir()))

    def test_existing_published_release_is_reused_without_remote_mutation(self):
        self.assertEqual(0, self.transport("publish").returncode)
        before = {path.name: path.read_bytes() for path in next(self.remote.iterdir()).iterdir()}
        result = self.transport("publish", FAKE_GH_LOG=str(self.root / "gh.log"))
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertIn('"status":"exists"', result.stdout.replace(" ", ""))
        self.assertEqual(before, {path.name: path.read_bytes() for path in next(self.remote.iterdir()).iterdir()})
        calls = [json.loads(line) for line in (self.root / "gh.log").read_text().splitlines()]
        self.assertEqual(["api"], [call[0] for call in calls])

    def test_draft_or_malformed_exact_metadata_fails_before_create(self):
        self.assertEqual(0, self.transport("publish").returncode)
        snapshot = next(self.remote.iterdir())
        before = {path.name: path.read_bytes() for path in snapshot.iterdir()}
        valid = json.loads((snapshot / "release.json").read_text())
        malformed = [dict(valid, draft=True), dict(valid, draft="false"), {},
                     {"draft": False}, {key: value for key, value in valid.items() if key != "tag_name"},
                     dict(valid, tag_name="other-tag"), dict(valid, target_commitish="e" * 40)]
        for metadata in [*(json.dumps(value) for value in malformed), "not-json", ""]:
            with self.subTest(metadata=metadata):
                (self.root / "gh.log").unlink(missing_ok=True)
                result = self.transport("publish", FAKE_LOOKUP_API_JSON=metadata,
                                        FAKE_GH_LOG=str(self.root / "gh.log"))
                self.assertEqual(0, result.returncode, result.stdout + result.stderr)
                self.assertIn('"status":"failed"', result.stdout.replace(" ", ""))
                self.assertIn("exact release", result.stdout)
                calls = [json.loads(line) for line in (self.root / "gh.log").read_text().splitlines()]
                self.assertEqual(["api"], [call[0] for call in calls])
                self.assertEqual(before, {path.name: path.read_bytes() for path in next(self.remote.iterdir()).iterdir()})

    def test_failed_exact_lookup_stops_before_remote_writes_and_preserves_diagnostics(self):
        for body in ('{"message":"Forbidden","status":"403"}',
                     '{"message":"Server error","status":"500"}', 'not-json', ''):
            with self.subTest(body=body):
                (self.root / "gh.log").unlink(missing_ok=True)
                diagnostic = "lookup transport failed\nsecond line\n"
                result = self.transport("publish", FAKE_LOOKUP_API_JSON=body, FAKE_LOOKUP_API_EXIT="1",
                                        FAKE_LOOKUP_API_STDERR=diagnostic,
                                        FAKE_GH_LOG=str(self.root / "gh.log"))
                self.assertEqual(0, result.returncode, result.stdout + result.stderr)
                report = json.loads(next(line.partition(" ")[2] for line in result.stdout.splitlines()
                                         if line.startswith("LEAN_CACHE_PUBLISH ")))
                self.assertEqual("failed", report["status"])
                self.assertTrue(report["reason"].endswith("stderr: " + diagnostic), report)
                self.assertEqual([], list(self.remote.iterdir()))
                calls = [json.loads(line) for line in (self.root / "gh.log").read_text().splitlines()]
                self.assertEqual(["api"], [call[0] for call in calls])

    def invalid_post_edit_responses(self, tag, commit):
        published = dict(draft=False, tag_name=tag, target_commitish=commit)
        malformed = [dict(published, draft=True), [], {"draft": False},
                     dict(published, tag_name="wrong-tag"), dict(published, target_commitish="e" * 40)]
        return [*((json.dumps(value), "0") for value in malformed), ("not-json", "0"),
                ('{"message":"Not Found","status":"404"}', "1"),
                ('{"message":"Forbidden","status":"403"}', "1"),
                ('{"message":"Server error","status":"500"}', "1")]

    def test_post_edit_confirmation_is_required_before_publication_success(self):
        partition = json.loads(self.transport("address").stdout)["partition"]
        tag = "lean-cache-v2-" + partition.replace("/", "-") + "-123-1"
        for metadata, status in self.invalid_post_edit_responses(tag, "d" * 40):
            with self.subTest(metadata=metadata, status=status):
                shutil.rmtree(self.remote)
                self.remote.mkdir()
                (self.root / "gh.log").unlink(missing_ok=True)
                result = self.transport("publish", FAKE_POST_EDIT_API_JSON=metadata,
                                        FAKE_POST_EDIT_API_EXIT=status, FAKE_GH_LOG=str(self.root / "gh.log"))
                self.assertEqual(0, result.returncode, result.stdout + result.stderr)
                self.assertIn('"status":"failed"', result.stdout)
                self.assertNotIn('"status":"published"', result.stdout)
                calls = [json.loads(line) for line in (self.root / "gh.log").read_text().splitlines()]
                self.assertEqual(["api", "create", "upload", "edit", "api"],
                                 [call[0] if call[0] == "api" else call[1] for call in calls])

    def test_concurrent_publishers_keep_distinct_complete_snapshots(self):
        with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
            results = list(pool.map(lambda run: self.transport("publish", run), ["401", "402"]))
        self.assertEqual([0, 0], [result.returncode for result in results])
        releases = [json.loads(path.read_text()) for path in self.remote.glob("*/release.json")]
        self.assertEqual(2, len(releases))
        self.assertTrue(all(not release["draft"] for release in releases))
        self.assertEqual(2, len({release["tag_name"] for release in releases}))

    def test_direct_fetch_respects_existing_cache_writer(self):
        import fcntl
        self.assertEqual(0, self.transport("publish").returncode)
        shutil.rmtree(self.root / ".lake/build")
        address = digest(str((self.root / ".lake").resolve()).encode())
        directory = self.root / ".cache/stratalint-lean-cache-guards"
        directory.mkdir(parents=True, exist_ok=True)
        with (directory / (address + ".lock")).open("a+b") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            blocked = self.transport("fetch")
            self.assertNotEqual(0, blocked.returncode)
            self.assertFalse((self.root / ".lake/build").exists())
        self.assertEqual(0, self.transport("fetch").returncode)
        self.assertTrue((self.root / ".lake/build/lib/lean/D5/A.olean").is_file())

    def test_actions_seed_skips_fetch_but_publication_requires_successful_build(self):
        result = self.transport("fetch", STRATALINT_ACTIONS_CACHE_SEEDED="1")
        self.assertEqual(0, result.returncode, result.stderr)
        self.assertIn("skipped", result.stdout)
        result = self.transport("publish", FAKE_BUILD_EXIT="19")
        self.assertEqual(19, result.returncode, result.stdout + result.stderr)
        self.assertEqual([], list(self.remote.iterdir()))
        result = self.transport("publish", FAKE_BUILD_EXIT="0")
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertIn('"status":"published"', result.stdout)
        self.assertTrue(list(self.remote.iterdir()))

    def test_pr_cannot_publish_even_after_a_successful_build(self):
        result = self.transport("publish", GITHUB_EVENT_NAME="pull_request_target")
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertIn("skipped", result.stdout)
        self.assertEqual([], list(self.remote.iterdir()))

    def test_transfer_failure_is_a_miss_and_empty_target_accepts_a_complete_seed(self):
        self.assertEqual(0, self.transport("publish").returncode)
        shutil.rmtree(self.root / ".lake/build")
        failed = self.transport("fetch", FAKE_FAIL="download")
        self.assertNotEqual(0, failed.returncode)
        self.assertFalse((self.root / ".lake/build").exists())
        (self.root / ".lake/build").mkdir()
        restored = self.transport("fetch")
        self.assertEqual(0, restored.returncode, restored.stdout + restored.stderr)
        self.assertTrue((self.root / ".lake/build/lib/lean/D5/A.olean").is_file())

    def test_retention_keeps_five_complete_snapshots_and_cleanup_failure_is_nonfatal(self):
        for run in range(501, 508):
            self.assertEqual(0, self.transport("publish", str(run)).returncode)
        self.assertEqual(5, len(list(self.remote.glob("*/release.json"))))
        result = self.transport("publish", "508", FAKE_FAIL="delete")
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertIn('"status":"published"', result.stdout)
        self.assertIn("prune_error", result.stdout)



FAKE_GH = '''#!/usr/bin/env python3
import hashlib, json, os, pathlib, shutil, sys
args = sys.argv[1:]
root = pathlib.Path(os.environ["FAKE_REMOTE"])
if "FAKE_GH_LOG" in os.environ:
    with pathlib.Path(os.environ["FAKE_GH_LOG"]).open("a") as log:
        log.write(json.dumps(args) + "\\n")
verb = args[0] if args and args[0] == "api" else (args[1] if len(args) > 1 else "")
if os.environ.get("FAKE_HANG") == verb:
    import signal
    signal.pause()
def fail():
    sys.stderr.write(os.environ.get("FAKE_FAIL_STDERR", ""))
    sys.exit(23)
if len(args) > 1 and os.environ.get("FAKE_FAIL") == verb and verb != "upload": fail()
if args[:2] == ["release", "list"] and "FAKE_LIST_JSON" in os.environ:
    print(os.environ["FAKE_LIST_JSON"]); sys.exit(0)
if args[0] == "api" and "FAKE_API_JSON" in os.environ:
    print(os.environ["FAKE_API_JSON"]); sys.exit(0)
if args[0] == "api" and "FAKE_VERIFICATION_API" in os.environ:
    responses = json.loads(pathlib.Path(os.environ["FAKE_VERIFICATION_API"]).read_text())
    if args[1] in responses:
        print(json.dumps(responses[args[1]])); sys.exit(0)
def option(name): return args[args.index(name)+1]
def metadata(directory):
    value = json.loads((directory / "release.json").read_text())
    value["assets"] = [{"name": p.name, "size": p.stat().st_size, "digest": "sha256:" + hashlib.sha256(p.read_bytes()).hexdigest()}
                       for p in directory.iterdir() if p.name != "release.json"]
    return value
if args[:2] == ["release", "list"]:
    print(json.dumps([{"tagName": p.parent.name, "createdAt": p.parent.name, "isDraft": json.loads(p.read_text())["draft"]}
                      for p in root.glob("*/release.json")]))
elif args[0] == "api":
    directory = root / args[1].split("/")[-1]
    phase = "FAKE_POST_EDIT_API" if (root.parent / ("gh-edited-" + str(os.getppid()))).exists() else "FAKE_LOOKUP_API"
    if phase + "_JSON" in os.environ:
        print(os.environ[phase + "_JSON"])
        sys.stderr.write(os.environ.get(phase + "_STDERR", ""))
        sys.exit(int(os.environ.get(phase + "_EXIT", "0")))
    if not directory.exists():
        print(json.dumps({"message": "Not Found", "status": "404"}))
        sys.exit(1)
    print(json.dumps(metadata(directory)))
else:
    verb, tag = args[1:3]
    directory = root / tag
    if verb == "create":
        directory.mkdir()
        (directory / "release.json").write_text(json.dumps({"tag_name": tag, "target_commitish": option("--target"), "draft": True}))
    elif verb == "upload":
        for value in args[3:]:
            if pathlib.Path(value).is_file(): shutil.copyfile(value, directory / pathlib.Path(value).name)
        if os.environ.get("FAKE_FAIL") == "upload": fail()
    elif verb == "edit":
        value = json.loads((directory / "release.json").read_text()); value["draft"] = False
        (directory / "release.json").write_text(json.dumps(value))
        (root.parent / ("gh-edited-" + str(os.getppid()))).touch()
        if os.environ.get("FAKE_DAMAGE_AFTER_EDIT") == "1":
            (directory / "lean-build.tgz").write_bytes(b"damaged after upload")
        if os.environ.get("FAKE_TRUNCATE_AFTER_EDIT") == "1":
            archive = directory / "lean-build.tgz"
            packed = archive.read_bytes()[:-8]; archive.write_bytes(packed)
            manifest = json.loads((directory / "manifest.json").read_text())
            digest = hashlib.sha256(packed).hexdigest()
            manifest.update(archive_bytes=len(packed), archive_sha256=digest,
                parts=[{"name": archive.name, "bytes": len(packed), "sha256": digest}])
            (directory / "manifest.json").write_text(json.dumps(manifest))
    elif verb == "download":
        destination = pathlib.Path(option("--dir")); destination.mkdir(exist_ok=True)
        if not directory.exists():
            sys.exit(0)
        patterns = [args[i + 1] for i, value in enumerate(args) if value == "--pattern" and i + 1 < len(args)]
        for path in directory.iterdir():
            if path.name != "release.json" and (not patterns or path.name in patterns):
                shutil.copyfile(path, destination / path.name)
    elif verb == "view":
        if not directory.exists(): sys.exit(1)
        print(json.dumps(metadata(directory)))
    elif verb == "delete": shutil.rmtree(directory)
    else: sys.exit(2)
'''
