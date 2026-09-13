"""Release seed transport cases using a private local GitHub fake."""
import concurrent.futures
import json
import os
import pathlib
import shutil
import subprocess

from lean_seed_support import OTHER, PUBLISH, REV, PartitionFixture, digest, write


class ReleaseTransportCases(PartitionFixture):
    def setUp(self):
        super().setUp()
        self.remote = self.root / "remote"
        self.bin = self.root / "bin"
        self.bin.mkdir()
        self.remote.mkdir()
        write(self.root / ".lake/build/lib/lean/D5/A.olean", "locally-produced-olean")
        write(self.bin / "make", '#!/bin/sh\nprintf "%s\\n" "$*" >> "$FAKE_BUILD_LOG"\nexit "${FAKE_BUILD_EXIT:-0}"\n')
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
        self.assertEqual(["lean"] + ["-C " + str(self.root) + " lean"] * 6,
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
        result = self.transport("publish", "506", **self.deadline_probe(5, step=1))
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertIn('"status":"published"', result.stdout)
        self.assertIn("deadline exhausted", result.stdout)
        self.assertEqual([5, 4, 3, 2, 1], [call["timeout"] for call in self.gh_budgets()])
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
        self.assertEqual(["lean"] + ["-C " + str(self.root) + " lean"] * 4,
                         (self.root / "build-runs").read_text().splitlines())

    def test_optional_fetch_valid_seed_still_reaches_build(self):
        self.assertEqual(0, self.transport("publish").returncode)
        shutil.rmtree(self.root / ".lake/build")
        result = self.fetch_then_build()
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertIn('"status":"unpacked"', result.stdout)
        self.assertEqual(["lean", "-C " + str(self.root) + " lean"],
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
        self.assertEqual(["lean", "lean"], (self.root / "build-runs").read_text().splitlines())

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
        saved = self.transport("publish")
        self.assertEqual(0, saved.returncode, saved.stdout + saved.stderr)
        self.assertIn('"status":"published"', saved.stdout.replace(" ", ""))
        shutil.rmtree(self.root / ".lake/build")
        write(self.root / "D5/A.lean", "def a := 333\n")
        restored = self.transport("fetch", GITHUB_SHA="e"*40)
        self.assertEqual(0, restored.returncode, restored.stdout + restored.stderr)
        self.assertEqual("locally-produced-olean", (self.root / ".lake/build/lib/lean/D5/A.olean").read_text())
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
verb = args[0] if args and args[0] == "api" else (args[1] if len(args) > 1 else "")
if os.environ.get("FAKE_HANG") == verb:
    import signal
    signal.pause()
if len(args) > 1 and os.environ.get("FAKE_FAIL") == verb and verb != "upload": sys.exit(23)
if args[:2] == ["release", "list"] and "FAKE_LIST_JSON" in os.environ:
    print(os.environ["FAKE_LIST_JSON"]); sys.exit(0)
if args[0] == "api" and "FAKE_API_JSON" in os.environ:
    print(os.environ["FAKE_API_JSON"]); sys.exit(0)
def option(name): return args[args.index(name)+1]
def metadata(directory):
    value = json.loads((directory / "release.json").read_text())
    value["assets"] = [{"name": p.name, "digest": "sha256:" + hashlib.sha256(p.read_bytes()).hexdigest()}
                       for p in directory.iterdir() if p.name != "release.json"]
    return value
if args[:2] == ["release", "list"]:
    print(json.dumps([{"tagName": p.parent.name, "createdAt": p.parent.name, "isDraft": json.loads(p.read_text())["draft"]}
                      for p in root.glob("*/release.json")]))
elif args[0] == "api":
    directory = root / args[1].split("/")[-1]
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
        if os.environ.get("FAKE_FAIL") == "upload": sys.exit(23)
    elif verb == "edit":
        value = json.loads((directory / "release.json").read_text()); value["draft"] = False
        (directory / "release.json").write_text(json.dumps(value))
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
