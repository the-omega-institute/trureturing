"""Behavioral contracts for bounded, complete cache material validation."""
import contextlib
import io
import json
import os
from pathlib import Path
import sys
import tempfile
import threading
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tools/scripts/worktree"))
import cache_material as material
import lean_actions as actions


class CacheMaterialContracts(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="cache-material-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.data = self.root / "data"
        self.data.mkdir()
        for name, value in [("a", b"alpha"), ("b", b"beta"),
                            ("nested/c", b"gamma"), ("nested/d", b"delta")]:
            path = self.data / name
            path.parent.mkdir(exist_ok=True)
            path.write_bytes(value)
        self.expected = material.files(self.data)

    def cpu(self, online=4, affinity=4, linux=False):
        stack = contextlib.ExitStack()
        stack.enter_context(mock.patch.object(material.os, "cpu_count", return_value=online))
        stack.enter_context(mock.patch.object(material.os, "sched_getaffinity",
                                             return_value=set(range(affinity)), create=True))
        stack.enter_context(mock.patch.object(material.sys, "platform", "linux" if linux else "darwin"))
        return stack

    def cgroup(self, membership, mounts, contents):
        def read(path, *args, **kwargs):
            name = str(path)
            if name == "/proc/self/cgroup":
                return membership
            if name == "/proc/self/mountinfo":
                return mounts
            if name in contents:
                return contents[name]
            raise FileNotFoundError(name)
        return mock.patch.object(Path, "read_text", read)

    def test_cpu_capacity_tracks_limits_without_a_fixed_worker_cap(self):
        for online, affinity, files, workers in [(2, 8, 20, 2), (3, 8, 20, 3),
                                                  (64, 33, 50, 33), (64, 64, 2, 2)]:
            with self.subTest(online=online, affinity=affinity), self.cpu(online, affinity), \
                    mock.patch.object(os, "getloadavg", side_effect=AssertionError("load is not capacity")):
                self.assertEqual(workers, material.hash_workers(files))

    def test_cpu_capacity_rejects_unknown_empty_and_subcpu_capacity(self):
        for online, affinity in [(None, 2), (0, 2), (4, 0)]:
            with self.subTest(online=online, affinity=affinity), self.cpu(online, affinity):
                with self.assertRaisesRegex(ValueError, "CPU capacity"):
                    material.hash_workers(4)
        mounts = "31 1 0:1 / /sys/fs/cgroup rw - cgroup2 cgroup rw\n"
        with self.cpu(linux=True), self.cgroup("0::/job\n", mounts,
                {"/sys/fs/cgroup/cpu.max": "max 100000\n",
                 "/sys/fs/cgroup/job/cpu.max": "50000 100000\n"}):
            with self.assertRaisesRegex(ValueError, "CPU capacity"):
                material.hash_workers(4)

    def test_cgroup_quotas_include_ancestors_and_preserve_fractional_limits(self):
        mounts = "31 1 0:1 / /sys/fs/cgroup rw - cgroup2 cgroup rw\n"
        values = {"/sys/fs/cgroup/cpu.max": "max 100000\n",
                  "/sys/fs/cgroup/jobs/cpu.max": "250000 100000\n",
                  "/sys/fs/cgroup/jobs/current/cpu.max": "390000 100000\n"}
        with self.cpu(8, 6, linux=True), self.cgroup("0::/jobs/current\n", mounts, values):
            self.assertEqual(2, material.hash_workers(8))
            values["/sys/fs/cgroup/jobs/cpu.max"] = "350000 100000\n"
            self.assertEqual(3, material.hash_workers(8))
            values["/sys/fs/cgroup/jobs/current/cpu.max"] = "invalid\n"
            with self.assertRaises(ValueError):
                material.hash_workers(8)

    def test_cgroup_v1_cpu_mount_root_and_unlimited_ancestors(self):
        mounts = "31 1 0:1 /tenant /sys/fs/cgroup/cpu rw - cgroup cgroup rw,cpu,cpuacct\n"
        values = {"/sys/fs/cgroup/cpu/cpu.cfs_quota_us": "-1\n",
                  "/sys/fs/cgroup/cpu/cpu.cfs_period_us": "100000\n",
                  "/sys/fs/cgroup/cpu/job/cpu.cfs_quota_us": "200000\n",
                  "/sys/fs/cgroup/cpu/job/cpu.cfs_period_us": "100000\n"}
        with self.cpu(8, 6, linux=True), self.cgroup("2:cpu,cpuacct:/tenant/job\n", mounts, values):
            self.assertEqual(2, material.hash_workers(8))

    def test_cgroup_unresolved_membership_and_partial_quota_fail_explicitly(self):
        mounts = "31 1 0:1 /tenant /sys/fs/cgroup/cpu rw - cgroup cgroup rw,cpu\n"
        for member in ["cpu.cfs_quota_us", "cpu.cfs_period_us"]:
            values = {"/sys/fs/cgroup/cpu/job/" + member: "100000\n"}
            with self.subTest(member=member), self.cpu(linux=True), \
                    self.cgroup("2:cpu:/tenant/job\n", mounts, values):
                with self.assertRaises((ValueError, FileNotFoundError)):
                    material.hash_workers(4)
        with self.cpu(linux=True), self.cgroup("2:cpu:/tenant/job\n", mounts, {}):
            self.assertEqual(4, material.hash_workers(4))
        with self.cpu(linux=True), self.cgroup("2:cpu:/other/job\n", mounts, {}):
            with self.assertRaisesRegex(ValueError, "unresolved cgroup"):
                material.hash_workers(4)

    def test_parallel_validation_matches_serial_with_complete_declared_material(self):
        barrier = threading.Barrier(2)
        lock = threading.Lock()
        seen = []
        original = material.sha

        def hashing(path):
            with lock:
                seen.append(path.relative_to(self.data).as_posix())
            barrier.wait()  # The outer process hang guard diagnoses a deadlocked producer.
            return original(path)

        with self.cpu(2, 2), mock.patch.object(material, "sha", side_effect=hashing):
            actual = material.files(self.data, expected=list(reversed(self.expected)), parallel=True)
        self.assertEqual(self.expected, actual)
        self.assertCountEqual([row["path"] for row in self.expected], seen)
        self.assertEqual(len(seen), len(set(seen)))

    def test_manifest_validation_precedes_hashing_and_rejects_copy_mode(self):
        duplicate = self.expected + [self.expected[0]]
        with self.cpu(), mock.patch.object(material, "sha", side_effect=AssertionError("read before validation")):
            with self.assertRaisesRegex(ValueError, "duplicate"):
                material.files(self.data, expected=duplicate, parallel=True)
            with self.assertRaises(ValueError):
                material.files(self.data, expected=self.expected, copy_to=self.root / "copy", parallel=True)
            with self.assertRaises(ValueError):
                material.files(self.data, parallel=True)
        self.assertFalse((self.root / "copy").exists())

    def test_parallel_errors_are_reported_in_manifest_order(self):
        second_batch = threading.Event()

        def hashing(path):
            name = path.relative_to(self.data).as_posix()
            if name == "a":
                second_batch.wait()
                raise OSError("first manifest failure")
            if name == "nested/c":
                second_batch.set()
                raise OSError("later manifest failure")
            raise AssertionError("a failed batch continued")

        with self.cpu(2, 2), mock.patch.object(material, "sha", side_effect=hashing):
            with self.assertRaisesRegex(OSError, "first manifest failure"):
                material.files(self.data, expected=self.expected, parallel=True)

    def test_moved_restore_rejects_damage_and_returns_owned_source(self):
        for defect in ["content", "mode", "missing", "extra", "symlink"]:
            with self.subTest(defect=defect), tempfile.TemporaryDirectory(dir=self.root) as location:
                cached, staged = Path(location) / "cached", Path(location) / "staged"
                cached.mkdir()
                member = cached / "one"
                member.write_bytes(b"expected")
                (cached / "two").write_bytes(b"another verified member")
                expected = material.files(cached)
                if defect == "content":
                    member.write_bytes(b"corrupt")
                elif defect == "mode":
                    member.chmod((member.stat().st_mode & 0o777) ^ 0o100)
                elif defect == "missing":
                    member.unlink()
                elif defect == "extra":
                    (cached / "extra").write_bytes(b"unlisted")
                else:
                    member.unlink()
                    member.symlink_to(self.data / "a")
                with self.cpu(2, 2), self.assertRaises((ValueError, OSError)):
                    actions.move_validated_cache_data(cached, staged, expected)
                self.assertTrue(cached.is_dir())
                self.assertFalse(staged.exists())

    def test_hash_io_exception_rolls_back_before_publication(self):
        staged = self.root / "staged"
        with self.cpu(2, 2), mock.patch.object(material, "sha", side_effect=OSError("unreadable")):
            with self.assertRaisesRegex(OSError, "unreadable"):
                actions.move_validated_cache_data(self.data, staged, self.expected)
        self.assertTrue(self.data.is_dir())
        self.assertFalse(staged.exists())
        self.assertEqual(self.expected, material.files(self.data))

    def test_worker_start_failure_joins_started_readers_and_is_an_optional_miss(self):
        cached = self.root / "cache"
        cached.mkdir()
        self.data.rename(cached / "data")
        key = "project-17-2"
        (cached / "manifest.json").write_text(json.dumps(dict(schema="lean-actions-seed-v1",
            partition="fixture", layer="project", key=key, files=self.expected)))
        target = self.root / "candidate"
        target.mkdir()
        (target / "current").write_bytes(b"candidate bytes")
        keys = {"partition": "fixture", "project": {"path": "cache", "target": "candidate",
                "restore_prefix": "project-", "key": key}}
        release = threading.Event()
        original_start, original_sha = threading.Thread.start, material.sha
        starts, completed = [], []

        def start(thread):
            starts.append(thread)
            if len(starts) == 2:
                release.set()
                raise RuntimeError("can't start new thread")
            return original_start(thread)

        def hashing(path):
            release.wait()  # One reader is running when the next worker fails.
            value = original_sha(path)
            completed.append(path.name)
            return value

        with self.cpu(2, 2), mock.patch.object(threading.Thread, "start", start), \
                mock.patch.object(material, "sha", side_effect=hashing), \
                mock.patch.object(actions, "cache_guard", return_value=contextlib.nullcontext()), \
                mock.patch.dict(os.environ, GITHUB_ENV=str(self.root / "environment")), \
                contextlib.redirect_stdout(io.StringIO()) as output:
            actions.restore(self.root, keys, {"project": key}, ["project"])
        self.assertEqual(2, len(starts))
        self.assertFalse(starts[0].is_alive())
        self.assertTrue(completed)
        self.assertIn('"status": "miss"', output.getvalue())
        self.assertIn("can't start new thread", output.getvalue())
        self.assertIn("STRATALINT_ACTIONS_CACHE_SEEDED=0", output.getvalue())
        self.assertEqual(b"candidate bytes", (target / "current").read_bytes())
        self.assertEqual(self.expected, material.files(cached / "data"))
        self.assertFalse((cached / "restored.json").exists())
        self.assertEqual([], list(self.root.glob(".actions-*")))

    def test_snapshot_fast_difference_check_remains_serial(self):
        with mock.patch.object(material, "hash_workers", side_effect=AssertionError("unexpected parallel read")):
            self.assertEqual(self.expected,
                             actions.validate_cache_directory(self.data, self.expected, small_files_first=True))


if __name__ == "__main__":
    unittest.main(verbosity=2)
