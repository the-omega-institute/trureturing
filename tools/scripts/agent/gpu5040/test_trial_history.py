"""Storage contracts use only small synthetic data and standard-library unittest."""

import copy
import json
import os
from pathlib import Path
import sqlite3
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from search_config import Config, descriptor, identity
from state_store import StateLocks, external_path, shared_root
from trial_history import Registry


RUNTIME = {"torch": "2.8.0", "numpy": "2.0.2", "python": "3.9.6",
           "platform": "macOS-test", "machine": "arm64", "hardware": "synthetic",
           "actual_device": "mps:0", "training_precision": "torch.float32",
           "cpu_fallback": False, "torch_cpu_threads": 1,
           "environment": {"PYTORCH_ENABLE_MPS_FALLBACK": "0",
                           "PYTORCH_MPS_FAST_MATH": None,
                           "PYTORCH_MPS_PREFER_METAL": None}}


class HistoryTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="gpu5040-test-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.db = self.root / "history.sqlite3"
        self.registry = Registry(self.db)
        self.addCleanup(self.registry.close)
        self.config = Config(dimensions=(13,), seed_steps=3)
        self.desc = descriptor(self.config, 13, 5040, RUNTIME)

    def test_identity_is_canonical_and_cosmetic_settings_do_not_invalidate(self):
        reverse = dict(reversed(list(self.desc.items())))
        self.assertEqual(identity(self.desc), identity(reverse))
        for name, value in (("batch_steps", 1), ("log_backups", 4),
                            ("log_max_bytes", 8192), ("verification_gap", 0.1),
                            ("verification_interval_steps", 12),
                            ("verification_chunk_size", 32), ("mps_memory_fraction", 0.1)):
            with self.subTest(name=name):
                config = copy.deepcopy(self.config)
                setattr(config, name, value)
                self.assertEqual(self.desc, descriptor(config, 13, 5040, RUNTIME))
        runtime = dict(RUNTIME, python_executable="/a/different/python")
        self.assertEqual(self.desc, descriptor(self.config, 13, 5040, runtime))

    def test_every_scientific_setting_changes_identity(self):
        variants = [descriptor(self.config, 16, 5040, RUNTIME),
                    descriptor(self.config, 13, 5041, RUNTIME)]
        for name, value in (("seed_steps", 4), ("learning_rate", 0.02),
                            ("minimum_learning_rate", 0.0001)):
            config = copy.deepcopy(self.config)
            setattr(config, name, value)
            variants.append(descriptor(config, 13, 5040, RUNTIME))
        for key in ("torch", "python", "platform", "hardware"):
            variants.append(descriptor(self.config, 13, 5040, dict(RUNTIME, **{key: "changed"})))
        for key in ("algorithm", "dtype", "physical_model", "initialization", "optimizer"):
            altered = copy.deepcopy(self.desc)
            altered[key] = "changed"
            variants.append(altered)
        runtime = copy.deepcopy(RUNTIME)
        runtime["environment"]["PYTORCH_MPS_FAST_MATH"] = "1"
        variants.append(descriptor(self.config, 13, 5040, runtime))
        for variant in variants:
            self.assertNotEqual(identity(self.desc), identity(variant))

    def test_verifier_version_does_not_change_optimizer_identity(self):
        runtime = dict(RUNTIME, numpy="a different verifier version")
        self.assertEqual(self.desc, descriptor(self.config, 13, 5040, runtime))

    def test_unique_claim_statuses_and_provenance_are_separate(self):
        key = self.registry.claim(self.desc, self.root / "one", {"source": "old"})
        self.assertFalse(self.registry.completed(self.desc))
        with self.assertRaisesRegex(ValueError, "resume|owned"):
            self.registry.claim(self.desc, self.root / "two", {})
        self.registry.mark(key, "interrupted")
        self.assertFalse(self.registry.completed(self.desc))
        self.registry.mark(key, "failed")
        self.assertFalse(self.registry.completed(self.desc))
        self.registry.claim(self.desc, self.root / "one", {"source": "new"})
        summary = {"initial": {"fidelity": 0.1}, "final": {"fidelity": 0.2},
                   "best": {"fidelity": 0.3}, "best_complete": True}
        self.registry.complete(key, 3, summary, "c" * 64)
        self.registry.complete(key, 3, summary, "c" * 64)
        self.assertTrue(self.registry.completed(self.desc))
        self.registry.mark(key, "failed")
        row = self.registry.get(key)
        self.assertEqual("completed", row["status"])
        self.assertEqual(summary, row["summary"])
        self.assertEqual({"source": "new"}, row["provenance"])
        self.assertEqual(1, len(self.registry.rows()))
        with self.assertRaisesRegex(ValueError, "budget|iteration"):
            self.registry.complete(key, 2, summary, "c" * 64)

    def test_champion_and_candidate_verification_are_independent(self):
        key = self.registry.claim(self.desc, self.root, {})
        self.registry.champion(13, "a" * 64, {"fidelity": 0.7}, str(self.root / "best-13.pt"))
        self.registry.champion(13, "b" * 64, {"fidelity": 0.6}, "/lesser")
        self.registry.verification("a" * 64, "verified", {"target_fidelity": 0.6999})
        self.assertEqual("running", self.registry.get(key)["status"])
        self.assertEqual("a" * 64, self.registry.champions()[0]["candidate_sha256"])
        self.assertEqual([], self.registry.verifications("b" * 64))
        self.assertEqual("verified", self.registry.verifications("a" * 64)[0]["status"])

    def test_sqlite_extra_rollback_journal_and_read_only_query(self):
        self.assertEqual((3,), self.registry.connection.execute("PRAGMA synchronous").fetchone())
        self.assertEqual(("delete",), self.registry.connection.execute("PRAGMA journal_mode").fetchone())
        self.registry.claim(self.desc, self.root, {})
        self.registry.close()
        original = self.db.read_bytes()
        result = subprocess.run([sys.executable, "-B", "-S", str(Path(__file__).with_name(
            "trial_history.py")), "--history-db", str(self.db)], capture_output=True, text=True,
            timeout=30)
        self.assertEqual(0, result.returncode, result.stderr)
        rows = json.loads(result.stdout)["trials"]
        self.assertEqual(1, len(rows))
        self.assertEqual(original, self.db.read_bytes())
        self.assertFalse(self.db.with_name(self.db.name + "-wal").exists())

    def test_missing_read_only_database_is_not_created(self):
        missing = self.root / "absent" / "history.sqlite3"
        result = subprocess.run([sys.executable, "-B", "-S", str(Path(__file__).with_name(
            "trial_history.py")), "--history-db", str(missing)], capture_output=True, text=True,
            timeout=30)
        self.assertEqual(0, result.returncode, result.stderr)
        self.assertEqual([], json.loads(result.stdout)["trials"])
        self.assertFalse(missing.parent.exists())

    def test_state_and_gpu_locks_across_states_and_source_copies(self):
        with patch.dict(os.environ, {"GPU5040_SHARED_ROOT": str(self.root / "shared")}):
            self.assertEqual(self.root / "shared", shared_root())
            with StateLocks(self.root / "one"):
                for state in (self.root / "one", self.root / "two"):
                    with self.assertRaisesRegex(ValueError, "lock"):
                        with StateLocks(state):
                            self.fail("concurrent owner admitted")
                module = Path(__file__).with_name("state_store.py")
                copy_path = self.root / "copy"
                copy_path.mkdir()
                (copy_path / module.name).write_bytes(module.read_bytes())
                result = subprocess.run([sys.executable, "-B", "-c",
                    "from state_store import StateLocks\nimport sys\n"
                    "with StateLocks(sys.argv[1]): pass", str(self.root / "three")],
                    cwd=copy_path, capture_output=True, text=True, timeout=30)
                self.assertNotEqual(0, result.returncode)
                self.assertIn("lock", result.stderr)
            with StateLocks(self.root / "two"):
                pass

    def test_lock_order_is_state_then_shared_and_failed_acquisition_releases_state(self):
        with patch.dict(os.environ, {"GPU5040_SHARED_ROOT": str(self.root / "shared")}):
            with StateLocks(self.root / "one"):
                with self.assertRaises(ValueError):
                    with StateLocks(self.root / "two"):
                        pass
            with StateLocks(self.root / "two") as locks:
                self.assertEqual(self.root / "two" / ".state.lock", locks.paths[0])
                self.assertEqual(shared_root() / "gpu-verifier.lock", locks.paths[1])

    def test_runtime_paths_reject_repo_or_source_tree(self):
        with self.assertRaisesRegex(ValueError, "source|repository|external"):
            external_path(Path(__file__).parent / "state")
        repository = self.root / "repository"
        repository.mkdir()
        (repository / ".git").write_text("synthetic worktree marker")
        with self.assertRaises(ValueError):
            external_path(repository / "state")
        self.assertEqual(self.root / "external", external_path(self.root / "external"))


if __name__ == "__main__":
    unittest.main()
