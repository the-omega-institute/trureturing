"""Synthetic stopped snapshots; tensor serialization is CPU only."""

import copy
import dataclasses
import hashlib
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import torch

import legacy_conversion as legacy
from search_config import Config, OBJECTIVE, OCCUPATION, descriptor
from search_session import Campaign
from state_store import atomic_json, hash_json
from trial_history import Registry
from test_trial_history import RUNTIME


class LegacyTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="gpu5040-legacy-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.snapshot = self.root / "retained"
        self.snapshot.mkdir()
        self.output = self.root / "converted"
        self.db = self.root / "history.sqlite3"
        self.config = Config(dimensions=(13, 16), seed_steps=3)
        for name in ("gpu_worker.py", "tensor_core.py", "PREREGISTRATION.md"):
            (self.snapshot / name).write_text("synthetic retained " + name + "\n")
        self.source_hash = legacy.source_hash(self.snapshot)
        known = patch.object(legacy, "KNOWN_SOURCE_SHA256", self.source_hash)
        known.start()
        self.addCleanup(known.stop)
        environment = patch.dict(os.environ, {"GPU5040_SHARED_ROOT": str(self.root / "shared")})
        environment.start()
        self.addCleanup(environment.stop)
        self.saved = {
            "schema": 1, "kind": "latest", "occupation": list(OCCUPATION), "objective": OBJECTIVE,
            "source_sha256": self.source_hash, "config": dataclasses.asdict(self.config),
            "config_sha256": hash_json(dataclasses.asdict(self.config)),
            "preregistration_sha256": hashlib.sha256((self.snapshot / "PREREGISTRATION.md").read_bytes()).hexdigest(),
            "runtime": RUNTIME,
            "progress": {"run_index": 2, "iteration": 1, "total_steps": 7,
                         "dimension": 13, "seed": 5042, "seed_initial_fidelity": 0.01,
                         "last_verification": {}, "wall_seconds": 5.0, "created_utc": "synthetic-campaign"},
            "model": {"reflectors": torch.ones(13, 52), "initial": torch.ones(13)},
            "optimizer": {},
            "rng": {"torch_cpu": torch.tensor([1, 2], dtype=torch.uint8),
                    "torch_mps": torch.tensor([3, 4], dtype=torch.uint8)},
            "matrices": torch.ones(4, 13, 13), "initial": torch.ones(13),
            "metrics": {"fidelity": 0.2, "iteration": 1},
        }
        model = torch.nn.ParameterList([torch.nn.Parameter(value.clone()) for value in self.saved["model"].values()])
        optimizer = torch.optim.Adam(model.parameters(), lr=self.config.learning_rate, foreach=False, fused=False)
        for parameter in model:
            parameter.grad = torch.ones_like(parameter)
        optimizer.step()
        self.saved["optimizer"] = optimizer.state_dict()
        self.best = dict(self.saved, kind="best", dimension=13,
                         metrics={"fidelity": 0.4, "iteration": 0}, verification=None)
        self.write_snapshot()

    def write_snapshot(self):
        iteration = self.saved["progress"]["iteration"]
        if iteration:
            for state in self.saved["optimizer"]["state"].values():
                state["step"] = torch.tensor(float(iteration))
        else:
            self.saved["optimizer"]["state"] = {}
        self.saved["optimizer"]["param_groups"][0]["lr"] = (
            self.config.learning_rate_at(iteration - 1) if iteration else self.config.learning_rate)
        torch.save(self.saved, self.snapshot / "latest.pt")
        torch.save(self.best, self.snapshot / "best-13.pt")
        atomic_json(self.snapshot / "stopped.json", {
            "stopped": True, "source_sha256": self.source_hash,
            "checkpoint_sha256": hashlib.sha256((self.snapshot / "latest.pt").read_bytes()).hexdigest(),
            "best_sha256": {"best-13.pt": hashlib.sha256((self.snapshot / "best-13.pt").read_bytes()).hexdigest()}})

    def assert_tensors_equal(self, left, right):
        if isinstance(left, torch.Tensor):
            self.assertTrue(torch.equal(left, right))
        elif isinstance(left, dict):
            self.assertEqual(set(left), set(right))
            for key in left:
                self.assert_tensors_equal(left[key], right[key])
        else:
            self.assertEqual(left, right)

    def test_partial_prefix_unknown_metrics_and_preservation_idempotence(self):
        original = {p.name: p.read_bytes() for p in self.snapshot.iterdir()}
        report = legacy.convert(self.snapshot, self.output, self.db)
        self.assertEqual(2, report["completed_imported"])
        saved = torch.load(self.output / "latest.pt", weights_only=True)
        from gpu_worker import source_hash as current_source_hash
        self.assertEqual(current_source_hash(), saved["source_sha256"])
        self.assertEqual(self.source_hash, saved["migration_evidence"]["source_sha256"])
        for key in ("model", "optimizer", "rng", "matrices", "initial"):
            self.assert_tensors_equal(self.saved[key], saved[key])
        best = torch.load(self.output / "best-13.pt", weights_only=True)
        for key in ("model", "matrices", "initial"):
            self.assert_tensors_equal(self.best[key], best[key])
        before = (self.output / "latest.pt").read_bytes()
        again = legacy.convert(self.snapshot, self.output, self.db)
        self.assertEqual(report["lineage"], again["lineage"])
        self.assertEqual(before, (self.output / "latest.pt").read_bytes())
        with Registry(self.db) as registry:
            rows = registry.rows()
            self.assertEqual(3, len(rows))
            self.assertEqual(2, sum(row["status"] == "completed" for row in rows))
            for row in rows[:2]:
                self.assertIsNone(row["descriptor"]["runtime"])
                self.assertIsNone(row["summary"]["initial"])
                self.assertIsNone(row["summary"]["best"])
            self.assertEqual("interrupted", registry.get(saved["trial"]["identity"])["status"])
        self.assertEqual(original, {p.name: p.read_bytes() for p in self.snapshot.iterdir()})

    def test_end_boundary_imports_current_but_not_next_and_lineage_is_explicit(self):
        self.saved["progress"].update(iteration=3, total_steps=9)
        self.saved["metrics"]["iteration"] = 3
        self.write_snapshot()
        report = legacy.convert(self.snapshot, self.output, self.db)
        self.assertEqual(3, report["completed_imported"])
        saved = torch.load(self.output / "latest.pt", weights_only=True)
        with Registry(self.db) as registry:
            campaign = Campaign(self.output, self.config, registry, RUNTIME,
                                checkpoint=saved, fresh_start=True)
            campaign.select()
            self.assertEqual(3, campaign.run_index)
            self.assertEqual(3, campaign.skipped_trials)
            other = self.root / "independent"
            other.mkdir()
            independent = Campaign(other, self.config, registry, RUNTIME)
            independent.select()
            self.assertEqual(0, independent.run_index)
            self.assertFalse(registry.completed(descriptor(self.config, 13, 5040, RUNTIME)))
            config = copy.deepcopy(self.config)
            config.learning_rate = 0.02
            changed = Campaign(self.root / "changed", config, registry, RUNTIME, lineage=report["lineage"])
            changed.select()
            self.assertEqual(0, changed.run_index)

    def test_no_history_before_fresh_start_is_inferred(self):
        self.saved["progress"].update(run_index=0, iteration=0, total_steps=0, dimension=13, seed=5040)
        self.saved["metrics"]["iteration"] = 0
        self.write_snapshot()
        report = legacy.convert(self.snapshot, self.output, self.db)
        self.assertEqual(0, report["completed_imported"])

    def test_retained_champion_and_verification_are_imported_by_candidate_digest(self):
        from gpu_worker import tensor_digest
        digest = tensor_digest(self.best["matrices"], self.best["initial"])
        self.best["candidate_sha256"] = digest
        self.best["verification"] = {"candidate_sha256": digest, "target_fidelity": 0.3999}
        self.write_snapshot()
        legacy.convert(self.snapshot, self.output, self.db)
        with Registry(self.db) as registry:
            self.assertEqual(1, len(registry.champions()))
            champion = registry.champions()[0]
            self.assertEqual(digest, champion["candidate_sha256"])
            self.assertEqual(self.best["metrics"], champion["metrics"])
            self.assertEqual(str(self.output / "best-13.pt"), champion["checkpoint_path"])
            self.assertEqual(self.best["verification"], registry.verifications(digest)[0]["result"])

    def test_retained_candidate_digest_mismatch_is_refused(self):
        self.best["candidate_sha256"] = "0" * 64
        self.write_snapshot()
        with self.assertRaisesRegex(ValueError, "candidate digest"):
            legacy.convert(self.snapshot, self.output, self.db)

    def test_refuses_unknown_source_unstopped_and_inconsistent_progress(self):
        for change in ("source", "stopped", "continuity", "schema", "hash", "best"):
            with self.subTest(change=change):
                self.write_snapshot()
                if change == "source":
                    (self.snapshot / "gpu_worker.py").write_text("unsupported source")
                elif change in ("continuity", "schema"):
                    saved = copy.deepcopy(self.saved)
                    if change == "schema":
                        saved["schema"] = 42
                    else:
                        saved["progress"]["total_steps"] += 1
                    torch.save(saved, self.snapshot / "latest.pt")
                    marker = json.loads((self.snapshot / "stopped.json").read_text())
                    marker["checkpoint_sha256"] = hashlib.sha256((self.snapshot / "latest.pt").read_bytes()).hexdigest()
                    atomic_json(self.snapshot / "stopped.json", marker)
                elif change == "best":
                    (self.snapshot / "best-13.pt").write_bytes(b"not retained evidence")
                else:
                    marker = json.loads((self.snapshot / "stopped.json").read_text())
                    marker["stopped" if change == "stopped" else "checkpoint_sha256"] = False
                    atomic_json(self.snapshot / "stopped.json", marker)
                with self.assertRaises((ValueError, OSError)):
                    legacy.convert(self.snapshot, self.output, self.db)
                (self.snapshot / "gpu_worker.py").write_text("synthetic retained gpu_worker.py\n")

    def test_refuses_incompatible_model_or_optimizer_even_with_matching_evidence_hash(self):
        original = copy.deepcopy(self.saved)
        for change in ("model_shape", "moment_shape", "optimizer_step"):
            with self.subTest(change=change):
                self.saved = copy.deepcopy(original)
                self.write_snapshot()
                saved = copy.deepcopy(self.saved)
                if change == "model_shape":
                    saved["model"]["reflectors"] = torch.ones(1, 2)
                elif change == "moment_shape":
                    saved["optimizer"]["state"][0]["exp_avg"] = torch.ones(1)
                else:
                    saved["optimizer"]["state"][0]["step"] = torch.tensor(200.0)
                torch.save(saved, self.snapshot / "latest.pt")
                marker = json.loads((self.snapshot / "stopped.json").read_text())
                marker["checkpoint_sha256"] = hashlib.sha256((self.snapshot / "latest.pt").read_bytes()).hexdigest()
                atomic_json(self.snapshot / "stopped.json", marker)
                with self.assertRaisesRegex(ValueError, "model|optimizer|Adam"):
                    legacy.convert(self.snapshot, self.output, self.db)


if __name__ == "__main__":
    unittest.main()
