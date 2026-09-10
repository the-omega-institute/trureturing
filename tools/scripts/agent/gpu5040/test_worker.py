"""Exercise the production worker loop with a synthetic CPU tensor fixture.

The fixture does no numerical optimization and never initializes Apple MPS.
"""

import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import torch

import gpu_worker as worker
from search_config import Config, descriptor
from trial_history import Registry
from test_trial_history import RUNTIME


class FixtureModel(torch.nn.Module):
    def __init__(self):
        super().__init__()
        self.value = torch.nn.Parameter(torch.tensor([0.2]))

    def forward(self):
        return torch.ones(4, 1, 1) / 2, self.value


class FixtureOptimizer:
    def __init__(self):
        self.state = {"step": 0, "moment": torch.tensor([0.0])}

    def state_dict(self):
        return self.state

    def load_state_dict(self, state):
        self.state = state


class SyntheticWorker(worker.Worker):
    def new_model(self):
        assert self.registry.get(self.campaign.trial["identity"])["status"] == "running"
        self.initializations.append((self.dimension, self.seed))
        self.model, self.optimizer = FixtureModel(), FixtureOptimizer()

    def initialize(self):
        self.initializations = []
        self.dp = lambda matrices, initial: initial
        self.new_model()
        saved = self.campaign.checkpoint
        if saved:
            self.model.load_state_dict(saved["model"])
            self.optimizer.load_state_dict(saved["optimizer"])
        self.campaign.checkpoint = None

    def train_step(self):
        with torch.no_grad():
            self.model.value.add_(0.1)
        self.optimizer.state["step"] += 1
        self.optimizer.state["moment"].add_(0.2)
        self.campaign.updated()


class WorkerTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="gpu5040-worker-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.state = self.root / "state"
        self.state.mkdir()
        self.registry = Registry(self.root / "history.sqlite3")
        self.addCleanup(self.registry.close)
        self.config = Config(dimensions=(13,), seed_steps=2, batch_steps=1)
        for target, kwargs in (("runtime_info", {"return_value": RUNTIME}),
                               ("torch.mps.get_rng_state", {"return_value": torch.tensor([7], dtype=torch.uint8)})):
            context = patch("gpu_worker." + target, **kwargs)
            context.start()
            self.addCleanup(context.stop)

    def create(self, steps=2, fresh=False, state=None):
        state = state or self.state
        args = worker.parser().parse_args(["--max-steps", str(steps)] + (["--fresh-start"] if fresh else []))
        saved = worker.load_checkpoint(state / "latest.pt", state) if (state / "latest.pt").exists() else None
        return SyntheticWorker(state, self.config, saved, worker.StopRequest(), args, self.registry)

    def run_worker(self, instance):
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            return instance.run()

    def test_worker_restart_fresh_and_new_state_skip_before_model_initialization(self):
        first = self.create()
        self.assertEqual(0, self.run_worker(first))
        self.assertEqual([(13, 5040)], first.initializations)
        second = self.create(fresh=True)
        self.assertEqual(0, self.run_worker(second))
        self.assertEqual([(13, 5041)], second.initializations)
        self.assertEqual(1, second.campaign.skipped_trials)
        third_state = self.root / "third"
        third_state.mkdir()
        third = self.create(steps=3, state=third_state)
        self.assertEqual(0, self.run_worker(third))
        self.assertEqual([(13, 5042), (13, 5043)], third.initializations)
        self.assertEqual(3, third.total_steps)
        self.assertEqual(2, third.campaign.skipped_trials)

    def test_worker_final_exception_retains_terminal_recovery_evidence(self):
        first = self.create()
        with patch.object(self.registry, "complete", side_effect=OSError("injected commit failure")):
            self.assertEqual(1, self.run_worker(first))
        saved = worker.load_checkpoint(self.state / "latest.pt", self.state)
        self.assertTrue(saved["trial"]["terminal"])
        self.assertEqual(2, saved["progress"]["iteration"])
        key = saved["trial"]["identity"]
        self.assertNotEqual("completed", self.registry.get(key)["status"])
        after = self.create(steps=1)
        self.assertEqual("completed", self.registry.get(key)["status"])
        self.assertEqual(0, self.run_worker(after))
        self.assertEqual([(13, 5041)], after.initializations)
        self.assertEqual("completed", self.registry.get(key)["status"])

    def test_interrupted_checkpoint_resumes_optimizer_and_fresh_start_refuses(self):
        first = self.create(steps=1)
        self.assertEqual(0, self.run_worker(first))
        before = (self.state / "latest.pt").read_bytes()
        with self.assertRaisesRegex(ValueError, "--resume"):
            self.create(fresh=True)
        self.assertEqual(before, (self.state / "latest.pt").read_bytes())
        second = self.create(steps=1)
        self.assertEqual(0, self.run_worker(second))
        self.assertEqual(2, second.optimizer.state["step"])
        self.assertAlmostEqual(0.4, float(second.optimizer.state["moment"]), places=6)
        self.assertAlmostEqual(0.4, float(second.model.value.detach()), places=6)

    def test_failed_update_does_not_overwrite_last_finite_checkpoint(self):
        first = self.create()
        with patch.object(first, "train_step", side_effect=FloatingPointError("synthetic failure")):
            self.assertEqual(1, self.run_worker(first))
        saved = worker.load_checkpoint(self.state / "latest.pt", self.state)
        self.assertEqual(0, saved["progress"]["iteration"])
        self.assertEqual("failed", self.registry.get(saved["trial"]["identity"])["status"])

    def test_stop_before_start_does_not_initialize_trial(self):
        first = self.create()
        first.stop.reason = "SIGTERM"
        self.assertEqual(0, self.run_worker(first))
        self.assertEqual([], self.registry.rows())
        self.assertFalse((self.state / "latest.pt").exists())

    def test_existing_stop_reports_zero_session_updates_and_keeps_optimizer(self):
        first = self.create(steps=2)
        self.assertEqual(0, self.run_worker(first))
        stopped = self.create()
        stopped.stop.reason = "STOP"
        self.assertEqual(0, self.run_worker(stopped))
        status = json.loads((self.state / "status.json").read_text())
        self.assertEqual("STOP", status["stop_reason"])
        self.assertEqual(0, status["session"]["completed_steps"])
        saved = worker.load_checkpoint(self.state / "latest.pt", self.state)
        self.assertEqual(2, saved["optimizer"]["step"])
        self.assertEqual(status["session"]["id"], saved["invocation"]["session_id"])

    def test_analytic_exact_budget_exhaustion_and_zero_allocation_skip(self):
        from search_config import load_initializer
        self.config = Config(dimensions=(55,), seed_steps=2, batch_steps=1)
        spec = load_initializer(Path(__file__).resolve().parents[4] /
            "Evidence/D5/S3/Quantum/AnalyticD55Initializer.result.json")[0]
        args = worker.parser().parse_args(["--initializer", "analytic-d55", "--max-steps", "2",
                                           "--device", "cpu", "--precision", "float64"])
        first = SyntheticWorker(self.state, self.config, None, worker.StopRequest(), args, self.registry)
        self.assertEqual(0, self.run_worker(first))
        self.assertEqual([(55, 0)], first.initializations)
        self.assertIsNone(args.initializer_recipe)
        self.assertEqual("cpu", str(first.device))
        self.assertEqual(str(Path(__file__).resolve().parents[4] /
                             "Evidence/D5/S3/Quantum/AnalyticD55Initializer.result.json"),
                         first.campaign.provenance["initializer_input"]["recipe_path"])
        status = json.loads((self.state / "status.json").read_text())
        self.assertEqual("exhausted", status["stop_reason"])
        self.assertEqual(2, status["session"]["completed_steps"])
        other = self.root / "other"
        other.mkdir()
        skipped = SyntheticWorker(other, self.config, None, worker.StopRequest(), args, self.registry)
        with patch.object(skipped, "initialize", side_effect=AssertionError("must skip before allocation")):
            self.assertEqual(0, self.run_worker(skipped))
        status = json.loads((other / "status.json").read_text())
        self.assertEqual("exhausted", status["stop_reason"])
        self.assertFalse(status["checkpoint_saved"])
        self.assertEqual(0, status["session"]["completed_steps"])
        self.assertEqual(spec, status["exhaustion"]["descriptor"]["initialization"])

    def test_scientific_source_hash_accounts_for_all_six_members(self):
        members = ("gpu_worker.py", "tensor_core.py", "search_config.py", "state_store.py",
                   "search_session.py", "trial_history.py")
        source = self.root / "scientific-source"
        source.mkdir()
        original = worker.source_hash()
        for name in members:
            (source / name).write_bytes((worker.ROOT / name).read_bytes())
        with patch.object(worker, "ROOT", source):
            self.assertEqual(original, worker.source_hash())
            for name in members:
                with self.subTest(member=name):
                    path = source / name
                    before = path.read_bytes()
                    path.write_bytes(before + b"\n")
                    self.assertNotEqual(original, worker.source_hash())
                    path.write_bytes(before)
            self.assertEqual(original, worker.source_hash())

    def test_source_mismatch_is_rejected_before_resume(self):
        first = self.create(steps=1)
        self.assertEqual(0, self.run_worker(first))
        with patch.object(worker, "source_hash", return_value="b" * 64):
            with self.assertRaisesRegex(ValueError, "source"):
                self.create(steps=1)
        saved = worker.load_checkpoint(self.state / "latest.pt", self.state)
        saved["migration_evidence"] = {"source_sha256": saved["source_sha256"]}
        worker.atomic_checkpoint(self.state / "latest.pt", saved)
        with patch.object(worker, "source_hash", return_value="b" * 64):
            with self.assertRaisesRegex(ValueError, "source"):
                self.create(steps=1)

    def test_analytic_fresh_skip_retains_checkpoint_without_mixing_progress(self):
        from gpu_bounded_launcher import read_status
        self.config = Config(dimensions=(55,), seed_steps=2, batch_steps=1)
        args = worker.parser().parse_args(["--initializer", "analytic-d55", "--max-steps", "2"])
        first = SyntheticWorker(self.state, self.config, None, worker.StopRequest(), args, self.registry)
        self.assertEqual(0, self.run_worker(first))
        original = (self.state / "latest.pt").read_bytes()
        saved = worker.load_checkpoint(self.state / "latest.pt", self.state)
        args.fresh_start = True
        fresh = SyntheticWorker(self.state, self.config, saved, worker.StopRequest(), args, self.registry)
        with patch.object(fresh, "initialize", side_effect=AssertionError("zero allocation skip")):
            self.assertEqual(0, self.run_worker(fresh))
        self.assertEqual(original, (self.state / "latest.pt").read_bytes())
        status = read_status(self.state)
        self.assertEqual(0, status["session"]["completed_steps"])
        self.assertEqual(1, status["progress"]["skipped_trials"])
        self.assertEqual(2, status["progress"]["traversal_start_steps"])
        self.assertFalse(status["checkpoint_saved"])
        self.assertIsNone(status["trial"])

    def test_analytic_best_identity_mismatch_is_rejected(self):
        self.config = Config(dimensions=(55,), seed_steps=2, batch_steps=1)
        args = worker.parser().parse_args(["--initializer", "analytic-d55", "--max-steps", "2"])
        first = SyntheticWorker(self.state, self.config, None, worker.StopRequest(), args, self.registry)
        self.assertEqual(0, self.run_worker(first))
        path = self.state / "best-55.pt"
        record = worker.load_checkpoint(path, self.state)
        record["trial_identity"] = "b" * 64
        worker.atomic_checkpoint(path, record)
        with self.assertRaisesRegex(ValueError, "identity"):
            worker.load_checkpoint(path, self.state)

    def test_analytic_forever_is_rejected_before_allocation(self):
        args = worker.parser().parse_args(["--initializer", "analytic-d55", "--forever"])
        with self.assertRaisesRegex(ValueError, "finite|forever"):
            SyntheticWorker(self.state, Config(dimensions=(55,)), None,
                            worker.StopRequest(), args, self.registry)


if __name__ == "__main__":
    unittest.main()
