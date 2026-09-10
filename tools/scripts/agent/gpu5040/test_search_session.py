import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from search_config import Config, descriptor
from search_session import Campaign
from state_store import atomic_json
from trial_history import Registry
from test_trial_history import RUNTIME


class SessionTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="gpu5040-session-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.state = self.root / "state"
        self.state.mkdir()
        self.registry = Registry(self.root / "history.sqlite3")
        self.addCleanup(self.registry.close)
        self.config = Config(dimensions=(13,), seed_steps=2)

    def campaign(self, state=None, checkpoint=None, fresh=False, config=None):
        return Campaign(state or self.state, config or self.config, self.registry, RUNTIME,
                        checkpoint=checkpoint, fresh_start=fresh, provenance={"source": "test"})

    def metric(self, campaign, fidelity):
        return {"fidelity": fidelity, "iteration": campaign.iteration,
                "gram_max_abs_error": 0.0001, "initial_norm_squared": 1.0}

    def publish(self, campaign, stopped=False):
        checkpoint = {"model": {"h": [1, 2]}, "optimizer": {"step": campaign.iteration},
                      "rng": {"cpu": [3], "mps": [4]}}
        return campaign.publish(checkpoint, atomic_json, stopped=stopped)

    def finish_trial(self, campaign):
        self.assertTrue(campaign.select())
        campaign.observe(self.metric(campaign, 0.3))
        campaign.updated()
        campaign.observe(self.metric(campaign, 0.6))
        campaign.updated()
        campaign.observe(self.metric(campaign, 0.4))
        self.publish(campaign, stopped=True)

    def load(self, state=None):
        return json.loads(((state or self.state) / "latest.pt").read_text())

    def test_completed_restart_fresh_start_and_new_state_skip_before_initialization(self):
        first = self.campaign()
        self.finish_trial(first)
        key = first.trial["identity"]
        restarted = self.campaign(checkpoint=self.load())
        self.assertTrue(restarted.select())
        self.assertEqual(1, restarted.run_index)
        self.assertEqual(2, restarted.total_steps)
        self.assertEqual("completed", self.registry.get(key)["status"])
        # Remove the new claim before testing another traversal of the same prefix.
        self.registry.mark(restarted.trial["identity"], "interrupted")
        fresh = self.campaign(checkpoint=self.load(), fresh=True)
        self.assertTrue(fresh.select())
        self.assertEqual(1, fresh.run_index)
        self.assertEqual(1, fresh.skipped_trials)
        self.assertEqual(2, fresh.total_steps)
        other = self.root / "other"
        other.mkdir()
        # A different campaign cannot steal the unfinished second trial.
        with self.assertRaisesRegex(ValueError, "resume|owned"):
            self.campaign(state=other).select()
        self.finish_trial(fresh)
        new = self.campaign(state=other)
        self.assertTrue(new.select())
        self.assertEqual(2, new.run_index)
        self.assertEqual(2, new.skipped_trials)
        self.assertEqual(0, new.total_steps)

    def test_partial_is_interrupted_fresh_rejected_and_optimizer_rng_retained(self):
        campaign = self.campaign()
        campaign.select()
        campaign.observe(self.metric(campaign, 0.1))
        campaign.updated()
        campaign.observe(self.metric(campaign, 0.2))
        self.publish(campaign, stopped=True)
        saved = self.load()
        self.assertEqual("interrupted", self.registry.get(campaign.trial["identity"])["status"])
        original = (self.state / "latest.pt").read_bytes()
        with self.assertRaisesRegex(ValueError, "--resume"):
            self.campaign(checkpoint=saved, fresh=True)
        self.assertEqual(original, (self.state / "latest.pt").read_bytes())
        restored = self.campaign(checkpoint=saved)
        self.assertTrue(restored.select())
        self.assertEqual(1, restored.iteration)
        self.assertEqual(saved["optimizer"], restored.checkpoint["optimizer"])
        self.assertEqual(saved["rng"], restored.checkpoint["rng"])
        restored.updated()
        restored.observe(self.metric(restored, 0.15))
        self.publish(restored)
        summary = self.registry.get(restored.trial["identity"])["summary"]
        self.assertEqual(0.1, summary["initial"]["fidelity"])
        self.assertEqual(0.15, summary["final"]["fidelity"])
        self.assertEqual(0.2, summary["best"]["fidelity"])
        self.assertEqual(1, summary["best"]["iteration"])

    def test_initialization_claim_exists_before_any_checkpoint(self):
        campaign = self.campaign()
        campaign.select()
        self.assertEqual("running", self.registry.get(campaign.trial["identity"])["status"])
        self.assertFalse((self.state / "latest.pt").exists())
        campaign.fail("initialization failed")
        self.assertEqual("failed", self.registry.get(campaign.trial["identity"])["status"])
        replacement = self.campaign()
        replacement.select()
        self.assertEqual(0, replacement.iteration)

    def test_trial_local_best_is_not_dimension_champion(self):
        self.registry.champion(13, "c" * 64, {"fidelity": 0.99}, "/retained/best.pt")
        campaign = self.campaign()
        self.finish_trial(campaign)
        self.assertEqual(0.6, self.registry.get(campaign.trial["identity"])["summary"]["best"]["fidelity"])
        self.assertEqual(0.99, self.registry.champions()[0]["metrics"]["fidelity"])

    def test_checkpoint_fsync_precedes_completion_and_guard_survives_error_handler(self):
        campaign = self.campaign()
        campaign.select()
        campaign.observe(self.metric(campaign, 0.1))
        self.publish(campaign)
        campaign.updated()
        campaign.updated()
        campaign.observe(self.metric(campaign, 0.3))
        order = []
        import state_store
        fsync = state_store.os.fsync

        def synced(fd):
            order.append("fsync")
            return fsync(fd)

        def fail_commit(*args):
            order.append("complete")
            self.assertTrue(self.load()["trial"]["terminal"])
            raise OSError("injected completion transaction failure")

        with patch.object(state_store.os, "fsync", side_effect=synced), patch.object(
                self.registry, "complete", side_effect=fail_commit):
            with self.assertRaisesRegex(OSError, "injected"):
                self.publish(campaign)
        self.assertEqual(["fsync", "fsync", "complete"], order)
        terminal = (self.state / "latest.pt").read_bytes()
        campaign.fail("final exception handler")
        self.assertEqual(terminal, (self.state / "latest.pt").read_bytes())
        with self.assertRaisesRegex(RuntimeError, "terminal|completion"):
            self.publish(campaign)
        self.assertFalse(self.registry.completed(campaign.trial["descriptor"]))
        recovered = self.campaign(checkpoint=self.load(), fresh=True)
        self.assertTrue(self.registry.completed(campaign.trial["descriptor"]))
        self.assertTrue(recovered.select())
        self.assertEqual(1, recovered.run_index)

    def test_failure_before_terminal_publish_cannot_commit_completion(self):
        campaign = self.campaign()
        campaign.select()
        campaign.observe(self.metric(campaign, 0.1))
        self.publish(campaign)
        original = (self.state / "latest.pt").read_bytes()
        campaign.updated()
        campaign.updated()
        campaign.observe(self.metric(campaign, 0.3))
        with self.assertRaises(OSError):
            campaign.publish({}, lambda *args: (_ for _ in ()).throw(OSError("disk full")))
        campaign.fail("disk full")
        self.assertEqual(original, (self.state / "latest.pt").read_bytes())
        self.assertFalse(self.registry.completed(campaign.trial["descriptor"]))

    def test_completion_commit_then_crash_reconciles_idempotently(self):
        campaign = self.campaign()
        campaign.select()
        campaign.observe(self.metric(campaign, 0.1))
        campaign.updated()
        campaign.updated()
        campaign.observe(self.metric(campaign, 0.2))
        complete = self.registry.complete

        def commit_then_crash(*args):
            complete(*args)
            raise OSError("crash after commit")

        with patch.object(self.registry, "complete", side_effect=commit_then_crash):
            with self.assertRaises(OSError):
                self.publish(campaign)
        campaign.fail("crash after commit")
        self.assertTrue(self.registry.completed(campaign.trial["descriptor"]))
        recovered = self.campaign(checkpoint=self.load())
        self.assertTrue(recovered.select())
        self.publish(recovered)
        self.assertFalse(self.load()["trial"]["terminal"])
        self.assertTrue(self.registry.completed(campaign.trial["descriptor"]))

    def test_operational_changes_resume_but_scientific_changes_require_new_traversal(self):
        campaign = self.campaign()
        campaign.select()
        campaign.observe(self.metric(campaign, 0.1))
        self.publish(campaign, stopped=True)
        cosmetic = copy.deepcopy(self.config)
        cosmetic.batch_steps = 1
        self.assertTrue(self.campaign(checkpoint=self.load(), config=cosmetic).select())
        changed = copy.deepcopy(self.config)
        changed.learning_rate = 0.02
        with self.assertRaisesRegex(ValueError, "scientific|mismatch"):
            self.campaign(checkpoint=self.load(), config=changed)

    def test_skips_do_not_consume_additional_update_budget(self):
        first = self.campaign()
        self.finish_trial(first)
        state = self.root / "new"
        state.mkdir()
        next_run = self.campaign(state=state)
        next_run.select()
        self.assertEqual(1, next_run.skipped_trials)
        self.assertEqual(0, next_run.total_steps)
        for _ in range(2):
            next_run.updated()
        self.assertEqual(2, next_run.total_steps)
        self.assertEqual(1, next_run.run_index)
        self.assertEqual(2, next_run.iteration)

    def test_inconsistent_scientific_checkpoint_cannot_reconcile_completion(self):
        campaign = self.campaign()
        campaign.select()
        campaign.updated()
        campaign.updated()
        campaign.observe(self.metric(campaign, 0.2))
        with patch.object(self.registry, "complete", side_effect=OSError("crash")):
            with self.assertRaises(OSError):
                self.publish(campaign)
        saved = self.load()
        saved["config"]["learning_rate"] = 0.02
        with self.assertRaisesRegex(ValueError, "scientific|descriptor"):
            self.campaign(checkpoint=saved, fresh=True)
        self.assertFalse(self.registry.completed(campaign.trial["descriptor"]))


if __name__ == "__main__":
    unittest.main()
