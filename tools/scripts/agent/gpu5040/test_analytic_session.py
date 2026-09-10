"""Finite analytic traversal, identity and durable recovery; no tensor allocation."""

import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from search_config import ALGORITHM, Config, load_initializer
from search_session import Campaign
from state_store import atomic_json
from trial_history import Registry
from test_trial_history import RUNTIME


RECIPE = Path(__file__).resolve().parents[4] / "Evidence/D5/S3/Quantum/AnalyticD55Initializer.result.json"


class AnalyticSessionTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.state = self.root / "state"
        self.state.mkdir()
        self.registry = Registry(self.root / "history.sqlite3")
        self.addCleanup(self.registry.close)
        self.config = Config(dimensions=(55,), seed_steps=2)
        self.spec = load_initializer(RECIPE)[0]

    def campaign(self, state=None, checkpoint=None, config=None, source="a" * 64, fresh=False):
        return Campaign(state or self.state, config or self.config, self.registry, RUNTIME,
                        checkpoint=checkpoint, fresh_start=fresh, initialization=self.spec,
                        provenance={"source_sha256": source})

    def metric(self, campaign):
        return {"fidelity": 0.4, "iteration": campaign.iteration}

    def finish(self, campaign):
        self.assertTrue(campaign.select())
        campaign.observe(self.metric(campaign))
        for _ in range(2):
            campaign.updated()
        campaign.observe(self.metric(campaign))
        return campaign.publish({}, atomic_json)

    def test_singleton_completion_and_skip_are_finite(self):
        campaign = self.campaign()
        saved = self.finish(campaign)
        self.assertEqual(0, campaign.seed)
        self.assertEqual(0, campaign.config.base_seed)
        self.assertTrue(campaign.exhausted)
        self.assertFalse(campaign.select())
        self.assertEqual(0, campaign.run_index)
        self.assertEqual(2, campaign.iteration)
        original = (self.state / "latest.pt").read_bytes()
        self.assertFalse(self.campaign(checkpoint=saved).select())
        self.assertEqual(original, (self.state / "latest.pt").read_bytes())
        other = self.root / "other"
        other.mkdir()
        changed_seed = copy.deepcopy(self.config)
        changed_seed.base_seed = 42
        skipped = self.campaign(state=other, config=changed_seed)
        self.assertFalse(skipped.select())
        self.assertTrue(skipped.exhausted)
        self.assertEqual(1, skipped.skipped_trials)
        self.assertEqual(0, skipped.total_steps)
        self.assertFalse((other / "latest.pt").exists())
        self.assertEqual(1, len(self.registry.rows()))

    def test_partial_owner_and_source_mismatch_before_reconciliation(self):
        campaign = self.campaign()
        campaign.select()
        campaign.updated()
        campaign.observe(self.metric(campaign))
        saved = campaign.publish({}, atomic_json, stopped=True)
        other = self.root / "other"
        other.mkdir()
        with self.assertRaisesRegex(ValueError, "owned|resume"):
            self.campaign(state=other).select()
        with self.assertRaisesRegex(ValueError, "unfinished|resume"):
            self.campaign(checkpoint=saved, fresh=True)
        with patch.object(self.registry, "mark", side_effect=AssertionError("must validate first")):
            with self.assertRaisesRegex(ValueError, "source|scientific|mismatch"):
                self.campaign(checkpoint=saved, source="b" * 64)
        resumed = self.campaign(checkpoint=saved)
        self.assertTrue(resumed.select())
        self.assertEqual(1, resumed.iteration)

    def test_terminal_failure_and_algorithm_mismatch_cannot_commit(self):
        campaign = self.campaign()
        with patch.object(self.registry, "complete", side_effect=OSError("injected publication failure")):
            with self.assertRaises(OSError):
                self.finish(campaign)
        campaign.fail("final handler")
        saved = json.loads((self.state / "latest.pt").read_text())
        with self.assertRaisesRegex(RuntimeError, "pending"):
            campaign.select()
        corrupt = copy.deepcopy(saved)
        corrupt["algorithm"] = ALGORITHM
        with self.assertRaisesRegex(ValueError, "algorithm|initializer"):
            self.campaign(checkpoint=corrupt)
        self.assertFalse(self.registry.completed(saved["trial"]["descriptor"]))
        recovered = self.campaign(checkpoint=saved)
        self.assertTrue(self.registry.completed(saved["trial"]["descriptor"]))
        self.assertFalse(recovered.select())


if __name__ == "__main__":
    unittest.main()
