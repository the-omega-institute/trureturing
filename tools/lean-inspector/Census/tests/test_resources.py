"""Functional subprocess results are independent of resource observations."""

import json
import pathlib
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

import resources


class FunctionalExecutionTests(unittest.TestCase):
    def test_functional_memory_observations_do_not_change_result(self):
        with tempfile.TemporaryDirectory() as temporary:
            outcomes = []
            for free in (29, 83):
                with self.subTest(free=free), mock.patch.object(resources, "free_memory", return_value=free):
                    result = resources.run([sys.executable, "-c", "print('valid functional result')"],
                                           temporary, f"memory-{free}", budget_gb=None)
                    outcomes.append((result["status"], result["exit_code"],
                                     (pathlib.Path(temporary) / f"memory-{free}.log").read_text()))
            self.assertEqual(outcomes, [("completed", 0, "valid functional result\n")] * 2)

    def test_functional_missing_memory_observation_does_not_reject(self):
        with tempfile.TemporaryDirectory() as temporary, mock.patch.object(
                resources, "free_memory", side_effect=OSError("memory observation unavailable")):
            result = resources.run([sys.executable, "-c", "print('valid')"], temporary,
                                   "unavailable", budget_gb=None)
            self.assertEqual(result["exit_code"], 0)
            self.assertIn("memory observation unavailable", json.dumps(result))

    def test_functional_nonzero_command_is_propagated(self):
        with tempfile.TemporaryDirectory() as temporary, mock.patch.object(resources, "free_memory", return_value=29):
            with self.assertRaisesRegex(RuntimeError, "command exited 7"):
                resources.run([sys.executable, "-c", "print('command failed'); raise SystemExit(7)"],
                              temporary, "failed", budget_gb=None)
            self.assertEqual(json.loads((pathlib.Path(temporary) / "failed.resources.json").read_text())["exit_code"], 7)
            self.assertIn("command failed", (pathlib.Path(temporary) / "failed.log").read_text())

    def test_functional_hang_guard_is_infrastructure_and_reaps_child(self):
        # Inject elapsed time at the execution boundary; machine speed is not an assertion.
        processes = []
        start = subprocess.Popen
        def launch(*args, **kwargs):
            process = start(*args, **kwargs)
            processes.append(process)
            return process
        with tempfile.TemporaryDirectory() as temporary, mock.patch.object(
                resources, "free_memory", return_value=83), mock.patch.object(
                resources.time, "monotonic", side_effect=[0, 1201, 1201, 1201]), mock.patch.object(
                resources.subprocess, "Popen", side_effect=launch):
            with self.assertRaisesRegex(RuntimeError, "infrastructure-hang-guard expired"):
                resources.run([sys.executable, "-c", "print('valid')"], temporary, "hang", budget_gb=None)
            self.assertTrue(processes)
            self.assertTrue(all(process.poll() is not None for process in processes))
            result = json.loads((pathlib.Path(temporary) / "hang.resources.json").read_text())
            self.assertEqual(result["status"], "infrastructure-unresolved")

    def test_workload_memory_acceptance_is_retained(self):
        with tempfile.TemporaryDirectory() as temporary, mock.patch.object(resources, "free_memory", return_value=29):
            with self.assertRaisesRegex(resources.ResourceRejected, "free memory"):
                resources.run([sys.executable, "-c", "raise AssertionError('must not start')"], temporary, "workload")


if __name__ == "__main__":
    unittest.main()
