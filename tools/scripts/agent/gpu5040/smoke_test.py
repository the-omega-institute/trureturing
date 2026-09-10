#!/usr/bin/env python3
"""Bounded numerical checks; --mps explicitly enables real GPU integration checks."""

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from state_store import external_path


def mps_checks():
    import torch
    from gpu_worker import load_checkpoint

    root = Path(__file__).resolve().parent
    commands = []

    def command(state, history, *arguments, expected=0, program="gpu_worker.py"):
        argv = [sys.executable, "-B", str(root / program), "--state-dir", str(state),
                "--history-db", str(history), *arguments]
        result = subprocess.run(argv, capture_output=True, text=True, timeout=180)
        commands.append({"argv": argv, "exit": result.returncode})
        if result.returncode != expected:
            raise AssertionError({"command": commands[-1], "stdout": result.stdout, "stderr": result.stderr})
        return json.loads((state / "status.json").read_text())

    settings = ("--dimensions", "13", "--seed-steps", "6", "--batch-steps", "1")
    with tempfile.TemporaryDirectory(prefix="gpu5040-mps-smoke-") as temporary:
        scratch = external_path(temporary)
        resumed, continuous, fresh = (scratch / name for name in ("resumed", "continuous", "fresh"))
        history = scratch / "history.sqlite3"
        first = command(resumed, history, *settings, "--max-steps", "3")
        assert first["runtime"]["actual_device"] == "mps:0"
        assert first["device_evidence"]["parameters"] == ["mps:0"]
        command(resumed, history, "--fresh-start", "--max-steps", "1", expected=2)
        second = command(resumed, history, "--resume", "--max-steps", "3")
        assert second["session"]["completed_steps"] == 3
        reference_db = scratch / "independent-reference.sqlite3"
        command(continuous, reference_db, *settings, "--max-steps", "6")
        actual = load_checkpoint(resumed / "latest.pt", resumed)
        reference = load_checkpoint(continuous / "latest.pt", continuous)
        model_error = max(float((value - reference["model"][name]).abs().max())
                          for name, value in actual["model"].items())
        moment_error = max(float((value[name] - reference["optimizer"]["state"][key][name]).abs().max())
                           for key, value in actual["optimizer"]["state"].items()
                           for name in ("exp_avg", "exp_avg_sq"))
        assert model_error < 2e-6 and moment_error < 2e-6
        assert all(torch.equal(actual["rng"][key], reference["rng"][key]) for key in actual["rng"])
        command(resumed, history, "--verify", "13")
        traversed = command(resumed, history, "--fresh-start", "--max-steps", "6")
        assert traversed["progress"]["skipped_trials"] == 1
        assert traversed["session"]["completed_steps"] == 6
        new = command(fresh, history, *settings, "--max-steps", "6")
        assert new["progress"]["skipped_trials"] == 2
        assert new["progress"]["seed"] == 5042
        terminal = command(fresh, history, program="gpu_bounded_launcher.py")
        assert terminal["session"]["completed_steps"] == 6
    return {"commands": commands, "model_resume_error": model_error,
            "adam_moment_resume_error": moment_error, "rng_equal": True,
            "temporary_states_removed": True}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mps", action="store_true", help="requires all older GPU workers to be paused")
    args = parser.parse_args(argv)
    os.environ.setdefault("PYTORCH_ENABLE_MPS_FALLBACK", "0")
    for name in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS"):
        os.environ.setdefault(name, "1")
    import test_numerics
    suite = unittest.defaultTestLoader.loadTestsFromModule(test_numerics)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    if not result.wasSuccessful():
        return 1
    report = {"cpu_tests": result.testsRun, "mps": "not requested"}
    if args.mps:
        report["mps"] = mps_checks()
    print(json.dumps(report, indent=2, allow_nan=False))
    return 0


if __name__ == "__main__":
    sys.exit(main())
