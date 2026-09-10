"""Real D55 Adam persistence contract; CPU by default, MPS only by explicit opt-in."""

import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

import torch

HERE = Path(__file__).resolve().parent
RECIPE = HERE.parents[3] / "Evidence/D5/S3/Quantum/AnalyticD55Initializer.result.json"


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def compare(left, right):
    """Report every leaf comparison, including byte-exact tensor serialization."""
    rows = {}
    def walk(a, b, name):
        if isinstance(a, torch.Tensor):
            shape = isinstance(b, torch.Tensor) and a.shape == b.shape and a.dtype == b.dtype
            rows[name] = {"same_layout": shape,
                          "byte_exact": shape and a.numpy().tobytes() == b.numpy().tobytes(),
                          "max_abs": float((a.double() - b.double()).abs().max()) if shape else None}
        elif isinstance(a, dict):
            rows[name + "/keys"] = {"exact": isinstance(b, dict) and a.keys() == b.keys()}
            if rows[name + "/keys"]["exact"]:
                for key in a:
                    walk(a[key], b[key], name + "/" + str(key))
        elif isinstance(a, (list, tuple)):
            rows[name + "/length"] = {"exact": type(a) is type(b) and len(a) == len(b)}
            if rows[name + "/length"]["exact"]:
                for i, (x, y) in enumerate(zip(a, b)):
                    walk(x, y, name + "/" + str(i))
        else:
            rows[name] = {"exact": type(a) is type(b) and a == b}
    walk(left, right, "state")
    return rows


def child(state, output, count, resume, device):
    # No availability probe or device auto-selection. CPU never visits MPS RNG.
    torch.set_default_device("cpu")
    import gpu_worker as worker
    import tensor_core
    if device == "cpu":
        def guard(name):
            # Distinct callables preserve Torch's function-identity registry.
            def forbidden(*args, **kwargs):
                raise AssertionError("CPU experiment attempted " + name)
            return forbidden
        for name in ("manual_seed", "get_rng_state", "set_rng_state", "synchronize",
                     "set_per_process_memory_fraction", "current_allocated_memory",
                     "driver_allocated_memory", "recommended_max_memory"):
            setattr(torch.mps, name, guard("torch.mps." + name))
        torch.manual_seed = guard("torch.manual_seed")
        torch.backends.mps.is_available = guard("MPS availability probe")
    if resume:
        def regeneration_forbidden(*args, **kwargs):
            raise AssertionError("resume regenerated the initializer")
        tensor_core.analytic_physical = regeneration_forbidden

    observations = {"pid": os.getpid(), "device": device, "source_sha256": worker.source_hash(),
                    "recipe_raw_sha256": sha(RECIPE), "steps": []}
    class RecordingWorker(worker.Worker):
        def capture(self):
            with torch.no_grad():
                matrices, initial = self.model()
                target = self.dp(matrices, initial)
                return worker.to_cpu({
                    "model": self.model.state_dict(), "optimizer": self.optimizer.state_dict(),
                    "rng": {"torch_cpu": torch.get_rng_state(),
                            "torch_mps": torch.mps.get_rng_state() if device == "mps:0" else None},
                    "forward": {"matrices": matrices, "initial": initial, "target": target,
                                "fidelity": target.square().sum()},
                    "progress": self.campaign.progress(),
                    "lr": self.optimizer.param_groups[0]["lr"]})

        def initialize(self):
            super().initialize()
            observations["first"] = self.capture()

        def train_step(self):
            super().train_step()
            step = self.capture()
            step["gradients_finite"] = all(bool(torch.isfinite(p.grad).all())
                                            for p in self.model.parameters())
            observations["steps"].append(step)

    worker.Worker = RecordingWorker
    args = ["--state-dir", state, "--history-db", str(Path(state).parent / "history.sqlite3"),
            "--device", device, "--precision", "float64" if device == "cpu" else "float32",
            "--seed-steps", "6", "--batch-steps", "1", "--max-steps", str(count)]
    args += ["--resume"] if resume else ["--initializer", "analytic-d55", "--initializer-recipe", str(RECIPE)]
    code = worker.main(args)
    worker.atomic_checkpoint(Path(output), observations)
    return code


class RealAdamResumeTests(unittest.TestCase):
    def experiment(self, device):
        retained = os.environ.get("GPU5040_ADAM_EVIDENCE")
        if retained:
            root = Path(retained).resolve() / device.replace(":", "-")
            root.mkdir(parents=True, exist_ok=False)
        else:
            temporary = tempfile.TemporaryDirectory(prefix="gpu5040-real-adam-")
            self.addCleanup(temporary.cleanup)
            root = Path(temporary.name).resolve()
        for name in ("reference", "split"):
            (root / name).mkdir()
        commands = []
        def invoke(name, state, count, resume=False):
            output = root / (name + ".pt")
            command = [sys.executable, "-B", str(Path(__file__).resolve()), "--child",
                       str(root / state / "state"), str(output), str(count), str(int(resume)), device]
            env = {**os.environ, "PYTHONDONTWRITEBYTECODE": "1", "PYTORCH_ENABLE_MPS_FALLBACK": "0",
                   "GPU5040_SHARED_ROOT": str(root / "shared"), "VECLIB_MAXIMUM_THREADS": "1",
                   "OPENBLAS_NUM_THREADS": "1", "OMP_NUM_THREADS": "1", "MKL_NUM_THREADS": "1"}
            process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=env)
            try:
                stdout, stderr = process.communicate(timeout=90)
            except subprocess.TimeoutExpired:
                process.kill()
                stdout, stderr = process.communicate()
                raise
            finally:
                if process.poll() is None:
                    process.kill()
                    process.wait()
            (root / (name + ".stdout.log")).write_bytes(stdout)
            (root / (name + ".stderr.log")).write_bytes(stderr)
            commands.append({"argv": command, "pid": process.pid, "exit": process.returncode,
                             "test_sha256": sha(__file__), "recipe_sha256": sha(RECIPE),
                             "stdout_sha256": hashlib.sha256(stdout).hexdigest(),
                             "stderr_sha256": hashlib.sha256(stderr).hexdigest()})
            (root / "commands.json").write_text(json.dumps(commands, indent=2) + "\n")
            self.assertEqual(0, process.returncode, stderr.decode())
            return torch.load(output, map_location="cpu", weights_only=True)

        reference = invoke("six", "reference", 6)
        split = invoke("three", "split", 3)
        saved_path = root / "saved-after-three.pt"
        shutil.copyfile(root / "split/state/latest.pt", saved_path)
        saved = torch.load(saved_path, map_location="cpu", weights_only=True)
        resumed = invoke("reload-three", "split", 3, True)
        final = torch.load(root / "split/state/latest.pt", map_location="cpu", weights_only=True)
        reference_final = torch.load(root / "reference/state/latest.pt", map_location="cpu", weights_only=True)
        self.assertNotEqual(split["pid"], resumed["pid"])
        self.assertEqual(6, len(reference["steps"]))
        self.assertEqual(3, len(split["steps"]))
        self.assertEqual(3, len(resumed["steps"]))
        limit, objective_limit = ((1e-12, 5e-12) if device == "cpu" else (2e-6, 1e-5))
        readings = {"device": device, "tensor_ceiling": limit, "objective_ceiling": objective_limit,
                    "source_sha256": reference["source_sha256"], "commands": commands,
                    "saved_checkpoint_sha256": sha(saved_path),
                    "rng_scope": "CPU bytes; MPS not applicable and unexecuted" if device == "cpu"
                                 else "CPU and MPS bytes",
                    "saved_loaded": {}, "trajectory": [], "all_gradients_finite": True}
        for key in ("model", "optimizer", "rng"):
            readings["saved_loaded"][key] = compare(saved[key], resumed["first"][key])
        readings["first_reloaded_forward"] = compare(split["steps"][-1]["forward"], resumed["first"]["forward"])
        readings["first_vs_serialized_physical"] = compare(
            {key: saved[key] for key in ("matrices", "initial")},
            {key: resumed["first"]["forward"][key] for key in ("matrices", "initial")})
        readings["restored_progress"] = compare(
            {key: saved["progress"][key] for key in resumed["first"]["progress"]},
            resumed["first"]["progress"])
        for a, b in zip(reference["steps"], split["steps"] + resumed["steps"]):
            readings["trajectory"].append(compare(a, b))
            readings["all_gradients_finite"] &= a["gradients_finite"] and b["gradients_finite"]
        readings["final"] = {key: compare(reference_final[key], final[key])
                              for key in ("model", "optimizer", "rng", "matrices", "initial")}
        # Restore the actual trained best through the same fixed layout too.
        from gpu_worker import load_checkpoint
        from tensor_core import RealIsometry
        best = load_checkpoint(root / "split/state/best-55.pt", root / "split/state")
        dtype = torch.float64 if device == "cpu" else torch.float32
        model = RealIsometry(55, torch.device(device), dtype, restore=True)
        model.load_state_dict(best["model"])
        with torch.no_grad():
            matrices, initial = model()
        readings["best_restoration"] = compare(
            {key: best[key] for key in ("matrices", "initial")},
            {"matrices": matrices.cpu(), "initial": initial.cpu()})
        readings["startup_first_forward"] = json.loads((root / "split/state/startup.json").read_text())["first_forward"]
        readings["final_status"] = json.loads((root / "split/state/status.json").read_text())
        (root / "readings.json").write_text(json.dumps(readings, indent=2, allow_nan=False) + "\n")

        def accept(rows, exact=False):
            for name, row in rows.items():
                if "exact" in row:
                    self.assertTrue(row["exact"], name)
                else:
                    self.assertTrue(row["same_layout"], name)
                    if exact or name.endswith("/step") or "/rng/" in name:
                        self.assertTrue(row["byte_exact"], name)
                    self.assertLessEqual(row["max_abs"], objective_limit if "fidelity" in name else limit, name)
        self.assertTrue(readings["all_gradients_finite"])
        for rows in readings["saved_loaded"].values():
            accept(rows, exact=True)
        for key in ("first_reloaded_forward", "first_vs_serialized_physical", "restored_progress", "best_restoration"):
            accept(readings[key])
        for rows in readings["trajectory"] + list(readings["final"].values()):
            accept(rows)
        self.assertEqual(saved["optimizer"]["param_groups"], resumed["first"]["optimizer"]["param_groups"])
        self.assertEqual(reference_final["trial"]["identity"], final["trial"]["identity"])
        self.assertEqual(reference["source_sha256"], resumed["source_sha256"])
        self.assertEqual("exhausted", readings["final_status"]["stop_reason"])
        self.assertEqual(3, readings["final_status"]["session"]["completed_steps"])
        self.assertEqual(3, readings["final_status"]["session"]["gradients"]["count"])
        self.assertTrue(readings["final_status"]["session"]["gradients"]["all_finite"])

    def test_cpu_float64_real_adam_new_process(self):
        self.experiment("cpu")

    @unittest.skipUnless(os.environ.get("GPU5040_RUN_MPS") == "1", "actual MPS requires explicit root handoff")
    def test_mps_float32_real_adam_new_process(self):
        self.experiment("mps:0")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "--child":
        sys.exit(child(sys.argv[2], sys.argv[3], int(sys.argv[4]), bool(int(sys.argv[5])), sys.argv[6]))
    unittest.main()
