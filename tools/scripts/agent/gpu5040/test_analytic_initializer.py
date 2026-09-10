"""Analytic physical input and fixed-eye codec contracts; CPU only."""

import copy
import hashlib
import json
import math
import itertools
import os
from pathlib import Path
import tempfile
import unittest

import torch
import numpy as np

from search_config import (Config, analytic_initializer, descriptor, identity,
                           load_initializer, protocol_initializer, validate_initializer, ALGORITHM)
from tensor_core import (OccupationDP, RealIsometry, analytic_physical,
                         encode_physical, enumerated_chunks, householder_frame,
                         verify_full_output)
from test_trial_history import RUNTIME


RECIPE = Path(__file__).resolve().parents[4] / "Evidence/D5/S3/Quantum/AnalyticD55Initializer.result.json"


class AnalyticTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        torch.set_num_threads(1)

    def spec(self):
        return load_initializer(RECIPE)[0]

    def test_content_relocation_and_unused_seed_identity(self):
        spec, provenance = load_initializer(RECIPE)
        raw = RECIPE.read_bytes()
        # Raw identity from StructuredCanonicalWriter.WriteJson; content is separate.
        self.assertEqual(1467, len(raw))
        self.assertEqual("fbbaee8c55cd098d7c298283b9496ae9ff85be835ea2adce5e90220fd9f3cd68",
                         provenance["recipe_raw_sha256"])
        self.assertEqual(hashlib.sha256(raw).hexdigest(), provenance["recipe_raw_sha256"])
        self.assertEqual(raw.decode("utf-8"), provenance["recipe_raw_utf8"])
        self.assertEqual(str(RECIPE.resolve()), provenance["recipe_path"])
        self.assertEqual("f22c900bd1482a55fb7a8294f4e164fde99c38bd7feaa80caf6af23ae41c44af",
                         spec["recipe_sha256"])
        self.assertEqual(spec["recipe_sha256"], identity(json.loads(raw)))
        with tempfile.TemporaryDirectory() as temporary:
            relocated = Path(temporary) / "relocated.json"
            relocated.write_bytes(raw)
            relocated_spec, relocated_provenance = load_initializer(relocated)
            self.assertEqual(spec, relocated_spec)
            self.assertEqual(provenance["recipe_raw_sha256"], relocated_provenance["recipe_raw_sha256"])
            self.assertEqual(provenance["recipe_raw_utf8"], relocated_provenance["recipe_raw_utf8"])
            self.assertNotEqual(provenance["recipe_path"], load_initializer(relocated)[1]["recipe_path"])
        config = Config(dimensions=(55,))
        one = descriptor(config, 55, 5040, RUNTIME, spec, "a" * 64)
        two = descriptor(config, 55, 42, RUNTIME, spec, "a" * 64)
        self.assertEqual(one, two)
        self.assertEqual(0, one["seed"])
        self.assertNotEqual(identity(one), identity(descriptor(config, 55, 0, RUNTIME, spec, "b" * 64)))
        recipe = copy.deepcopy(spec["recipe"])
        recipe["rotation"]["entries"][0][2] = "1"
        with self.assertRaisesRegex(ValueError, "recipe|candidate"):
            analytic_initializer(recipe)
        recipe = copy.deepcopy(spec["recipe"])
        recipe["perturbation"] = "random"
        with self.assertRaisesRegex(ValueError, "recipe|candidate"):
            analytic_initializer(recipe)

    def test_physical_bytes_and_float64_reconstruction(self):
        matrices, initial = analytic_physical(self.spec())
        self.assertEqual("cpu", str(matrices.device))
        # Retained physical bytes are an input oracle, never an executed checker.
        self.assertEqual("942e9d38fafb5d3252be9876f09721b48209f2fb841812eb6218b180e6b0478f",
                         hashlib.sha256(matrices.numpy().tobytes()).hexdigest())
        self.assertEqual("731fe20b2603f243d0a5215223917d3c0ef1f842858a31ff35e427ce6c4defb8",
                         hashlib.sha256(initial.numpy().tobytes()).hexdigest())
        before = torch.get_rng_state().clone()
        reflectors = encode_physical(matrices, initial)
        self.assertTrue(torch.equal(before, torch.get_rng_state()))
        self.assertEqual((55, 220), tuple(reflectors.shape))
        self.assertTrue(bool((reflectors.square().sum(1) > 0).all()))
        reconstructed = householder_frame(reflectors).reshape(4, 55, 55)
        self.assertLessEqual(float((reconstructed - matrices).abs().max()), 2e-13)
        model = RealIsometry(55, "cpu", torch.float64, initialization=self.spec())
        self.assertTrue(torch.equal(before, torch.get_rng_state()))
        self.assertEqual({"reflectors", "initial"}, set(model.state_dict()))
        self.assertTrue(torch.equal(initial, model.initial.detach()))
        with torch.no_grad():
            actual, vector = model()
        self.assertLessEqual(float((actual - matrices).abs().max()), 2e-13)
        self.assertLessEqual(float((vector - initial).abs().max()), 2e-13)
        fidelity = float(OccupationDP(device="cpu")(actual, vector).square().sum())
        self.assertLessEqual(abs(fidelity - 44028789605 / 44149689864), 5e-12)

    def test_malformed_metadata_is_rejected(self):
        for malformed in ([], "analytic-d55", 55, {"recipe": []}):
            with self.assertRaises(ValueError):
                validate_initializer(malformed)
        desc = descriptor(Config(dimensions=(55,)), 55, 0, RUNTIME, self.spec(), "a" * 64)
        with self.assertRaisesRegex(ValueError, "algorithm"):
            protocol_initializer(desc, ALGORITHM)
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "duplicate.json"
            path.write_text('{"schema":1,"schema":1}')
            with self.assertRaisesRegex(ValueError, "duplicate"):
                load_initializer(path)

    def test_precision_contract_and_physical_controls(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(os.environ.get("GPU5040_NUMERICAL_EVIDENCE", temporary))
            report = numerical_evidence(directory, self.spec())
        self.assertEqual([], report["failed_criteria"], report)

    def test_neutral_and_near_aligned_columns_and_invalid_input(self):
        initial = torch.tensor([1., 0.], dtype=torch.float64, device="cpu")
        frame = torch.eye(8, 2, dtype=torch.float64, device="cpu")
        for angle in (0., 1e-10, 0.3):
            rotated = frame.clone()
            rotated[0, 0], rotated[3, 0] = math.cos(angle), math.sin(angle)
            encoded = encode_physical(rotated.reshape(4, 2, 2), initial)
            self.assertLessEqual(float((householder_frame(encoded) - rotated).abs().max()), 2e-13)
        for matrices, vector in ((frame.reshape(4, 2, 2) * 1.001, initial),
                                 (frame.reshape(4, 2, 2), initial * 1.001)):
            with self.assertRaisesRegex(ValueError, "Gram|norm"):
                encode_physical(matrices, vector)


def numerical_evidence(directory, spec):
    """Current-code readings against the retained, explicit full-word formula."""
    directory.mkdir(parents=True, exist_ok=True)
    a, v = analytic_physical(spec)
    words = list(itertools.product(range(4), repeat=8))
    legal = np.asarray([tuple(w.count(i) for i in range(4)) == (4, 2, 1, 1) for w in words])
    p = set(itertools.permutations((1, 1, 2)))
    u = {w for w in set(itertools.permutations((0, 1, 1, 2))) if w[-1] != 0}
    affected = {w + (0, 0, 0, 3, 0) for w in p} | {w + (0, 0, 0, 3) for w in u}
    restored = {w + (0, 0, 0, 0, 3) for w in p}
    leak_p = {w + (0, 0, 0, 0, 0) for w in p}
    leak_u = {w + (0, 0, 0, 0) for w in u}

    def formula(c, s):
        result = np.zeros((65536, 55), dtype=np.float64)
        for i, w in enumerate(words):
            if legal[i]:
                result[i, 0] = s * c if w in restored else c if w in affected else 1
            elif w in leak_p or w in leak_u:
                factor = s ** 2 if w in leak_p else s
                result[i, 1:5] = factor * np.array([c, c*s, c*s*s, s**3])
        return result / math.sqrt(837)

    limits64 = dict(frame=2e-13, initial=2e-13, gram=2e-13, initial_norm=2e-13,
                    target=5e-12, amplitudes=2e-13, output_norm=5e-12,
                    fidelity=5e-12, dp_full=5e-12, forbidden=5e-12)
    limits32 = dict(frame=2e-5, initial=2e-6, gram=5e-5, initial_norm=5e-6,
                    target=5e-5, amplitudes=2e-5, output_norm=1e-4,
                    fidelity=1e-4, dp_full=1e-4, forbidden=1e-5)
    report = {"device": "cpu", "actual_mps": "unexecuted; root-owned handoff outstanding",
              "rows": {}, "controls": {}, "failed_criteria": []}

    def retain(name, matrices, initial):
        result = {}
        for key, tensor in (("matrices", matrices), ("initial", initial)):
            array = tensor.detach().cpu().numpy()
            path = directory / (name + "." + key + ".bin")
            with path.open("xb") as stream:
                stream.write(array.tobytes())
            path.chmod(0o444)
            result[key] = {"path": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                           "shape": list(array.shape), "dtype": array.dtype.str, "order": "C"}
        return result

    def measure(name, matrices, initial, physical, expected, limits):
        artifacts = retain(name, matrices, initial)
        full = verify_full_output(matrices.numpy(), initial.numpy(), chunk_size=256)
        actual = np.concatenate([block for block, _ in enumerated_chunks(
            matrices.numpy().astype(np.float64), initial.numpy().astype(np.float64), (4, 2, 1, 1), 256)])
        target = OccupationDP(device="cpu")(matrices, initial).numpy()
        expected_target = expected[legal].sum(0) / math.sqrt(840)
        expected_fidelity = float(expected_target @ expected_target)
        errors = {"frame": float((matrices.double() - physical).abs().max()),
                  "initial": float((initial.double() - v).abs().max()),
                  "gram": full["gram_max_abs_error"],
                  "initial_norm": abs(float(initial.double().square().sum()) - 1),
                  "target": float(np.max(np.abs(target - expected_target))),
                  "amplitudes": float(np.max(np.abs(actual - expected))),
                  "output_norm": abs(full["norm_squared"] - 1),
                  "fidelity": max(abs(full["target_fidelity"] - expected_fidelity),
                                  abs(float(target @ target) - expected_fidelity)),
                  "dp_full": abs(float(target @ target) - full["target_fidelity"]),
                  "forbidden": abs(full["forbidden_leakage_squared"] - float(np.square(expected[~legal]).sum()))}
        indexed = {word: {"actual": actual[int(word, 4)].tolist(),
                          "expected": expected[int(word, 4)].tolist()}
                   for word in ("11200003", "30000211")}
        report["rows"][name] = {"errors": errors, "ceilings": limits, "verifier": full,
                                 "dp_fidelity": float(target @ target), "indexed_words": indexed,
                                 "physical_artifacts": artifacts}
        for quantity, error in errors.items():
            if not math.isfinite(error) or error > limits[quantity]:
                report["failed_criteria"].append(name + "." + quantity)

    expected = formula(40/41, 9/41)
    measure("raw-float64", a, v, a, expected, limits64)
    reflectors = encode_physical(a, v)
    path = directory / "reflectors.float64.bin"
    path.write_bytes(reflectors.numpy().tobytes())
    path.chmod(0o444)
    report["reflectors"] = {"path": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                            "shape": [55, 220], "dtype": "<f8", "order": "C"}
    for dtype in (torch.float64, torch.float32):
        with torch.no_grad():
            model = RealIsometry(55, "cpu", dtype, initialization=spec)
            matrices, initial = model()
        measure("reconstructed-" + str(dtype).split(".")[-1], matrices, initial, a,
                expected, limits64 if dtype == torch.float64 else limits32)
    measure("cast-only-float32", a.float(), v.float(), a, expected, limits32)
    for name, c, s in (("baseline", 1., 0.), ("signed-phase", 40/41, -9/41),
                       ("invalid", 1., 9/41), ("rational-gauge-as-physical", 40/41, 9/41)):
        control = a.clone()
        control[0, 3, 4], control[0, 4, 4] = c, s
        if name == "rational-gauge-as-physical":
            for column in range(55):
                if column != 4:
                    control[:, :, column][control[:, :, column] != 0] = 1.
        artifacts = retain(name, control, v)
        full = verify_full_output(control.numpy(), v.numpy())
        if name in ("baseline", "signed-phase"):
            measure(name + "-reconstructed", householder_frame(encode_physical(control, v)).reshape(4, 55, 55),
                    v, control, formula(c, s), limits64)
        else:
            try:
                encode_physical(control, v)
                rejection = None
                report["failed_criteria"].append(name + ".must_reject_invalid_Gram")
            except ValueError as error:
                rejection = str(error)
            if full["gram_max_abs_error"] <= 2e-13 or abs(full["norm_squared"] - 1) <= 5e-12:
                report["failed_criteria"].append(name + ".control_detection")
        report["controls"][name] = {"verifier": full, "physical_artifacts": artifacts,
                                    "encoder_rejection": rejection if name in ("invalid", "rational-gauge-as-physical") else None}
    if not (report["controls"]["signed-phase"]["verifier"]["target_fidelity"] <
            report["controls"]["baseline"]["verifier"]["target_fidelity"] <
            report["rows"]["raw-float64"]["verifier"]["target_fidelity"]):
        report["failed_criteria"].append("coherent_phase_order")
    from positive_control import positive_control56
    c56, v56 = positive_control56()
    full56 = verify_full_output(c56, v56)
    report["controls"]["D56"] = full56
    if abs(full56["target_fidelity"] - 1) > 5e-12 or full56["gram_max_abs_error"] > 2e-13:
        report["failed_criteria"].append("D56")
    (directory / "readings.json").write_text(json.dumps(report, sort_keys=True, indent=2, allow_nan=False) + "\n")
    return report


if __name__ == "__main__":
    unittest.main()
