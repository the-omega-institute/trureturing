"""Scientific identities and protocol validation, independent of I/O cadence."""

import dataclasses
import hashlib
import json
import math
from pathlib import Path


OCCUPATION = (4, 2, 1, 1)
ALPHABET = (0, 1, 2, 3)
DIMENSIONS = (13, 16, 24, 32, 40, 48, 55)
WORD_COUNT = 840
OBJECTIVE = "||sum_legal A[w7] ... A[w0] v0 / sqrt(840)||^2"
RESTRICTIONS = {
    "field": "real",
    "isometry": "one fixed V: R^D -> R^4 tensor R^D, used eight times",
    "initial_memory": "one normalized trainable pure vector",
    "final_memory": "traced, no selected final vector",
    "postselection": False,
    "time_varying_controls": False,
    "entrywise_positivity": False,
    "interpretation": "numerical candidates only; search failure is not a lower bound",
}
ALGORITHM = "householder-occupation-dp-adam-v1"
SCHEMA = 2
ANALYTIC_ALGORITHM = "householder-occupation-dp-adam-analytic-d55-v1"
ANALYTIC_VERSION = "stationary55-column-rotation-v1"
CONVERTER = "positive-target-householder-fixed-eye-v1"
# Supported input identity, checked against the complete declarative recipe.
D55_RECIPE_SHA256 = "f22c900bd1482a55fb7a8294f4e164fde99c38bd7feaa80caf6af23ae41c44af"


@dataclasses.dataclass
class Config:
    dimensions: tuple = DIMENSIONS
    seed_steps: int = 5000
    base_seed: int = 5040
    learning_rate: float = 0.01
    minimum_learning_rate: float = 0.001
    batch_steps: int = 25
    log_max_bytes: int = 1048576
    log_backups: int = 3
    verification_gap: float = 1e-6
    verification_interval_steps: int = 1000
    verification_chunk_size: int = 256
    mps_memory_fraction: float = 0.25

    def validate(self):
        if not self.dimensions or len(set(self.dimensions)) != len(self.dimensions):
            raise ValueError("dimensions must be a nonempty list without duplicates")
        if any(type(d) is not int or d not in DIMENSIONS for d in self.dimensions):
            raise ValueError("search dimensions must be drawn from " + str(DIMENSIONS))
        integer_ranges = {
            "seed_steps": (1, 10000000), "base_seed": (0, 2 ** 63 - 1),
            "batch_steps": (1, 1000), "log_max_bytes": (4096, 67108864),
            "log_backups": (1, 10), "verification_interval_steps": (1, 10000000),
            "verification_chunk_size": (1, 4096),
        }
        for field, (low, high) in integer_ranges.items():
            value = getattr(self, field)
            if type(value) is not int or not low <= value <= high:
                raise ValueError("%s must be an integer in [%d, %d]" % (field, low, high))
        for field in ("learning_rate", "minimum_learning_rate", "verification_gap",
                      "mps_memory_fraction"):
            value = getattr(self, field)
            if not math.isfinite(value) or value <= 0:
                raise ValueError(field + " must be finite and positive")
        if self.minimum_learning_rate > self.learning_rate:
            raise ValueError("minimum learning rate must not exceed learning rate")
        if self.learning_rate > 1 or self.verification_gap > 1:
            raise ValueError("learning rate and verification gap must not exceed 1")
        if self.mps_memory_fraction > 1:
            raise ValueError("MPS memory fraction must be in (0, 1]")

    def learning_rate_at(self, iteration):
        fraction = iteration / max(1, self.seed_steps - 1)
        return self.minimum_learning_rate + 0.5 * (
            self.learning_rate - self.minimum_learning_rate) * (1 + math.cos(math.pi * fraction))


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False)


def identity(value):
    return hashlib.sha256(canonical(value).encode("utf-8")).hexdigest()


def numerical_runtime(runtime):
    keys = ("python", "torch", "torch_git", "torch_build", "platform", "machine", "hardware", "actual_device",
            "training_precision", "cpu_fallback", "torch_cpu_threads", "deterministic_algorithms")
    result = {key: runtime.get(key) for key in keys}
    result["environment"] = {key: runtime.get("environment", {}).get(key) for key in (
        "PYTORCH_ENABLE_MPS_FALLBACK", "PYTORCH_MPS_FAST_MATH", "PYTORCH_MPS_PREFER_METAL",
        "VECLIB_MAXIMUM_THREADS", "OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS")}
    return result


def analytic_initializer(recipe):
    if not isinstance(recipe, dict) or identity(recipe) != D55_RECIPE_SHA256:
        raise ValueError("unsupported analytic D55 recipe/candidate content")
    return {"kind": "analytic-d55", "version": ANALYTIC_VERSION,
            "recipe": json.loads(canonical(recipe)), "recipe_sha256": identity(recipe),
            "converter": CONVERTER, "construction_dtype": "torch.float64",
            "frame": "H[D-1] ... H[0] eye(4D,D); reversed reduction reflectors",
            "neutral_reflector": "last ambient axis; entire current row must be exactly zero",
            "initial": "copy physical vector; existing forward normalization",
            "rng": "reset CPU and selected MPS RNG to effective seed 0; zero initializer draws",
            "perturbation": "none"}


def load_initializer(path):
    raw = Path(path).read_bytes()
    def pairs(items):
        result = {}
        for key, value in items:
            if key in result:
                raise ValueError("duplicate recipe key: " + key)
            result[key] = value
        return result
    recipe = json.loads(raw, object_pairs_hook=pairs)
    spec = analytic_initializer(recipe)
    return spec, {"recipe_path": str(Path(path).resolve()),
                  "recipe_raw_sha256": hashlib.sha256(raw).hexdigest(),
                  "recipe_raw_utf8": raw.decode("utf-8")}


def validate_initializer(initialization):
    if initialization is not None and (not isinstance(initialization, dict)
            or initialization != analytic_initializer(initialization.get("recipe"))):
        raise ValueError("unsupported analytic initializer specification")
    return initialization


def protocol_initializer(value, algorithm=None):
    """Validate the algorithm/initializer pair before any checkpoint reconciliation."""
    if not isinstance(value, dict):
        raise ValueError("trial descriptor must be an object")
    if algorithm is not None and value.get("algorithm") != algorithm:
        raise ValueError("algorithm envelope/descriptor mismatch")
    algorithm = value.get("algorithm") if algorithm is None else algorithm
    if algorithm == ANALYTIC_ALGORITHM:
        spec = value.get("initialization")
        if not isinstance(spec, dict) or spec.get("kind") != "analytic-d55":
            raise ValueError("analytic algorithm requires complete initializer metadata")
        return validate_initializer(spec)
    if algorithm == ALGORITHM:
        expected = descriptor(Config(), 13, 0, None)["initialization"]
        if value.get("initialization") != expected:
            raise ValueError("random algorithm/initializer mismatch")
        return None
    raise ValueError("unsupported algorithm/initializer combination")


def descriptor(config, dimension, seed, runtime, initialization=None, source_sha256=None):
    value = {
        "identity_schema": 1, "algorithm": ALGORITHM,
        "physical_model": {"field": "real", "occupation": list(OCCUPATION),
                           "alphabet": list(ALPHABET), "word_count": WORD_COUNT,
                           "objective": OBJECTIVE, "stationary_isometry": True,
                           "trainable_pure_initial": True, "final_memory": "traced",
                           "postselection": False, "time_varying_controls": False,
                           "entrywise_positivity": False},
        "dimension": dimension, "seed": seed, "budget": config.seed_steps,
        "dtype": "torch.float32",
        "initialization": {"reflectors": "D normalized randn(D,4D) rows on MPS",
                           "initial": "normalized randn(D) on MPS, drawn after reflectors",
                           "frame": "H[D-1] ... H[0] eye(4D,D)",
                           "rng": "torch.manual_seed and torch.mps.manual_seed; independent trial"},
        "optimizer": {"name": "torch.optim.Adam", "betas": [0.9, 0.999], "eps": 1e-8,
                      "weight_decay": 0, "amsgrad": False, "foreach": False, "fused": False,
                      "maximize": False, "capturable": False, "differentiable": False,
                      "decoupled_weight_decay": False, "gradient_clipping": None,
                      "loss": "1 - fidelity", "zero_grad_set_to_none": True,
                      "learning_rate": float(config.learning_rate),
                      "minimum_learning_rate": float(config.minimum_learning_rate),
                      "schedule": "min + (lr-min)/2*(1+cos(pi*i/max(1,budget-1))); before update"},
        "runtime": numerical_runtime(runtime) if runtime is not None else None,
    }
    if initialization is not None:
        validate_initializer(initialization)
        if dimension != 55 or tuple(config.dimensions) != (55,):
            raise ValueError("analytic D55 requires dimensions [55]")
        if not isinstance(source_sha256, str) or len(source_sha256) != 64 or any(
                c not in "0123456789abcdef" for c in source_sha256):
            raise ValueError("analytic trial requires actual scientific source SHA256")
        precision = (runtime or {}).get("training_precision")
        if precision not in ("torch.float64", "torch.float32"):
            raise ValueError("unsupported analytic training precision")
        value.update(algorithm=ANALYTIC_ALGORITHM, seed=0, initialization=initialization,
                     dtype=precision, source_sha256=source_sha256)
    return value


def scientific_without_runtime(value):
    return {key: item for key, item in value.items() if key not in ("runtime", "legacy_lineage")}


def legacy_descriptor(config, dimension, seed, lineage):
    return dict(descriptor(config, dimension, seed, None), legacy_lineage=lineage)
