#!/usr/bin/env python3
"""Convert a retained, stopped schema-1 snapshot; never modify its original files."""

import argparse
import copy
import hashlib
import json
import math
import os
from pathlib import Path
import sys

from search_config import (ALGORITHM, DIMENSIONS, OBJECTIVE, OCCUPATION, SCHEMA,
                           Config, identity, legacy_descriptor)
from search_session import Campaign
from state_store import (StateLocks, atomic_json, atomic_write, default_history,
                         external_path, file_hash, hash_json, shared_root, tensor_digest)
from trial_history import Registry, empty_summary


KNOWN_SOURCE_SHA256 = "e2e66992c9e5209c8b37ccc3cae809d40764eee579b83e13e82a13833d284eb5"


def source_hash(directory):
    digest = hashlib.sha256()
    for name in ("gpu_worker.py", "tensor_core.py"):
        digest.update(name.encode("ascii") + b"\0" + (Path(directory) / name).read_bytes())
    return digest.hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load_old(path, kind, source):
    import torch
    try:
        record = torch.load(path, map_location="cpu", weights_only=True)
    except Exception as error:
        raise ValueError("unsupported retained checkpoint: " + str(error)) from error
    require(isinstance(record, dict) and record.get("schema") == 1 and record.get("kind") == kind,
            "unsupported legacy checkpoint schema/kind")
    require(record.get("occupation") == list(OCCUPATION) and record.get("objective") == OBJECTIVE,
            "legacy physical objective mismatch")
    require(record.get("source_sha256") == source, "legacy checkpoint/source mismatch")
    for key in ("model", "matrices", "initial", "metrics"):
        require(key in record, "missing legacy " + key)
    require(math.isfinite(record["metrics"]["fidelity"]), "nonfinite legacy metric")
    dimension = record.get("dimension") if kind == "best" else record.get("progress", {}).get("dimension")
    require(type(dimension) is int and dimension in DIMENSIONS, "unsupported legacy model dimension")
    require(isinstance(record["model"], dict) and set(record["model"]) == {"reflectors", "initial"},
            "unsupported legacy model parameters")
    for tensor, shape in ((record["model"]["reflectors"], (dimension, 4 * dimension)),
                          (record["model"]["initial"], (dimension,)),
                          (record["matrices"], (4, dimension, dimension)),
                          (record["initial"], (dimension,))):
        require(isinstance(tensor, torch.Tensor) and tensor.dtype == torch.float32
                and tuple(tensor.shape) == shape and bool(torch.isfinite(tensor).all()),
                "unsupported/nonfinite legacy model tensor shape or dtype")
    digest = tensor_digest(record["matrices"], record["initial"])
    require(record.get("candidate_sha256") in (None, digest), "retained candidate digest mismatch")
    verification = record.get("verification")
    require(verification is None or isinstance(verification, dict)
            and verification.get("candidate_sha256") == digest, "retained verification candidate digest mismatch")
    record["candidate_sha256"] = digest
    return record


def validate_optimizer(saved, config):
    import torch
    optimizer, iteration = saved["optimizer"], saved["progress"]["iteration"]
    groups = optimizer.get("param_groups")
    require(isinstance(groups, list) and len(groups) == 1, "unsupported legacy Adam parameter groups")
    group = groups[0]
    expected = {"betas": (0.9, 0.999), "eps": 1e-8, "weight_decay": 0, "amsgrad": False,
                "foreach": False, "fused": False, "maximize": False, "capturable": False,
                "differentiable": False, "decoupled_weight_decay": False}
    for key, value in expected.items():
        require(group.get(key, False if key == "decoupled_weight_decay" else None) == value,
                "unsupported legacy Adam setting: " + key)
    rate = config.learning_rate_at(iteration - 1) if iteration else config.learning_rate
    require(math.isclose(group["lr"], rate, rel_tol=1e-14), "legacy Adam learning rate mismatch")
    params, states = group.get("params"), optimizer.get("state")
    require(params == [0, 1] and isinstance(states, dict)
            and set(states) == ({0, 1} if iteration else set()), "unsupported legacy Adam state keys")
    for key, parameter in enumerate(saved["model"][name] for name in ("reflectors", "initial")):
        if not iteration:
            continue
        state = states[key]
        step = state.get("step")
        require(isinstance(step, torch.Tensor) and step.numel() == 1 and float(step) == iteration,
                "legacy optimizer step does not match current iteration")
        for name in ("exp_avg", "exp_avg_sq"):
            moment = state.get(name)
            require(isinstance(moment, torch.Tensor) and moment.shape == parameter.shape
                    and moment.dtype == parameter.dtype and bool(torch.isfinite(moment).all()),
                    "legacy optimizer moment shape/dtype mismatch")
    for state in saved["rng"].values():
        require(isinstance(state, torch.Tensor) and state.dtype == torch.uint8
                and state.ndim == 1 and state.numel() > 0, "unsupported legacy optimizer RNG state")


def inspect_snapshot(snapshot):
    snapshot = Path(snapshot).expanduser().resolve()
    source = source_hash(snapshot)
    require(source == KNOWN_SOURCE_SHA256, "unsupported legacy source lineage")
    stopped = json.loads((snapshot / "stopped.json").read_text())
    require(stopped.get("stopped") is True and stopped.get("source_sha256") == source,
            "requires retained stopped.json evidence with exact source hash")
    checkpoint_sha = file_hash(snapshot / "latest.pt")
    require(stopped.get("checkpoint_sha256") == checkpoint_sha, "retained checkpoint digest mismatch")
    best_paths = sorted(snapshot.glob("best-*.pt"))
    allowed = {"best-%d.pt" % d for d in DIMENSIONS}
    require(all(path.name in allowed for path in best_paths), "unsupported legacy best dimension")
    hashes = {path.name: file_hash(path) for path in best_paths}
    require(stopped.get("best_sha256") == hashes, "retained best tensor inventory/digest mismatch")
    saved = load_old(snapshot / "latest.pt", "latest", source)
    config = Config(**saved["config"])
    config.dimensions = tuple(config.dimensions)
    config.validate()
    require(saved.get("config_sha256") == hash_json(saved["config"]), "legacy config digest mismatch")
    preregistration = file_hash(snapshot / "PREREGISTRATION.md")
    require(saved.get("preregistration_sha256") == preregistration, "legacy preregistration digest mismatch")
    progress = saved["progress"]
    for key in ("run_index", "iteration", "total_steps"):
        require(type(progress[key]) is int and progress[key] >= 0, "invalid legacy progress")
    index, iteration = progress["run_index"], progress["iteration"]
    require(iteration <= config.seed_steps and progress["total_steps"] == index * config.seed_steps + iteration,
            "legacy update continuity mismatch")
    require(progress["dimension"] == config.dimensions[index % len(config.dimensions)]
            and progress["seed"] == (config.base_seed + index) % (2 ** 63), "legacy schedule mismatch")
    require(saved["metrics"]["iteration"] == iteration, "legacy final metric iteration mismatch")
    require(isinstance(progress.get("created_utc"), str) and bool(progress["created_utc"]),
            "missing legacy fresh-start lineage timestamp")
    require(isinstance(saved.get("optimizer"), dict) and isinstance(saved.get("rng"), dict)
            and set(saved["rng"]) == {"torch_cpu", "torch_mps"}, "missing optimizer/RNG state")
    validate_optimizer(saved, config)
    lineage = identity({"source_sha256": source, "created_utc": progress["created_utc"],
                        "config_sha256": saved["config_sha256"]})
    evidence = {"source_sha256": source, "checkpoint_sha256": checkpoint_sha,
                "best_sha256": hashes, "preregistration_sha256": preregistration,
                "snapshot_directory": str(snapshot)}
    best = {int(path.stem.split("-")[1]): load_old(path, "best", source) for path in best_paths}
    for dimension, record in best.items():
        require(record.get("dimension") == dimension, "legacy best dimension mismatch")
    return saved, config, lineage, evidence, best


def import_prefix(registry, config, lineage, evidence, directory, count):
    registry.add_lineage(lineage, evidence, directory)
    for index in range(count):
        desc = legacy_descriptor(config, config.dimensions[index % len(config.dimensions)],
                                 (config.base_seed + index) % (2 ** 63), lineage)
        key = identity(desc)
        if registry.get(key) is None:
            registry.claim(desc, directory, evidence)
        if not registry.completed(desc):
            registry.complete(key, config.seed_steps, empty_summary(False), None)
        registry.exclude(lineage, desc, key)


def convert(snapshot, output, history_db):
    import torch
    from gpu_worker import source_hash as current_source_hash
    snapshot = Path(snapshot).expanduser().resolve()
    output, history_db = external_path(output), external_path(history_db)
    require(output != snapshot and snapshot not in output.parents and output not in snapshot.parents,
            "conversion output must be separate from retained source evidence")
    require(snapshot not in history_db.parents and snapshot != history_db
            and snapshot not in shared_root().parents and snapshot != shared_root(),
            "history and shared locks must not mutate retained source evidence")
    saved, config, lineage, evidence, best = inspect_snapshot(snapshot)
    report = {"lineage": lineage, "history_db": str(history_db), "state_directory": str(output),
              "completed_imported": saved["progress"]["run_index"]
              + int(saved["progress"]["iteration"] == config.seed_steps), "evidence": evidence,
              "unknown": "prefix per-trial metrics and numerical runtime; history before last fresh-start"}
    with StateLocks(output), Registry(history_db) as registry:
        marker = output / "migration.json"
        if marker.exists():
            require(json.loads(marker.read_text()) == report, "output belongs to different migration evidence")
            return report
        current_path = output / "latest.pt"
        if current_path.exists():
            converted = torch.load(current_path, map_location="cpu", weights_only=True)
            require(converted.get("migration_evidence") == evidence,
                    "refusing to overwrite a non-migration checkpoint")
        else:
            require(not (output / "status.json").exists(), "output already contains worker state")
            for path in output.glob("best-*.pt"):
                partial = torch.load(path, map_location="cpu", weights_only=True)
                require(partial.get("migration_evidence") == evidence,
                        "refusing to overwrite unrelated best tensors in output")
            converted = copy.deepcopy(saved)
            converted.update(schema=SCHEMA, algorithm=ALGORITHM, history_db=str(history_db),
                             legacy_lineage=lineage, migration_evidence=evidence, provenance=evidence,
                             source_sha256=current_source_hash())
            converted["progress"].update(skipped_trials=0, traversal_start_steps=0)
            desc = legacy_descriptor(config, saved["progress"]["dimension"], saved["progress"]["seed"], lineage)
            summary = empty_summary(False)
            initial = saved["progress"].get("seed_initial_fidelity")
            if initial is not None:
                summary["initial"] = {"fidelity": initial, "iteration": 0,
                                      "gram_max_abs_error": None, "initial_norm_squared": None}
            summary["final"] = copy.deepcopy(saved["metrics"])
            converted["trial"] = {"identity": identity(desc), "descriptor": desc, "summary": summary,
                                  "terminal": saved["progress"]["iteration"] == config.seed_steps,
                                  "candidate_sha256": saved["candidate_sha256"]}
            converted["invocation"] = {"session_id": "legacy-" + lineage, "pid": os.getpid()}
            for dimension, record in best.items():
                record.update(schema=SCHEMA, algorithm=ALGORITHM, migration_evidence=evidence)
                path = output / ("best-%d.pt" % dimension)
                atomic_write(path, lambda stream, item=record: torch.save(item, stream))
            # The retained snapshot and this checkpoint establish the prefix.
            # Never publish modern completed knowledge before this durable file.
            atomic_write(current_path, lambda stream: torch.save(converted, stream))
        for dimension, record in best.items():
            digest = record["candidate_sha256"]
            registry.champion(dimension, digest, record["metrics"], str(output / ("best-%d.pt" % dimension)))
            if record.get("verification") is not None and not registry.verifications(digest):
                registry.verification(digest, "verified", record["verification"])
        import_prefix(registry, config, lineage, evidence, output, saved["progress"]["run_index"])
        trial = converted["trial"]
        if registry.get(trial["identity"]) is None:
            registry.claim(trial["descriptor"], output, evidence)
        campaign = Campaign(output, config, registry, converted.get("runtime", {}), checkpoint=converted)
        if trial["terminal"]:
            registry.exclude(lineage, trial["descriptor"], trial["identity"])
        # Bootstrap status is inspectable; root must publish a real worker session
        # with --resume --max-steps before enabling launchd repetition.
        receipt = {**converted["invocation"], "sha256": file_hash(current_path),
                   "progress": campaign.progress()}
        status = {"schema": SCHEMA, "phase": "stopped", "stop_reason": "legacy_conversion", "error": None,
                  "pid": os.getpid(), "source_sha256": converted["source_sha256"],
                  "state_directory": str(output), "history_db": str(history_db),
                  "latest_checkpoint": str(current_path), "config": converted["config"],
                  "config_sha256": hash_json(converted["config"]), "progress": converted["progress"],
                  "checkpoint_saved": True, "checkpoint_receipt": receipt,
                  "session": {"id": converted["invocation"]["session_id"],
                              "start_total_steps": campaign.total_steps, "completed_steps": 0,
                              "resumed_from": campaign.resumed_from}}
        atomic_json(output / "status.json", status)
        atomic_json(marker, report)
    return report


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--snapshot", required=True)
    parser.add_argument("--state-dir", required=True)
    parser.add_argument("--history-db", default=str(default_history()))
    args = parser.parse_args(argv)
    try:
        print(json.dumps(convert(args.snapshot, args.state_dir, args.history_db), indent=2, allow_nan=False))
        return 0
    except Exception as error:
        print("legacy conversion error: " + str(error), file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
