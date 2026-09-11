"""Structural trivial source closure through the production command and disk cache."""
import json
import os
import pathlib
import subprocess
import sys
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))
from validation import run_batches


def check_trivial_sources(repository, directory):
    directory.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, IE_PROJECTION_OUTPUT_DIR=str(directory))
    def step(command, label, **kwargs):
        subprocess.run(command, cwd=repository, env=env, check=True)
    step(["lake", "env", "lean", "-R", "tools/lean-inspector",
          "tools/lean-inspector/LeanInformationAudit/Tests/Census/StructuralSources.lean"], "sources")
    read = lambda name: json.loads((directory / name).read_bytes())
    metadata, request = read("trivial-source-index.json"), read("trivial-source-request.json")
    key = request["keys"][0]
    batch = {"keys": [key], "imports": [key[0], "LeanInformationAudit.Census.Command"]}
    plan = {"execute": [batch], "planned": [batch], "bound": metadata["batch_module_bound"],
            "key_bound": 1, "scopes": dict(metadata["scopes"]), "cache": directory / "cache",
            "addresses": {key[2]: "sha256:fixture"}, "inputs_for": lambda _: {"key": key},
            "keys_by_id": {key[2]: key}, "entries": [], "source_inputs": [], "hits": [], "misses": [key]}
    binary = directory / "lean-command"
    binary.write_text('#!/bin/sh\nexec lake env lean "$@"\n')
    binary.chmod(0o700)
    result, _ = run_batches(repository, directory, metadata, request, plan, step, str(binary))
    cached = read("cache/fixture.json")
    expected = read("trivial-source-output.json")["source_inputs"]
    assert len(expected) == 1 and result["source_inputs"] == cached["source_inputs"] == expected, \
        "StructuralSources: cache drops structural trivial provenance"
    assert cached["row"] == result["entries"][0], "StructuralSources: cached row changes"
    return {"name": "structural_trivial_production_cache", "sources": len(expected), "exit": 0}


if __name__ == "__main__":
    print(json.dumps(check_trivial_sources(pathlib.Path(__file__).resolve().parents[4],
                                          pathlib.Path(sys.argv[1]).resolve())))
