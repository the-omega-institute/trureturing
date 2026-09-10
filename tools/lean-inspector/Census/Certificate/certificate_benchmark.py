"""Measure the real frozen-key certificate without running disposition queries.

The two emit authorities are parseReport's validated rows and the frozen export.
This produces a key-accounting receipt, not a disposition classification report.
Run after make lean-cache-ensure and make lean on the measured candidate tree.
"""

import argparse
import hashlib
import json
import os
import pathlib
import subprocess
import sys


if __package__ in (None, ""):
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

from Certificate.emission import write_manifest, string, write_module
from pipeline import frozen_keys
from resources import run


def emit(report_path, bindings_path, directory):
    report_bytes = report_path.read_bytes()
    report = json.loads(report_bytes)
    write_manifest(directory, json.loads(bindings_path.read_text()), frozen_keys(report),
        report["source_commit"], "sha256:" + hashlib.sha256(report_bytes).hexdigest(), "CensusRun.Root")


def benchmark(repository, report, directory):
    directory.mkdir(parents=True, exist_ok=True)
    head = json.loads(report.read_text())["source_commit"]
    digest = "sha256:" + hashlib.sha256(report.read_bytes()).hexdigest()
    module = "LeanInformationAudit.Tests.Census.Manifest.Benchmark"
    driver = write_module(directory, "BenchmarkDriver", f"import {module}\n"
        f"#census_certificate_benchmark report {string(str(report))} head {string(head)} "
        f"digest {string(digest)} directory {string(str(directory))}\n")
    result = run(["lake", "env", "python3", str(pathlib.Path(__file__).resolve()),
        "--report", str(report), "--directory", str(directory), "--driver", str(driver)],
        directory, "certificate", cwd=repository, budget_gb=4,
        env=dict(os.environ, LEAN_NUM_THREADS="1"), phase_path=directory / "benchmark.phase")
    build = json.loads((directory / "CensusRun/Root.checked.build.json").read_text())
    result["build"] = build
    result["compiler_build_target_met"] = build["wall_s"] <= 180 and build["max_process_peak_rss_bytes"] <= 1024 ** 3
    result["compiler_build_profile_required"] = build["wall_s"] > 360 or build["max_process_peak_rss_bytes"] > 2 * 1024 ** 3
    result["whole_path_target_met"] = result["wall_seconds"] <= 180 and result["peak_rss_bytes"] <= 1024 ** 3
    result["profile_required"] = result["wall_seconds"] > 360 or result["peak_rss_bytes"] > 2 * 1024 ** 3
    (directory / "target.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


def run_driver(driver):
    # Lake supplies the warm dependency paths. Put the compiler's own library
    # first so every Init/Lean import avoids a failed probe of each package.
    # Lake setup and this lookup are inside the whole-path resource timer.
    prefix = subprocess.check_output(["lean", "--print-prefix"], text=True).strip()
    library = str(pathlib.Path(prefix) / "lib/lean")
    paths = [path for path in os.environ.get("LEAN_PATH", "").split(os.pathsep)
             if path and path != library]
    env = dict(os.environ, LEAN_PATH=os.pathsep.join([library, *paths]))
    os.execvpe("lean", ["lean", "-DmaxHeartbeats=0", "-DmaxRecDepth=4000", str(driver)], env)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", required=True, type=pathlib.Path)
    parser.add_argument("--directory", required=True, type=pathlib.Path)
    parser.add_argument("--bindings", type=pathlib.Path, help="Internal: emit from parseReport's validated rows")
    parser.add_argument("--driver", type=pathlib.Path, help="Internal: execute inside Lake's warm environment")
    options = parser.parse_args()
    if options.driver:
        run_driver(options.driver)
    elif options.bindings:
        emit(options.report, options.bindings, options.directory)
    else:
        repository = pathlib.Path(__file__).resolve().parents[4]
        benchmark(repository, options.report.resolve(), options.directory.resolve())


if __name__ == "__main__":
    main()
