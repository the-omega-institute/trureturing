"""Sequential kernel compiles, with content-addressed bucket reuse and OS peaks.

The assembly imports exported module interfaces: packed values and reduction
proofs live only in each bucket's private olean, never in the assembly heap.
"""

import argparse
import hashlib
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import time


def measured_compile(source, target, directory, env):
    command = ["lean", "-DmaxHeartbeats=0", "-DmaxRecDepth=4000", "-R", str(directory),
               "-o", str(target), str(source)]
    started = time.monotonic()
    with source.with_suffix(".compiler.log").open("w") as log:
        child = subprocess.Popen(command, env=env, stdout=log, stderr=subprocess.STDOUT)
        _, status, usage = os.wait4(child.pid, 0)
        child.returncode = os.waitstatus_to_exitcode(status)
    peak = usage.ru_maxrss * (1 if sys.platform == "darwin" else 1024)
    return {"module": source.stem, "command": command, "exit_code": child.returncode,
            "wall_s": time.monotonic() - started, "peak_rss_bytes": peak,
            "cpu_s": usage.ru_utime + usage.ru_stime}


def build(source, root, inputs, certificate_directory, data_only=False):
    repository = pathlib.Path(__file__).resolve().parents[4]
    started = time.monotonic()
    directory = source
    for _ in root.split("."):
        directory = directory.parent
    cache = pathlib.Path(os.environ.get("CENSUS_BUCKET_CACHE",
                                       repository / ".lake/build/census/buckets"))
    cert = repository / "tools/lean-inspector/LeanInformationAudit/Census/Certificate.lean"
    certificate_digest = hashlib.sha256(cert.read_bytes()).hexdigest()
    toolchain = (repository / "lean-toolchain").read_text().strip()
    library = pathlib.Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip()) / "lib/lean"
    env = dict(os.environ, LEAN_NUM_THREADS="1",
               LEAN_PATH=os.pathsep.join(map(str, [directory, library, certificate_directory])))
    def imports(text):
        return re.findall(r"^public import (CensusRun\.Range[0-9]+_[0-9]+)$", text, re.M)
    modules = []
    visited = set()
    def visit(module):
        if module in visited:
            return
        visited.add(module)
        text = (inputs / pathlib.Path(*module.split(".")).with_suffix(".lean")).read_text()
        for child in imports(text):
            visit(child)
        modules.append(module)
    for module in imports(source.read_text()):
        visit(module)
    addresses = {}
    result = {"cache_hits": 0, "cache_misses": 0, "processes": [], "buckets": [],
              "certificate_sha256": certificate_digest, "toolchain": toolchain,
              "data_only": data_only}
    receipt = source.with_suffix(".build.json")
    try:
        for module in modules:
            relative = pathlib.Path(*module.split(".")).with_suffix(".lean")
            text = (inputs / relative).read_text()
            if data_only:
                text = re.sub(r"^public theorem .*\n", "", text, flags=re.M)
            # The canonical source is a deterministic encoding of the two
            # literal vectors, n, k and b, including their fixed proof template.
            digest = hashlib.sha256(json.dumps([text, toolchain, certificate_digest,
                [addresses[child] for child in imports(text)]],
                                               separators=(",", ":")).encode()).hexdigest()
            addresses[module] = digest
            kind = "node" if imports(text) else "leaf"
            entry = cache / digest
            cached_source = entry / relative
            cached_target = cached_source.with_suffix(".olean")
            hit = (entry / "complete.json").is_file()
            result["cache_hits" if hit else "cache_misses"] += 1
            result["buckets"].append({"module": module, "digest": digest, "cache_hit": hit, "kind": kind})
            if not hit:
                cached_source.parent.mkdir(parents=True, exist_ok=True)
                cached_source.write_text(text)
                measurement = measured_compile(cached_source, cached_target, entry, env)
                measurement.update(module=module, kind=kind)
                result["processes"].append(measurement)
                if measurement["exit_code"]:
                    raise RuntimeError(cached_source.with_suffix(".compiler.log").read_text())
                temporary = entry / "complete.json.tmp"
                temporary.write_text(json.dumps(measurement, indent=2) + "\n")
                temporary.replace(entry / "complete.json")
            destination = directory / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_text(text)
            for artifact in cached_source.parent.glob(cached_source.stem + ".*"):
                if artifact.name.endswith((".lean", ".compiler.log")):
                    continue
                shutil.copyfile(artifact, destination.parent / artifact.name)
        measurement = measured_compile(source, source.with_suffix(".olean"), directory, env)
        measurement.update(module=root, kind="root")
        result["processes"].append(measurement)
        result["assembly_peak_rss_bytes"] = measurement["peak_rss_bytes"]
        if measurement["exit_code"]:
            raise RuntimeError(source.with_suffix(".compiler.log").read_text())
    finally:
        result["wall_s"] = time.monotonic() - started
        result["process_count"] = len(result["processes"])
        result["max_process_peak_rss_bytes"] = max(
            (item["peak_rss_bytes"] for item in result["processes"]), default=0)
        for kind in ["leaf", "node", "root"]:
            result[kind + "_peak_rss_bytes"] = max((p["peak_rss_bytes"] for p in result["processes"]
                if p["kind"] == kind), default=0)
        result["leaf_olean_bytes"] = [(directory / pathlib.Path(*p["module"].split(".")).with_suffix(".olean")).stat().st_size
            for p in result["buckets"] if p["kind"] == "leaf" and
            (directory / pathlib.Path(*p["module"].split(".")).with_suffix(".olean")).exists()]
        receipt.write_text(json.dumps(result, indent=2) + "\n")
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", required=True, type=pathlib.Path)
    parser.add_argument("--root", required=True)
    parser.add_argument("--inputs", required=True, type=pathlib.Path)
    parser.add_argument("--certificate-directory", required=True, type=pathlib.Path)
    parser.add_argument("--data-only", action="store_true")
    args = parser.parse_args()
    build(args.source, args.root, args.inputs, args.certificate_directory, args.data_only)
