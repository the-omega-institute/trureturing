"""Report donor preference for the existing Actions current execution seed.

Keys are hints. Native transport, report publication and selected Lake builds
remain the authorities for acceptance and current obligations.
"""
import hashlib
import json
import pathlib
import re
import subprocess
import sys


def reuse_owner():
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2] / "lean-inspector"))
    import reuse
    return reuse


def report_prefix(prefix, captured):
    if (not isinstance(captured, dict) or captured.get("eligible") is not True
            or set(captured) != {"eligible", "semantic_version", "files", "execution"}):
        return ""
    # Hash the capture owner's value, never producer bytes or receipt metadata.
    digest = hashlib.sha256(json.dumps(captured, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    return prefix + "report-" + digest + "-"


def prefer_report(root, spec):
    """Capture only for the restore request, never again during restore/save."""
    prefix = ""
    try:
        prefix = report_prefix(spec["restore_prefix"], reuse_owner().capture(root))
    except (OSError, ValueError, TypeError, KeyError) as error:
        # Optional selection cannot hide required registration/producer errors;
        # the normal report entry still validates its authored inputs.
        print("LEAN_ACTIONS_CACHE " + json.dumps(dict(layer="current", status="preference-unavailable",
                                                       reason=str(error)), sort_keys=True), flush=True)
    if prefix:
        spec["key"] = prefix + spec["key"][len(spec["restore_prefix"]):]
    spec["report_prefix"] = prefix


def snapshot_key(spec, staged, inventory):
    """Use the actual transported producer's seal, including carried donors.

    The native exporter has accepted and copied this inventory. Reuse those
    hashes to bind its receipt; do not hash/decode the large report again or
    label a stale carried report with the current checkout's inputs.
    """
    instance = "-".join(spec["key"].rsplit("-", 2)[-2:])
    fallback = spec["restore_prefix"] + instance
    try:
        seed = "build/ci/current-check-seed/"
        bound = {item["path"]: item["sha256"] for item in inventory}
        producer_path = seed + "producer-report.json"
        data = (staged / producer_path).read_bytes()
        if hashlib.sha256(data).hexdigest() != bound[producer_path]:
            raise ValueError("producer binding changed after export")
        producer = json.loads(data)
        relative = ".lake/build/stratalint/raw-lean-report.json"
        if producer["report"] != relative:
            raise ValueError("unexpected producer report")
        api = reuse_owner()
        receipt_path = seed + relative + api.SUFFIX
        seal_bytes = (staged / receipt_path).read_bytes()
        if hashlib.sha256(seal_bytes).hexdigest() != bound[receipt_path]:
            raise ValueError("producer receipt changed after export")
        sealed = api.receipt_record(seal_bytes)
        bundle = {suffix: bound[seed + relative + suffix] for suffix in api.publication.SUFFIXES}
        if sealed["bundle"] != bundle:
            raise ValueError("producer receipt bundle mismatch")
        prefix = report_prefix(spec["restore_prefix"], sealed["inputs"])
        if prefix:
            return prefix + fallback[len(spec["restore_prefix"]):]
    except (OSError, ValueError, KeyError, TypeError):
        pass  # Keep legitimate check seeds cacheable through the broad prefix.
    return fallback


def report_seed(root):
    """Ask the normal producer whether a transported full report can be reused.

    The seed manifest declares the report paths; this adapter neither infers
    producer inputs nor treats a cache hit or prior check as current success.
    Publication and the second input/material validation belong to inspect.sh.
    """
    seed = root / "build/ci/current-check-seed"
    try:
        checks = json.loads((seed / "checks.json").read_text())
        if (checks.get("version") != 2 or checks.get("stage") != "current"
                or not re.fullmatch(r"[0-9a-f]{64}", checks.get("candidate", ""))
                or not re.fullmatch(r"[0-9a-f]{32}", checks.get("round", ""))):
            return None
        reports = set()
        suffixes = ("", ".sha256", ".input.attestation", ".provenance.json", ".materials.zip", ".reuse.json")
        producer_path = seed / "producer-report.json"
        if producer_path.exists():
            producer = json.loads(producer_path.read_text())
            relative = ".lake/build/stratalint/raw-lean-report.json"
            if (set(producer) != {"version", "candidate", "round", "report", "materials"}
                    or producer["version"] != 1 or producer["report"] != relative
                    or not re.fullmatch(r"[0-9a-f]{64}", producer["candidate"])
                    or not re.fullmatch(r"[0-9a-f]{32}", producer["round"])):
                return None
            declared = [material["path"] for material in producer["materials"]]
            if len(declared) != len(suffixes) or set(declared) != {relative + suffix for suffix in suffixes}:
                return None
            reports.add(relative)
        else:
            # Legacy seeds carry only the original report of each check unit.
            for unit in checks["units"]:
                relative = unit.get("report")
                if not isinstance(relative, str) or not re.fullmatch(
                        r"build/ci/check-material/[0-9a-f]{64}/[0-9a-f]{32}/[0-9a-f]{32}/report/raw-lean-report\.json", relative):
                    continue
                declared = {material["path"] for material in unit["materials"]}
                if all(relative + suffix in declared for suffix in suffixes):
                    reports.add(relative)
    except (OSError, ValueError, TypeError, KeyError, AttributeError):
        return None
    for relative in sorted(reports):
        report = seed / relative
        result = subprocess.run([sys.executable, str(root / "tools/lean-inspector/reuse.py"), "probe",
            "--repository", str(root), "--report", str(report), "--diagnostics"],
            cwd=root, check=True, capture_output=True, text=True)
        outcome = json.loads(result.stdout)
        if type(outcome.get("needs_lake")) is not bool:
            raise ValueError("report producer returned no cache resource decision")
        if result.stderr:
            print(result.stderr, end="", file=sys.stderr, flush=True)
        if not outcome["needs_lake"]:
            return str(report)
    return None
