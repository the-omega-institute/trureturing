#!/usr/bin/env python3
"""Exercise ordinary compiled optional information across authenticated probe replay."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]
MODULE = "LeanInformationAuditRegTests.SearchReduction.InformationCacheApplication"
SOURCE = ROOT / "tools/lean-inspector" / (MODULE.replace(".", "/") + ".lean")
APPLICATION = "LeanInformationAudit.Tests.SearchReduction.InformationCacheApplication.application"
FIXTURE_MODULE = "LeanInformationAuditRegTests.SearchReduction.InformationCache.LawFixture"
FIXTURE = ROOT / "tools/lean-inspector" / (FIXTURE_MODULE.replace(".", "/") + ".lean")
TARGET = FIXTURE_MODULE + ".RegisteredPos.target"
B0 = "b02b98342945a1a724a227db4fa38e376640e573"
FIELDS = ("information_face", "information_application", "information_registration",
          "information_ordinary_records")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    directory = Path(tempfile.mkdtemp(prefix="information-cache-", dir=ROOT / "build/lean-inspector"))
    print("INFORMATION_CACHE_ARTIFACTS " + str(directory), flush=True)
    env = dict(os.environ, SEARCH_REDUCTION_PROBE_CACHE=str(directory / "cache"),
               SEARCH_REDUCTION_RESUME="", SEARCH_REDUCTION_QUERY_CACHE="",
               SEARCH_REDUCTION_WORKERS="1", SEARCH_REDUCTION_PROFILE=str(directory / "phases.log"))
    observations = {}
    phases = {}
    checks = []

    def run(label, command, overrides=None):
        profile = Path(env["SEARCH_REDUCTION_PROFILE"])
        offset = profile.stat().st_size if profile.exists() else 0
        started = time.monotonic()
        result = subprocess.run(command, cwd=ROOT, env=dict(env, **(overrides or {})),
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        (directory / (label + ".log")).write_text(result.stdout)
        phases[label] = profile.read_bytes()[offset:].decode() if profile.exists() else ""
        (directory / (label + ".phases.log")).write_text(phases[label])
        record = dict(label=label, command=command, exit=result.returncode,
                      seconds=round(time.monotonic() - started, 3))
        checks.append(record)
        print("INFORMATION_CACHE_CHECK " + json.dumps(record), flush=True)
        if result.returncode:
            raise RuntimeError(label + ": nonzero exit; see " + str(directory / (label + ".log")))
        return result.stdout

    request = directory / "request.lean"
    request.write_text(f"import {MODULE}\nimport LeanInformationAuditRegAnalysis.SearchReduction.Commands\n"
        "set_option Elab.async false\nset_option maxHeartbeats 0\n"
        "open Lean\nrun_cmd modifyEnv fun env => env.setMainModule "
        "`LeanInformationAuditRegTests.SearchReduction.InformationCacheRequest\n"
        f'#search_reduction {TARGET} at "{B0}" baseline [] using [] '
        f"information {APPLICATION} as informationCacheReading\n")
    # The normal command owns child isolation and the cache base. The fixture
    # module address permits the existing test-index fallback, without changing B0.

    current = directory / "current.lean"
    current.write_text(f"import {MODULE}\nimport LeanInformationAuditRegAnalysis.SearchReduction.Commands\n"
        "set_option maxHeartbeats 0\nopen Lean Elab Command LeanInformationAudit.SearchReduction\n"
        f"run_cmd do\n  let reading ← acquireInformation (← getEnv) `{TARGET} #[] (some `{APPLICATION})\n"
        f"  pickle (System.FilePath.mk {json.dumps(str(directory / 'current-reading.pickle'))}) reading\n"
        f"  logInfo (observationJson (withInformation {{target := `{TARGET}, base := .found, paired := .found, verdict := .bindOnly}} reading)).compress\n")
    if SOURCE.exists() or FIXTURE.exists():
        raise RuntimeError("temporary fixture paths already exist; refusing to overwrite")
    fixture_original = ROOT / "tools/lean-inspector/LeanInformationAuditFibTests/AuricFib/LawFixture.lean"
    FIXTURE.parent.mkdir(parents=True, exist_ok=True)
    FIXTURE.write_text(fixture_original.read_text().replace(
        "LeanInformationAuditFibTests.AuricFib.LawFixture", FIXTURE_MODULE))
    original = (f"import {FIXTURE_MODULE}\n"
        "namespace LeanInformationAudit.Tests.SearchReduction.InformationCacheApplication\n"
        "open LeanInformationAudit.AuricFib.Contract\n"
        f"open {FIXTURE_MODULE}\n"
        "private noncomputable def currentApplication : Application.{0,0,0,0,0,0} RegisteredPos.target :=\n"
        "  RegisteredPos.strict\n"
        "noncomputable def application : Application.{0,0,0,0,0,0} RegisteredPos.target :=\n"
        "  currentApplication\n"
        "end LeanInformationAudit.Tests.SearchReduction.InformationCacheApplication\n").encode()
    SOURCE.write_bytes(original)
    expected_source = sha(SOURCE)
    identities = []

    def build(label):
        run(label, ["make", "lean", "LEAN_TARGETS=LeanInformationAuditRegAnalysis.SearchReduction.Commands " + MODULE])
        base = ROOT / ".lake/build/lean-inspector/reg/lib/lean" / MODULE.replace(".", "/")
        target_base = ROOT / ".lake/build/lean-inspector/reg/lib/lean" / FIXTURE_MODULE.replace(".", "/")
        identities.append(dict(label=label, source_sha256=sha(SOURCE), target_sha256=sha(target_base.with_suffix(".olean")), compiled={
            str(path.relative_to(ROOT)): sha(path) for path in
            (base.with_suffix(".olean"), base.with_suffix(".olean.server"),
             base.with_suffix(".olean.private")) if path.exists()}))

    def observation(label, path, cached=True):
        text = run(label, ["make", "search-reduction-run", "REQUESTS=" + str(path)],
                   None if cached else {"SEARCH_REDUCTION_PROBE_CACHE": "0"})
        rows = []
        for line in text.splitlines():
            try:
                value = json.loads(line[line.index("{"):])
            except (ValueError, json.JSONDecodeError):
                continue
            if isinstance(value, dict) and "information_face" in value:
                rows.append(value)
        if len(rows) != 1:
            raise RuntimeError(label + ": expected one executed ordinary information reading")
        observations[label] = rows[0]
        return rows[0], text

    def metadata(value):
        return {field: value[field] for field in FIELDS}

    def hot(label, expected):
        value, text = observation(label, request)
        if "PROBE_CACHE hit=authenticated" not in text or "PROBE_CACHE_ENTRY selected=authenticated" not in text:
            raise RuntimeError(label + ": unchanged computational inputs did not reuse authenticated entry")
        if any(marker in text for marker in ("PROBE_CACHE_REJECTED", "PANIC",
                "search.probe_compile_failed")):
            raise RuntimeError(label + ": hot replay panicked or fell back")
        if "PROBE_CACHE miss" in text or " query/" in phases[label]:
            raise RuntimeError(label + ": hot replay recomputed R")
        if "probe/cache-kernel-end" not in phases[label]:
            raise RuntimeError(label + ": missing executed hot kernel phase")
        if metadata(value) != metadata(expected):
            raise RuntimeError(label + ": stale optional information: " + json.dumps({
                "cached_face": value["information_face"],
                "current_face": expected["information_face"],
                "different_fields": [field for field in FIELDS if value[field] != expected[field]]}))
        computational = lambda row: {key: item for key, item in row.items()
                                     if key not in (*FIELDS, "information_tag")}
        if computational(value) != computational(cold):
            raise RuntimeError(label + ": optional information changed computational observation")
        return value

    try:
        build("strict-build")
        cold, _ = observation("strict-cold", request)
        fresh, _ = observation("strict-current", current, False)
        if fresh["information_face"] != "strict-bound" or not fresh["information_ordinary_records"]:
            raise RuntimeError("strict positive ordinary registration was not acquired")
        if metadata(cold) != metadata(fresh):
            raise RuntimeError("cold optional reading differs from current ordinary assessor")
        hot("strict-hot", fresh)
        replacement = "{ evidence := .law RegisteredPos.client RegisteredPos.family none [] none }"
        text = original.decode()
        if text.count("  RegisteredPos.strict\n") != 1:
            raise RuntimeError("application fixture mutation anchor is not unique")
        SOURCE.write_text(text.replace("  RegisteredPos.strict\n", "  " + replacement + "\n"))
        build("unknown-build")
        fresh, _ = observation("unknown-current", current, False)
        if fresh["information_face"] != "unknown-bound" or not fresh["information_ordinary_records"]:
            raise RuntimeError("valid unknown ordinary registration was not acquired")
        hot("unknown-hot", fresh)
        SOURCE.write_text(text.replace("noncomputable def application", "unsafe def application").replace(
            "  currentApplication\n", "  unsafeCast (0 : Nat)\n"))
        build("unsafe-build")
        fresh, _ = observation("unsafe-current", current, False)
        if (fresh["information_face"] != "not-bound(application_not_safe_definition)" or
                fresh["information_registration"] is not None or fresh["information_ordinary_records"]):
            raise RuntimeError("invalid application did not yield typed not-bound with empty metadata")
        hot("unsafe-hot", fresh)
    finally:
        SOURCE.write_bytes(original)
        if sha(SOURCE) != expected_source:
            raise RuntimeError("application fixture source restoration failed")
        try:
            build("restored-build")
        finally:
            (directory / "application.lean").write_bytes(original)
            (directory / "target.lean").write_bytes(FIXTURE.read_bytes())
            SOURCE.unlink()
            FIXTURE.unlink()
            FIXTURE.parent.rmdir()
        if identities[-1]["compiled"] != identities[0]["compiled"]:
            raise RuntimeError("compiled application restoration changed bytes")
        if len({row["target_sha256"] for row in identities}) != 1:
            raise RuntimeError("application mutation changed the mathematical target artifact")
        (directory / "result.json").write_text(json.dumps(dict(checks=checks,
            identities=identities, observations=observations, request_sha256=sha(request),
            restored_source_sha256=expected_source), indent=2) + "\n")
    fresh, _ = observation("restored-current", current, False)
    hot("restored-hot", fresh)
    (directory / "result.json").write_text(json.dumps(dict(checks=checks, identities=identities,
        observations=observations, request_sha256=sha(request), restored_source_sha256=expected_source), indent=2) + "\n")
    print("INFORMATION_CACHE_ACCEPTED authenticated_reuse=true new_R=0 current_optional_reading=true "
          "controls=strict,unknown,unsafe,restored source=restored", flush=True)


if __name__ == "__main__":
    main()
