#!/usr/bin/env bash

# Validate a complete canonical Lean-report bundle. With only REPORT, validate
# the bundle's self-contained address relationships. With current repository
# identities, also require the bundle to address those exact inputs. An optional
# final MODE pins the provenance mode for freshly materialized bundles.
lean_report_bundle_validate() {
  if [[ "$#" -ne 1 && "$#" -ne 6 && "$#" -ne 7 ]]; then
    printf '%s\n' 'lean_report_bundle_validate requires 1, 6, or 7 arguments' >&2
    return 2
  fi

  python3 - "$@" <<'PY'
import hashlib
import json
import pathlib
import re
import sys
import zipfile


def reject(reason):
    print(f"lean-report-bundle: {reason}", file=sys.stderr)
    raise SystemExit(1)


arguments = sys.argv[1:]
report = pathlib.Path(arguments[0])
expected = arguments[1:]
if len(expected) not in (0, 5, 6):
    reject("invalid expected-identity arity")

members = [
    report,
    pathlib.Path(str(report) + ".sha256"),
    pathlib.Path(str(report) + ".input.attestation"),
    pathlib.Path(str(report) + ".provenance.json"),
    pathlib.Path(str(report) + ".materials.zip"),
]
if any(path.is_symlink() or not path.is_file() or path.stat().st_size == 0 for path in members):
    reject("bundle member is missing, empty, or symbolic")

try:
    report_digest = hashlib.sha256(report.read_bytes()).hexdigest()
    sidecar = members[1].read_bytes()
    attestation = members[2].read_bytes()
    provenance_bytes = members[3].read_bytes()
    provenance = json.loads(provenance_bytes.decode("utf-8", errors="strict"))
except (OSError, UnicodeError, ValueError, json.JSONDecodeError) as error:
    reject(f"bundle sidecar is unreadable: {error}")

expected_sidecar = f"{report_digest}  {report.name}\n".encode("ascii")
if sidecar != expected_sidecar:
    reject("report SHA-256 sidecar mismatch")

try:
    attestation_lines = attestation.decode("ascii").splitlines(keepends=True)
except UnicodeDecodeError:
    reject("input attestation is not ASCII")
if len(attestation_lines) != 4 or any(not line.endswith("\n") for line in attestation_lines):
    reject("input attestation must contain exactly four terminated lines")
attestation_values = [line[:-1] for line in attestation_lines]
hex64 = re.compile(r"[0-9a-f]{64}")
if (
    attestation_values[0] != "schema=stratalint-lean-report-input-attestation-v1"
    or not re.fullmatch(r"repository_input_sha256=[0-9a-f]{64}", attestation_values[1])
    or not re.fullmatch(r"producer_sha256=[0-9a-f]{64}", attestation_values[2])
    or attestation_values[3] != f"report_sha256={report_digest}"
):
    reject("input attestation mismatch")
repository_address = attestation_values[1].split("=", 1)[1]
attested_producer = attestation_values[2].split("=", 1)[1]

expected_keys = {
    "schema", "side", "mode", "source_side", "input_address",
    "producer_sha256", "repository_inspector_sha256", "lean_sources_sha256",
    "lean_config_sha256", "report_sha256",
}
if not isinstance(provenance, dict) or set(provenance) != expected_keys:
    reject("provenance must contain exactly the canonical ten keys")
hash_fields = (
    "producer_sha256",
    "repository_inspector_sha256",
    "lean_sources_sha256",
    "lean_config_sha256",
    "report_sha256",
)
if (
    provenance.get("schema") != "stratalint-lean-report-provenance-v1"
    or provenance.get("side") != "candidate"
    or provenance.get("mode") not in ("produced", "cached")
    or provenance.get("source_side") != "candidate"
    or any(not isinstance(provenance.get(field), str)
           or not hex64.fullmatch(provenance[field]) for field in hash_fields)
    or provenance.get("report_sha256") != report_digest
    or provenance.get("producer_sha256") != attested_producer
):
    reject("provenance identity mismatch")

address_preimage = (
    "schema=stratalint-lean-report-input-v1\n"
    f"producer_sha256={provenance['producer_sha256']}\n"
    f"repository_inspector_sha256={provenance['repository_inspector_sha256']}\n"
    f"lean_sources_sha256={provenance['lean_sources_sha256']}\n"
    f"lean_config_sha256={provenance['lean_config_sha256']}\n"
).encode("ascii")
input_address = hashlib.sha256(address_preimage).hexdigest()
if provenance.get("input_address") != "sha256:" + input_address:
    reject("provenance input address mismatch")

canonical_provenance = (
    '{"schema":"stratalint-lean-report-provenance-v1","side":"candidate",'
    f'"mode":"{provenance["mode"]}","source_side":"candidate",'
    f'"input_address":"sha256:{input_address}",'
    f'"producer_sha256":"{provenance["producer_sha256"]}",'
    f'"repository_inspector_sha256":"{provenance["repository_inspector_sha256"]}",'
    f'"lean_sources_sha256":"{provenance["lean_sources_sha256"]}",'
    f'"lean_config_sha256":"{provenance["lean_config_sha256"]}",'
    f'"report_sha256":"{report_digest}"}}\n'
).encode("ascii")
if provenance_bytes != canonical_provenance:
    reject("provenance sidecar is not the canonical byte sequence")

if expected:
    expected_repository, expected_producer, expected_resident, expected_sources, expected_config = expected[:5]
    if any(not hex64.fullmatch(value) for value in expected[:5]):
        reject("expected repository identity is malformed")
    if (
        repository_address != expected_repository
        or provenance["producer_sha256"] != expected_producer
        or provenance["repository_inspector_sha256"] != expected_resident
        or provenance["lean_sources_sha256"] != expected_sources
        or provenance["lean_config_sha256"] != expected_config
    ):
        reject("bundle does not address the current repository inputs")
    if len(expected) == 6 and provenance["mode"] != expected[5]:
        reject("provenance mode mismatch")

try:
    if not zipfile.is_zipfile(members[4]):
        reject("material archive is not a ZIP file")
    with zipfile.ZipFile(members[4]) as archive:
        damaged_member = archive.testzip()
except (OSError, ValueError, zipfile.BadZipFile, RuntimeError) as error:
    reject(f"material archive is invalid: {error}")
if damaged_member is not None:
    reject(f"material archive member failed CRC: {damaged_member}")

print(input_address)
PY
}
