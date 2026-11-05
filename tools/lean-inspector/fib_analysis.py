"""Downstream FIB readings within the existing native module artifact custody.

The compiler supplies typed applications. No source-law instance lives here;
readings are data and do not contribute to proof assessment or seal authority.
"""
import argparse
import copy
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time
import zipfile

HEX = re.compile(r"[0-9a-f]{64}")
FIELDS = {"arena", "source_contract", "atom_readout", "seam_readout",
          "pyramid_coordinates", "association_coordinate", "continuation_target",
          "kernel", "escape_pairs", "escape_rate", "unique_capture",
          "layered_spectrum", "residuals", "disposition"}
ROW_FIELDS = {"application", "owner", "target", "target_module", "target_type_identity",
              "input_identity", "request", "unavailable_reason", "reading"}


def validate(value, *, complete=True):
    if (not isinstance(value, dict) or set(value) != {"applications"}
            or not isinstance(value["applications"], list)):
        raise ValueError("fib.invalid_partition")
    previous = None
    for row in value["applications"]:
        if not isinstance(row, dict) or set(row) != ROW_FIELDS:
            raise ValueError("fib.invalid_application")
        if (any(not isinstance(row[k], str) or not row[k] for k in
                ("application", "owner", "target_module", "input_identity"))
                or (row["target"] is not None and
                    (not isinstance(row["target"], str) or not row["target"]))
                or (row["target"] is None and row["request"] is not None)
                or not HEX.fullmatch(row["input_identity"])
                or (row["target_type_identity"] is not None and
                    not HEX.fullmatch(row["target_type_identity"]))
                or not isinstance(row["unavailable_reason"], str)
                or (row["request"] is not None and not isinstance(row["request"], dict))
                or (previous is not None and row["application"] <= previous)):
            raise ValueError("fib.invalid_binding")
        request = row["request"]
        if request is not None and "binding" in request:
            source = request["binding"]
            binding = source.get("occurrence") if isinstance(source, dict) else None
            original = binding.get("original_type") if isinstance(binding, dict) else None
            if (not isinstance(binding, dict) or not isinstance(original, dict)
                    or binding.get("source_name") != row["target"]
                    or original.get("identity") != row["target_type_identity"]):
                raise ValueError("fib.source_binding_mismatch")
        previous = row["application"]
        reading = row["reading"]
        if reading is None and not complete:
            continue
        if (not isinstance(reading, dict) or set(reading) != FIELDS
                or reading["disposition"].get("is_lean_proof") is not False):
            raise ValueError("fib.invalid_reading")
        if row["request"] is None and any(reading[k] is not None for k in FIELDS - {"disposition"}):
            raise ValueError("fib.unavailable_fabricated_reading")
    return value


def unavailable(reason):
    reading = dict.fromkeys(FIELDS)
    reading["disposition"] = {"status": "open", "reason": reason,
                              "is_lean_proof": False,
                              "proof_escape": "unchanged; downstream analysis only",
                              "readings": {key: {"kind": "unavailable", "reason": reason}
                                           for key in sorted(FIELDS - {"disposition"})}}
    return reading


def prepare(row, previous_artifact):
    """Reuse unchanged declaration payloads from the existing module artifact.

    No separate cache, source inventory or dependency planner is created.
    Changed leaves arrive solely through Lake's compiler dependency traces.
    """
    partition = row.get("fib_analysis")
    if partition is None:
        return
    validate(partition, complete=False)
    previous = {}
    path = Path(previous_artifact)
    if path.suffix == ".pending":
        path = path.with_suffix("")
    if path.is_file():
        # These are the same production-validated artifacts Lake reuses as is.
        # A malformed prior leaf prevents reuse rather than becoming evidence.
        import publication
        with zipfile.ZipFile(path) as artifact:
            report = publication.read_json(artifact.read('raw-lean-report.json'))
            if report['schema'] != publication.materials.REPORT_SCHEMA or len(report['modules']) != 1:
                raise ValueError('fib.previous_module_binding')
            old = report['modules'][0]
            if old['module'] != row['module']:
                raise ValueError('fib.previous_module_binding')
            publication.check_origin(publication.read_json(
                artifact.read('raw-lean-report.json.provenance.json')), old)
        if "fib_analysis" in old:
            validate(old["fib_analysis"])
            previous = {x["application"]: x for x in old["fib_analysis"]["applications"]}
    pending = []
    reused = 0
    for leaf in partition["applications"]:
        old = previous.get(leaf["application"])
        # Compare the complete detached compiled input as well as its closure.
        if old and all(old[k] == leaf[k] for k in ROW_FIELDS - {"reading"}):
            leaf["reading"] = copy.deepcopy(old["reading"])
            reused += 1
        elif leaf["request"] is None:
            leaf["reading"] = unavailable(leaf["unavailable_reason"])
        else:
            leaf["reading"] = None
            pending.append(leaf)
    return dict(extracted=len(partition['applications']), generated=len(pending), reused=reused,
                unavailable=sum(x['request'] is None for x in partition['applications']))


def finish(row, analyzer, stats):
    """Complete the existing spool after Lake prepares a needed analyzer."""
    partition = row.get('fib_analysis')
    if partition is None:
        return
    pending = [leaf for leaf in partition['applications'] if leaf['reading'] is None]
    if len(pending) != stats['generated']:
        raise ValueError('fib.analysis_incomplete')
    analysis_ns = 0
    if pending:
        if not analyzer:
            raise ValueError("fib.analysis_program_missing")
        started = time.monotonic_ns()
        result = subprocess.run([str(analyzer), "--batch"],
            input=json.dumps([x["request"] for x in pending]),
            text=True, capture_output=True, check=False,
            env=dict(os.environ, LEAN_FIB_COMPILED_PROJECTION="1"))
        analysis_ns = time.monotonic_ns() - started
        if result.returncode not in (0, 2):
            raise ValueError(f"fib.analysis_failed:exit={result.returncode}:{result.stderr}")
        outputs = json.loads(result.stdout)
        if not isinstance(outputs, list) or len(outputs) != len(pending):
            raise ValueError("fib.analysis_incomplete")
        for leaf, reading in zip(pending, outputs):
            leaf["reading"] = reading
        rejected = any(x["disposition"]["status"] == "refuted" for x in outputs)
        if (result.returncode == 2) != rejected:
            raise ValueError("fib.analysis_exit_mismatch")
    validate(partition)
    stats = dict(stats, **{'analysis-invocations': int(bool(pending)), 'analysis-ns': analysis_ns})
    print(f'LEAN_INSPECTOR_FIB module={row["module"]} generated={len(pending)} reused={stats["reused"]} unavailable='
          f'{stats["unavailable"]}')
    return stats


def produce(row, previous_artifact, analyzer):
    stats = prepare(row, previous_artifact)
    return finish(row, analyzer, stats) if stats is not None else None


def application_inputs(report):
    """Complete compiled inputs from an existing custody-bound report.

    Only the input fields are compared. Readings and diagnostics are not test
    receipts or invalidation keys. No source inventory or owner list is used.
    """
    import publication
    with tempfile.TemporaryDirectory(prefix='fib-inputs.') as directory:
        report = Path(report)
        if report.suffix == '.zip':
            with zipfile.ZipFile(report) as bundle:
                for suffix in ('', '.provenance.json'):
                    with bundle.open('raw-lean-report.json' + suffix) as source:
                        with (Path(directory) / ('raw-lean-report.json' + suffix)).open('wb') as output:
                            shutil.copyfileobj(source, output)
            report = Path(directory) / 'raw-lean-report.json'
        provenance = publication.read_json(publication.member(report, '.provenance.json').read_bytes())
        origins = provenance.get('module_origins', {provenance['module']: provenance}
                                 if 'module' in provenance else {})
        result = {}
        seen = set()
        for row in publication.report_rows(report, publication.materials.REPORT_SCHEMA):
            name = row['module']
            if name in seen or name not in origins:
                raise ValueError('fib.report_membership')
            seen.add(name)
            origin = origins[name]
            expected = {x['name'] for x in origin['input_projection']['inputs']
                        if x['type'] == 'LeanInformationAudit.AuricFib.Contract.Application'}
            partition = row.get('fib_analysis')
            if partition is None:
                if expected:
                    raise ValueError('fib.missing_required_inputs')
                continue
            publication.check_origin(origin, row)
            leaves = validate(partition)['applications']
            if expected != {x['application'] for x in leaves}:
                raise ValueError('fib.missing_required_inputs')
            for leaf in leaves:
                if leaf['owner'] != name:
                    raise ValueError('fib.application_owner_mismatch')
                result[name, leaf['application']] = {k: leaf[k] for k in ROW_FIELDS - {'reading'}}
        if seen != set(origins):
            raise ValueError('fib.report_membership')
        return result


def run_regressions(repository, previous, current, selected=False):
    """An already selected report consumer discharges one regression obligation.

    This runs after its canonical writer returns and before publication. The
    previous published data survives a failed command, so retries compare the
    same inputs without a persisted semantic test receipt.
    """
    current_inputs = application_inputs(current)
    try:
        previous_inputs = application_inputs(previous) if Path(previous).exists() else {}
    except ValueError as error:
        if os.environ.get('REGENERATE_REPORT_ARTIFACTS') != '1' or str(error) != 'fib.invalid_partition':
            raise
        # Explicit regeneration cannot use a rejected old partition as equality
        # evidence. Require one canonical suite before publishing fresh data.
        previous_inputs = None
    changed = current_inputs != previous_inputs
    print(f'LEAN_INSPECTOR_FIB_REGRESSIONS changed={str(changed).lower()} selected={str(selected).lower()}',
          flush=True)
    if changed or selected:
        environment = dict(os.environ)
        for name in ('STRATALINT_INSPECTOR_ACTIVITY', 'STRATALINT_INSPECTOR_PHASES',
                     'STRATALINT_INSPECTOR_MODULE_WORK'):
            environment.pop(name, None)
        subprocess.run(['make', '-C', str(repository), 'compiled-fib-test'],
                       env=environment, check=True)
    return changed or selected


def consume(report, targets=()):
    """Project production readings after the ordinary material/custody checks."""
    import materials
    import publication
    provenance = publication.read_json(publication.member(report, '.provenance.json').read_bytes())
    publication.check_aggregate_rows(publication.validated_rows(report,
        publication.member(report, '.materials.zip')),
        provenance.get('module_origins', {provenance['module']: provenance}
                       if 'module' in provenance else {}))
    records = []
    for row in publication.report_rows(report, materials.REPORT_SCHEMA):
        value = row.get('fib_analysis')
        if value is not None:
            records.extend(validate(value)['applications'])
    if targets:
        selected = [x for x in records if x['target'] in targets]
        found = {x['target'] for x in selected}
        for row in publication.report_rows(report, materials.REPORT_SCHEMA):
            for declaration in row['declarations']:
                name = declaration['name']
                if name not in targets or name in found:
                    continue
                selected.append({"target": name, "target_module": row['module'],
                    "reading": unavailable("compiled declaration has no acquired FIB Application contract")})
                found.add(name)
        if found != set(targets):
            raise ValueError("fib.requested_declaration_not_in_report")
        records = selected
    return {"applications": records,
            "authority": "downstream analysis; proof and admission fields unchanged"}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('report', type=Path, nargs='?')
    parser.add_argument('--target', action='append', default=[])
    parser.add_argument('--regressions', type=Path)
    parser.add_argument('--previous', type=Path)
    parser.add_argument('--selected', choices=('true', 'false'), default='false')
    args = parser.parse_args()
    if args.report is None:
        parser.error('a report is required')
    try:
        if args.regressions:
            if args.previous is None:
                parser.error('regressions require --previous')
            run_regressions(args.regressions, args.previous, args.report, args.selected == 'true')
        else:
            print(json.dumps(consume(args.report, args.target), sort_keys=True))
    except subprocess.CalledProcessError as error:
        sys.exit(error.returncode)
