"""Downstream FIB readings within the existing native module artifact custody.

The compiler supplies typed applications. No source-law instance lives here;
readings are data and do not contribute to proof assessment or seal authority.
"""
import argparse
import copy
import json
from pathlib import Path
import re
import subprocess
import zipfile

HEX = re.compile(r"[0-9a-f]{64}")
FIELDS = {"arena", "source_contract", "atom_readout", "seam_readout",
          "pyramid_coordinates", "association_coordinate", "continuation_target",
          "kernel", "escape_pairs", "escape_rate", "unique_capture",
          "layered_spectrum", "residuals", "disposition"}
ROW_FIELDS = {"application", "owner", "target", "target_module", "target_type_identity",
              "input_identity", "request", "unavailable_reason", "reading"}


def validate(value, *, complete=True):
    if (not isinstance(value, dict) or set(value) != {"schema_version", "applications"}
            or value["schema_version"] != 1 or not isinstance(value["applications"], list)):
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


def _qualify_compiled(request, reading):
    """Describe evidence already acquired by FibApplications in this producer.

    The arithmetic subprocess has no compiler custody and always returns raw
    table scope. This function is internal to production artifact creation;
    neither the standalone JSON command nor consume promotes decoded requests.
    """
    if request.get("arena") != "typed-source" or reading["disposition"]["status"] == "refuted":
        return reading
    acquisition = request["acquisition"]
    kind, reason = acquisition["kind"], acquisition["reason"]
    finite = kind == "finite"
    disposition = reading["disposition"]
    disposition["reason"] = "source-bound downstream analysis; ordinary audit obligations remain independent"
    readings = disposition["readings"]
    def evidence(field, kind, reason):
        readings[field] = dict(kind=kind, reason=reason)
    evidence("arena", "available" if finite or kind == "infinite" else "unavailable", reason)
    evidence("source_contract", "available", "full compiled source correspondence; probability law unknown")
    evidence("continuation_target", "available", "same-source total task; numerical outputs require acquired presentation")
    evidence("kernel", "available", "structural equality kernels exist for the full actual family")
    evidence("layered_spectrum", "available", "source-bound weak refinement; counts require finite acquisition")
    count_kind = "available" if finite else "not-applicable" if kind == "infinite" else "unavailable"
    for field in ("escape_pairs", "unique_capture"):
        evidence(field, count_kind, "complete certified domain and bidirectional table reflection" if finite else reason)
    n = reading["arena"]["cardinality"]
    evidence("escape_rate", "available" if n is not None and n > 1 else
             "not-applicable" if kind == "infinite" or n is not None else "unavailable",
             "N(N-1) ordered off-diagonal pairs" if n is not None and n > 1 else
             "finite pair rate requires complete finite N>1" if kind == "infinite" or n is not None else reason)
    source = reading["source_contract"]
    source.pop("supplied_binding")
    source.pop("supplied_acquisition")
    source.update(kind="typed-source", binding=request["binding"], acquisition=acquisition)
    reading["continuation_target"]["scope"] = ("same actual source realization; complete finite total task"
                                               if finite else "same actual source realization; total task")
    if finite:
        reading["arena"]["kind"] = "certified-finite-presentation"
        reading["arena"]["scope_boundary"] = ("counts refer only to the certified whole fiber, restriction or quotient; "
                                               "original theorem remains universal")
        reading["kernel"]["scope"] = "certified readout kernels and supplied layers; no exponential lattice claimed"
    else:
        reading["arena"].update(kind=kind, reason=reason)
    return reading


def produce(row, previous_artifact, analyzer):
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
            pending.append(leaf)
    if pending:
        if not analyzer:
            raise ValueError("fib.analysis_program_missing")
        result = subprocess.run([str(analyzer), "--batch"],
            input=json.dumps([x["request"] for x in pending]),
            text=True, capture_output=True, check=False)
        if result.returncode not in (0, 2):
            raise ValueError(f"fib.analysis_failed:exit={result.returncode}:{result.stderr}")
        outputs = json.loads(result.stdout)
        if not isinstance(outputs, list) or len(outputs) != len(pending):
            raise ValueError("fib.analysis_incomplete")
        for leaf, reading in zip(pending, outputs):
            leaf["reading"] = _qualify_compiled(leaf["request"], reading)
        rejected = any(x["disposition"]["status"] == "refuted" for x in outputs)
        if (result.returncode == 2) != rejected:
            raise ValueError("fib.analysis_exit_mismatch")
    validate(partition)
    stats = {'generated': len(pending), 'reused': reused,
             'unavailable': sum(x['request'] is None for x in partition['applications'])}
    print(f'LEAN_INSPECTOR_FIB module={row["module"]} generated={len(pending)} reused={reused} unavailable='
          f'{stats["unavailable"]}')
    return stats


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
    return {"schema_version": 1, "applications": records,
            "authority": "downstream analysis; proof and admission fields unchanged"}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('report', type=Path)
    parser.add_argument('--target', action='append', default=[])
    args = parser.parse_args()
    print(json.dumps(consume(args.report, args.target), sort_keys=True))
