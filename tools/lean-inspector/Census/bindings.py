"""Retain the Lean producer's binding results across census caches and output."""

import hashlib
import re

from streaming import canonical


def incomplete(diagnostic):
    return {"schema_version": 1, "compatibility_version": 5, "query_completed": False,
            "diagnostic": diagnostic, "records": [], "source_inputs": []}


def absent():
    return dict(incomplete(None), query_completed=True)


def validate(value):
    """Check transport shape; Lean alone assesses provenance and the native join."""
    def require(ok):
        if not ok:
            raise ValueError("IE-C050 ClosedTruthReadout reason=incomplete_closure rule=dtr.census_cache")

    require(isinstance(value, dict) and set(value) == {
        "schema_version", "compatibility_version", "query_completed", "diagnostic", "records", "source_inputs"})
    require(value["schema_version"] == 1 and value["compatibility_version"] == 5)
    require(type(value["query_completed"]) is bool)
    require(isinstance(value["records"], list) and isinstance(value["source_inputs"], list))
    if value["query_completed"]:
        require(value["diagnostic"] is None)
    else:
        require(isinstance(value["diagnostic"], str) and bool(value["diagnostic"]))
        require(not value["records"] and not value["source_inputs"])
    seen = set()
    for row in value["records"]:
        require(isinstance(row, dict) and {"key", "state", "certificate", "diagnostic"} <= row.keys())
        key = canonical(row["key"])
        require(key not in seen)
        seen.add(key)
        state = row["state"]
        require(state in {"undeclared", "declared_unresolved", "declared_validated"})
        if state == "declared_validated":
            certificate = row["certificate"]
            require(isinstance(certificate, dict) and certificate.get("key") == row["key"])
            require(isinstance(certificate.get("evidence_ref"), str) and
                    re.fullmatch(r"[0-9a-f]{64}", certificate["evidence_ref"]) is not None)
            require(row["diagnostic"] is None)
        else:
            require(row["certificate"] is None)
            require(isinstance(row["diagnostic"], str) and bool(row["diagnostic"]))
            if state == "undeclared":
                key = row["key"]
                require(isinstance(key, dict) and all(isinstance(key.get(k), str)
                        for k in ("root", "catalog", "theorem")))
                expected = (f'IE-C050 ClosedTruthReadout key={key["root"]}/{key["catalog"]}/{key["theorem"]} '
                            'reason=unclassified_form rule=dtr.missing_declaration site="" readout="" '
                            'provenance={"argument_inputs":[],"extraction_inputs":[],"plan_identity":null,'
                            '"rule":"dtr.missing_declaration","site":"","template_key":null}')
                require(row["diagnostic"] == expected)
    seen = set()
    for source in value["source_inputs"]:
        require(isinstance(source, dict) and set(source) == {"path", "sha256"})
        path = source["path"]
        require(isinstance(path, str) and bool(path) and not path.startswith("/") and
                "\\" not in path and all(p not in {"", ".", ".."} for p in path.split("/")))
        require(path not in seen)
        seen.add(path)
        require(isinstance(source["sha256"], str) and
                re.fullmatch(r"[0-9a-f]{64}", source["sha256"]) is not None)
    return value


def sources_current(repository, value):
    validate(value)
    for source in value["source_inputs"]:
        path = repository / source["path"]
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != source["sha256"]:
            return False
    return True
