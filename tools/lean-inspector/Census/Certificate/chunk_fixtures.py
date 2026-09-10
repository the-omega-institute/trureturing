"""Exercise multi-chunk binding against independent synthetic wire authorities."""

import json
import os
import re

from Certificate.emission import manifest_source, bucket_sources, name, string, write_module
from resources import run


def check_chunks(repository, directory):
    root = directory / "chunks"
    rows = [{"theorem_name": ["str", ["anonymous"], "T"],
             "statement_id": "sha256:" + format(n, "064x")} for n in range(125)]
    keys = [("Fixture", "ns(n0,1:T)", row["statement_id"]) for row in rows]
    assembly = manifest_source(rows, keys, "fixture-head", "digest", "CensusRun.Root", b=1)
    original = bucket_sources(rows, keys, b=1)["CensusRun.Range1_0"]
    wire = "#[" + ",\n".join(
        f"StatementKey.mk {name(row['theorem_name'])} {string(row['statement_id'])}" for row in rows) + "]"
    source = write_module(root, "CensusRun.Root", assembly)
    for module, contents in bucket_sources(rows, keys, b=1).items():
        write_module(root, module, contents)
    bucket = root / "CensusRun/Range1_0.lean"
    driver = write_module(root, "ChunkBinding", "import LeanInformationAudit.Census.Publish\n"
        "open Lean Elab Command LeanInformationAudit\n"
        f"def expectedRows : Array StatementKey := {wire}\n"
        "run_cmd do\n"
        f"  let env <- CensusProjection.elaborateFinalSource (<- IO.FS.readFile {string(str(source))})\n"
        f"    {string(str(source))} `CensusRun.Root {{}} (dataOnly := true)\n"
        "  liftTermElabM <| CensusProjection.checkFinalEnvironment env (some `CensusRun.Root)\n"
        f"  searchPathRef.modify (fun paths => System.FilePath.mk {string(str(source.with_suffix('.compile')))} :: paths)\n"
        "  withEnv env <| liftTermElabM do\n"
        "    CensusManifest.bindEmittedManifest\n"
        "      { headSha := \"fixture-head\", reportSha256 := \"digest\", theorems := expectedRows }\n"
        "      `CensusRun.Root expectedRows `CensusRun.manifest `CensusRun.reportKeys\n")
    ordered = "decodeIds 100 CensusRun.Range1_0.reportKeys.chunk0, decodeIds 25 CensusRun.Range1_0.reportKeys.chunk1"
    cases = [("noncomputableMultiChunkBound", original, True),
             ("chunkReorderedBetweenSides", original.replace(ordered,
                 "decodeIds 25 CensusRun.Range1_0.reportKeys.chunk1, decodeIds 100 CensusRun.Range1_0.reportKeys.chunk0"), False),
             ("wrongChunkArity", original.replace("decodeIds 100 CensusRun.Range1_0.reportKeys.chunk0",
                 "decodeIds 99 CensusRun.Range1_0.reportKeys.chunk0"), False),
             ("chunkLiteralBinding", re.sub(r"(CensusRun.Range1_0.reportKeys.chunk0 : Nat := )(0x[0-9a-f]+)",
                 lambda m: m[1] + hex(int(m[2], 0) + 1), original, count=1), False)]
    outcomes = []
    try:
        for label, text, accepted in cases:
            bucket.write_text(text)
            try:
                run(["lake", "env", "lean", "-R", str(root), str(driver)], root / label, "process",
                    cwd=repository, env=dict(os.environ, LEAN_PATH=str(root), LEAN_NUM_THREADS="1"))
            except RuntimeError:
                assert not accepted
                log = (root / label / "process.log").read_text()
                expected = "component=statement_id_nat" if label == "chunkLiteralBinding" else "component=report_keys_binding"
                assert expected in log, log
            else:
                assert accepted, label + " accepted"
            outcomes.append({"name": label, "status": "accepted" if accepted else "rejected",
                             "keys": 125, "chunks_per_side": 2})
    finally:
        bucket.write_text(original)
    (root / "fixtures.json").write_text(json.dumps(outcomes, indent=2) + "\n")
    return outcomes
