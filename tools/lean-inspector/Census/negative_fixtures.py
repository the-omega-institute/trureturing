"""Real olean negatives for the streaming ownership and scope boundary."""

import json
import os
import pathlib
import shutil
import subprocess
import sys

from phases import enumerate_domain, external_graph, read, write
from resources import run
from streaming import enumerate_oleans, freshness

PREFIX = "LeanInformationAuditRegTests.Research.Census.Query."


def name_key(text):
    result = "n0"
    for part in text.split("."):
        result = f"ns({result},{len(part.encode('utf-8'))}:{part})"
    return result


def key(module, declaration, number=0):
    return [PREFIX + module, name_key("LeanInformationAudit.Tests.Census.Query." + declaration), "sha256:" + format(number, "064x")]


def lean_env(repository):
    env = json.loads(subprocess.check_output(["lake", "env", sys.executable, "-c",
        "import os,json;print(json.dumps(dict(os.environ)))"], cwd=repository))
    env["LEAN_NUM_THREADS"] = "1"
    # Native Census compilation needs every source root supplied by Lake.
    return env


def lean(repository, directory, program, args, label, env):
    binary = shutil.which("lean", path=env["PATH"])
    if program in ("scan.lean", "membership.lean"):
        from native import build
        native = build(repository, program, env)
        result = run([str(native), *map(str, args)], directory, label, cwd=repository, env=env,
                     budget_gb=1 if program == "scan.lean" else 0.5)
        if program == "scan.lean":
            from extraction import detached_records
            path = pathlib.Path(args[2])
            temporary = path.with_suffix(".finished")
            with path.open() as source, temporary.open("wb") as out:
                from streaming import canonical
                for row in detached_records(source, lambda module: "tools/lean-inspector/" +
                        module.replace(".", "/") + ".lean"):
                    out.write(canonical(row))
            os.replace(temporary, path)
            from extraction import add_collision_identities
            add_collision_identities(repository, path, read(args[0]), pathlib.Path(args[1]),
                lambda module: "tools/lean-inspector/" + module.replace(".", "/") + ".lean", env)
        return result
    return run([binary, "-DmaxRecDepth=100000", "-DmaxHeartbeats=0", "--run",
                str(repository / "tools/lean-inspector/Census" / program), *map(str, args)],
               directory, label, cwd=repository, env=env)



def truth_export_identity(repository, directory):
    identity = directory / "identity.json"
    driver = directory / "Identity.lean"
    driver.write_text("import LeanInformationAuditRegAnalysis.Census.Report\n" +
        "#eval IO.FS.writeFile " + json.dumps(str(identity)) +
        " LeanInformationAudit.DispositionCensus.truthExportIdentity.compress\n")
    run(["lake", "env", "lean", str(driver)], directory, "identity", cwd=repository, env=lean_env(repository))
    return read(identity)
