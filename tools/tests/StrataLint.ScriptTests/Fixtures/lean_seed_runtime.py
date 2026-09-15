"""Private runtimes shared by the Lean cache and report behavior fixtures."""

FAKE_LAKE = '''#!/usr/bin/env python3
import json, os, pathlib, sys
args = sys.argv[1:]
root = pathlib.Path.cwd()
with (root/"lake-runs").open("a") as log: log.write(" ".join(args)+"\\n")
if args == ["--version"]: print("Lake version 5.0.0-src (Lean version 4.33.0)"); sys.exit(0)
if os.environ.get("LAKE_INITIALIZES_CONFIG"):
    if args == ["env", "lean", "--print-prefix"]:
        config = root / ".lake/config/0"
        config.mkdir(parents=True, exist_ok=True)
        (config / "lakefile.olean").write_text("elaborated package configuration")
        (config / "lakefile.olean.trace").write_text("package trace")
    if args == ["exe", "cache", "get"]:
        olean = root / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Fixture.olean"
        olean.parent.mkdir(parents=True, exist_ok=True)
        olean.write_text("mathlib fixture cache")
        sys.exit(0)
    if args and args[0] == "build":
        seeded = (root / ".lake/build/lib/lean/D5/A.olean").is_file()
        with (root / "project-builds").open("a") as log: log.write(("reused" if seeded else "cold") + "\\n")
        fetches = root / "release-fetches"
        with (root / "project-build-observations").open("a") as log:
            log.write(json.dumps({"seed_present": seeded,
                "release_fetches": len(fetches.read_text().splitlines()) if fetches.exists() else 0}) + "\\n")
if args and args[0] == "build":
    if os.environ.get("LAKE_EXPECT_NO_LAKE") and (root/".lake").exists(): sys.exit(29)
    sys.exit(int(os.environ.get("LAKE_BUILD_FAIL", "0")))
if "--print-prefix" in args: print(pathlib.Path(__file__).parent.parent); sys.exit(0)
if os.environ.get("LAKE_INSPECT_FAIL"): sys.exit(int(os.environ["LAKE_INSPECT_FAIL"]))
output = pathlib.Path(args[args.index("--output")+1])
modules = []
values = args[args.index("--utility-input")+2:]
for index in range(0, len(values), 3):
    module, source, sha = values[index:index+3]
    modules.append({"module": module, "source_path": source, "source_sha256": sha, "imports": [], "declarations": []})
output.write_text(json.dumps({"schema":"stratalint-lean-inspector-spool-v1", "modules":sorted(modules, key=lambda m: m["module"])})+"\\n")
'''


PAIR_PRODUCER = '''#!/usr/bin/env python3
import hashlib, json, os, pathlib, shutil, sys, zipfile
args = sys.argv[1:]
root = pathlib.Path(args[args.index("--repository")+1])
output = pathlib.Path(args[args.index("--output")+1])
sys.path.insert(0, str(root / "tools/lean-inspector"))
from preparation import prepare
state = prepare(root, pathlib.Path(args[args.index("--preparation")+1]))
with (root / "producer-runs").open("a") as log: log.write("entered\\n")
if os.environ.get("PAIR_FAIL"): sys.exit(int(os.environ["PAIR_FAIL"]))
modules = [{"module": str(p.relative_to(root))[:-5].replace("/", "."),
    "source_path": str(p.relative_to(root)), "source_sha256": "sha256:"+hashlib.sha256(p.read_bytes()).hexdigest(),
    "imports": [], "declarations": []} for p in sorted([root/"Trureturing.lean", root/"D5/A.lean"])]
output.write_text(json.dumps({"modules": modules, "schema": "stratalint-raw-lean-report-v2"}, sort_keys=True)+"\\n")
with zipfile.ZipFile(str(output)+".materials.zip", "w"): pass
pathlib.Path(str(output)+".sha256").write_text(hashlib.sha256(output.read_bytes()).hexdigest()+"  "+output.name+"\\n")
pathlib.Path(str(output)+".seed.json").write_text(json.dumps({"runtime_sha256":state["runtime_sha256"]}))
pathlib.Path(str(output)+".execution.json").write_text(json.dumps({"lean_build_succeeded": True}))
logs = pathlib.Path(args[args.index("--log-dir")+1] if "--log-dir" in args else str(output)+".logs")
logs.mkdir(parents=True)
(logs/"producer.log").write_text("produced\\n")
(logs/"subprocess").mkdir()
(logs/"subprocess/stderr.log").write_bytes(b"diagnostic\\x00bytes\\n")
damage = os.environ.get("PAIR_DAMAGE")
if damage == "logs": shutil.rmtree(logs)
if damage == "materials": pathlib.Path(str(output)+".materials.zip").write_text("corrupt")
if damage == "checksum": pathlib.Path(str(output)+".sha256").write_text("bad")
if damage == "report": output.write_text("bad")
'''
