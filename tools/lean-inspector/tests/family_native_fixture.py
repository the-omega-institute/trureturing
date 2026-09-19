"""Produce real family/fixed fixture evidence for the ordinary managed tests.

Lake owns compilation and native coherence; Inspector and materials.compact own
the report. This fixture chooses inputs and never manufactures accepted rows.
"""
import hashlib
import json
import os
import pathlib
import shutil
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "tools/lean-inspector"))
import materials
import publication


PREFIX = "LeanInformationAudit.Tests.RegistrationGates."
FIXTURES = ["DependentFamilyOriginal", "DependentFamilyWitnesses", "DependentFamily",
            "DependentFamilySidecar", "DependentFamilyControls", "DependentFamilyMissingPin",
            "DependentFamilyDictionaries", "DependentFamilyUnicode", "DependentFamilyUnresolved",
            "DependentFamilyFixedControl", "DependentFamilyReuse", "DependentFamilyWrongRegistration"]


def build(producer, production):
    targets = (["LeanInformationAudit.Registry.Family", "reportInspector"] if production
               else [PREFIX + name for name in FIXTURES])
    subprocess.run(["dotnet", str(producer), "with-cache-writer", "--", "lake", "build", *targets],
                   cwd=ROOT, check=True)


def produce(destination, producer, names=None):
    destination.mkdir(parents=True, exist_ok=True)
    cache = ["dotnet", str(producer)]
    # Coherence/assertion fixtures participate in the build. These sources alone
    # own the deliberately selected report occurrences and imported definitions.
    reported = [PREFIX + name for name in (names if names is not None
                else FIXTURES[:5] + FIXTURES[7:])]
    spool = destination / "native.spool.json"
    material_spool = destination / "native.material-spool"
    args = ["--output", str(spool), "--material-spool", str(material_spool)]
    for module in reported:
        source = "tools/lean-inspector/" + module.replace(".", "/") + ".lean"
        digest = hashlib.sha256((ROOT / source).read_bytes()).hexdigest()
        args.extend([module, source, "sha256:" + digest])
    subprocess.run([*cache, "with-cache-reader", "--", "lake", "env",
                    str(ROOT / ".lake/build/lean-inspector/producer/bin/reportInspector"), *args],
                   cwd=ROOT, check=True)
    artifact = destination / "native.json"
    materials.compact(spool, material_spool, artifact, ROOT / "lean-report-inputs.json")
    publication.validate_rows(artifact, pathlib.Path(str(artifact) + ".materials.zip"),
                              manifest=ROOT / "lean-report-inputs.json")
    return artifact


def compilation_stamps(root):
    """Observe actual compiler outputs, including unchanged dependencies."""
    return {str(p.relative_to(root)): [p.stat().st_mtime_ns, p.stat().st_size]
            for p in (root / ".lake").rglob("*.olean")}


def transition(operation, producer, destination):
    global ROOT
    source = ROOT
    private = destination / "repository"
    owners = ["DependentFamily", "DependentFamilyReuse", "DependentFamilyFixedControl"]
    if operation == "transition-snapshot":
        # Read the existing warm cache under its ordinary reader lease. This
        # private copy has no Git/worktree identity and never writes the donor.
        private.mkdir(parents=True)
        for name in ["D5", "tools/lean-inspector"]:
            shutil.copytree(source / name, private / name,
                            ignore=shutil.ignore_patterns(".lake", "__pycache__"))
        for name in ["lean-toolchain", "lake-manifest.json", "lakefile.toml", "lean-report-inputs.json"]:
            shutil.copy2(source / name, private / name)
        command = (["cp", "-cR"] if sys.platform == "darwin" else ["cp", "-a", "--reflink=auto"])
        subprocess.run([*command, str(source / ".lake"), str(private / ".lake")], check=True)
        policy = json.loads((private / "lean-report-inputs.json").read_text())
        policy["report_semantic_version"] -= 1
        (private / "lean-report-inputs.json").write_text(json.dumps(policy, indent=2) + "\n")
        # Establish real prior-version plans independently of the donor's
        # version. These fixture source bytes then stay fixed across transition.
        for name in owners:
            path = private / "tools/lean-inspector" / (PREFIX + name).replace(".", "/")
            path = path.with_suffix(".lean")
            with path.open("a") as out:
                out.write("\n-- Private warm-transition fixture.\n")
        return
    ROOT = private
    if operation == "transition-prior-build":
        build(producer, production=False)
    elif operation == "transition-prior-produce":
        produce(destination / "prior", producer)
        rows = json.loads((destination / "prior/native.json").read_text())["modules"]
        for name in owners:
            row = next(r for r in rows if r["module"] == PREFIX + name)
            expected = json.loads((private / "lean-report-inputs.json").read_text())["report_semantic_version"]
            if row["information_templates"]["compatibility_version"] != expected:
                raise AssertionError("prior producer compatibility mismatch")
            records = row["information_templates"]["records"]
            if not records or any(r["state"] != "declared_validated" for r in records):
                raise AssertionError("prior plan is not valid: " + name)
        (destination / "before.json").write_text(json.dumps(compilation_stamps(private)))
    elif operation == "transition-current-build":
        # Only this real registered input changes between the two ordinary builds.
        shutil.copyfile(source / "lean-report-inputs.json", private / "lean-report-inputs.json")
        build(producer, production=False)
        before = json.loads((destination / "before.json").read_text())
        after = compilation_stamps(private)
        changed = sorted(p for p in after if before.get(p) != after[p])
        for name in owners:
            path = ".lake/build/lib/lean/" + (PREFIX + name).replace(".", "/") + ".olean"
            if path not in changed:
                raise AssertionError("stale compiled plan owner: " + name)
        # The source theorem, witnesses and missing-pin fixture have no import
        # edge from a plan owner. All other requested fixtures do.
        expected = {".lake/build/lib/lean/" + (PREFIX + name).replace(".", "/") + ".olean"
                    for name in FIXTURES if name not in
                    ["DependentFamilyOriginal", "DependentFamilyWitnesses", "DependentFamilyMissingPin"]}
        if set(changed) != expected:
            raise AssertionError("incorrect affected compilation scope: " + repr(changed))
        # Observe Lake's actual requested closure, independently of the owner
        # registry. Cached but unrequested oleans are accounted for separately.
        requested = set()
        for name in FIXTURES:
            module = (PREFIX + name).replace(".", "/")
            requested.add(".lake/build/lib/lean/" + module + ".olean")
            setup = json.loads((private / (".lake/build/ir/" + module + ".setup.json")).read_text())
            for arts in setup["importArts"].values():
                for path in arts[0]:
                    if path.endswith(".olean") and "/.lake/" in path:
                        requested.add(".lake/" + path.split("/.lake/", 1)[1])
        if not requested.issubset(after):
            raise AssertionError("Lake setup references an absent compiled dependency")
        (destination / "after.json").write_text(json.dumps(after))
        (destination / "affected.json").write_text(json.dumps(dict(
            compiled=changed, requested_olean_count=len(requested),
            requested_oleans_reused=len(requested) - len(changed),
            cached_olean_outputs_unchanged=len(after) - len(changed)), indent=2))
        print("WARM_TRANSITION " + (destination / "affected.json").read_text(), flush=True)
    elif operation == "transition-current-produce":
        produce(destination / "current", producer)
        rows = json.loads((destination / "current/native.json").read_text())["modules"]
        for name in owners:
            row = next(r for r in rows if r["module"] == PREFIX + name)
            if any(r["state"] != "declared_validated" for r in row["information_templates"]["records"]):
                raise AssertionError("current plan is stale: " + name)
    elif operation == "transition-reuse":
        build(producer, production=False)
        if compilation_stamps(private) != json.loads((destination / "after.json").read_text()):
            raise AssertionError("unchanged input recompiled Lean modules")
        produce(destination / "reused", producer)
        if (destination / "current/native.json").read_bytes() != (destination / "reused/native.json").read_bytes():
            raise AssertionError("unchanged rerun changed native evidence")
        if output := os.environ.get("STRATALINT_NATIVE_RESULT_DIR"):
            output = pathlib.Path(output)
            output.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(destination / "affected.json", output / "family-warm-transition.json")
        print("[PASS] warm_transition_unchanged_reuses_all", flush=True)
    else:
        raise SystemExit("unknown transition operation")


if __name__ == "__main__":
    operation = sys.argv[1]
    producer = pathlib.Path(sys.argv[2]).resolve()
    if operation.startswith("transition-"):
        transition(operation, producer, pathlib.Path(sys.argv[3]).resolve())
    elif operation == "build-producer":
        build(producer, production=True)
    elif operation == "build-fixtures":
        build(producer, production=False)
    elif operation == "produce":
        destination = pathlib.Path(sys.argv[3]).resolve()
        print(produce(destination, producer))
        # Independent native environments, followed by exact field comparison.
        # Imports remain imports even when they are also requested report roots.
        import json
        full = json.loads((destination / "native.json").read_text())
        for name in ["DependentFamilyControls", "DependentFamilyUnicode",
                     "DependentFamilySidecar", "DependentFamilyUnresolved"]:
            path = produce(destination / name, producer, [name])
            row = json.loads(path.read_text())["modules"][0]
            expected = next(m for m in full["modules"] if m["module"] == PREFIX + name)
            if row != expected:
                raise AssertionError("batch-dependent native module: " + name)
            print("[PASS] independent_batch_identical " + name)

    else:
        raise SystemExit("unknown family fixture operation")
