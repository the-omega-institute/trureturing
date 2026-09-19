"""Produce real family/fixed fixture evidence for the ordinary managed tests.

Lake owns compilation and native coherence; Inspector and materials.compact own
the report. This fixture chooses inputs and never manufactures accepted rows.
"""
import hashlib
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "tools/lean-inspector"))
import materials


PREFIX = "LeanInformationAudit.Tests.RegistrationGates."
FIXTURES = ["DependentFamilyOriginal", "DependentFamilyWitnesses", "DependentFamily",
            "DependentFamilySidecar", "DependentFamilyControls", "DependentFamilyMissingPin",
            "DependentFamilyDictionaries", "DependentFamilyUnicode", "DependentFamilyUnresolved",
            "DependentFamilyFixedControl"]


def build(producer, production):
    targets = (["LeanInformationAudit.Registry.Family", "reportInspector"] if production
               else [PREFIX + name for name in FIXTURES])
    subprocess.run(["dotnet", str(producer), "with-cache-writer", "--", "lake", "build", *targets],
                   cwd=ROOT, check=True)


def produce(destination, producer):
    destination.mkdir(parents=True, exist_ok=True)
    cache = ["dotnet", str(producer)]
    # Coherence/assertion fixtures participate in the build. These sources alone
    # own the deliberately selected report occurrences and imported definitions.
    reported = [PREFIX + name for name in FIXTURES[:5] + FIXTURES[7:10]]
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
    return artifact


if __name__ == "__main__":
    operation = sys.argv[1]
    producer = pathlib.Path(sys.argv[2]).resolve()
    if operation == "build-producer":
        build(producer, production=True)
    elif operation == "build-fixtures":
        build(producer, production=False)
    elif operation == "produce":
        print(produce(pathlib.Path(sys.argv[3]).resolve(), producer))
    else:
        raise SystemExit("unknown family fixture operation")
