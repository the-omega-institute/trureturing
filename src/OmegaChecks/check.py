"""Run from anywhere in this checkout. --incremental temporarily edits two clean sources."""
import argparse
import hashlib
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
LIB = ROOT / ".lake/build/lib/lean"
INIT = ["OmegaInit.Prelude", "OmegaInit.Data.Nat", "OmegaInit.Data.Ratio", "OmegaInit"]
TOPIC = "OmegaMath.Projective"
CONSUMER = "OmegaChecks.ProjectiveOverlap"
LEGACY = "D5.S1.Digit.Admissibility.SquarePrependOneAppendTwentyFive"
TARGETS = ["OmegaMath", CONSUMER, "OmegaChecks.Examples", "OmegaChecks.Mixed", LEGACY]


def run(*args):
    return subprocess.run(args, cwd=ROOT, text=True, check=True)


def build():
    run("make", "lean", "LEAN_TARGETS=" + " ".join(TARGETS))


def audit(name, modules, paths, error=None):
    args = ["lean", "--run", "src/OmegaChecks/Audit.lean", name,
            os.pathsep.join(map(str, paths)), *modules]
    result = subprocess.run(args, cwd=ROOT, capture_output=True, text=True)
    output = result.stdout + result.stderr
    if error is None:
        if result.returncode:
            raise RuntimeError(output)
        print(output.strip(), flush=True)
    elif not result.returncode or error not in output:
        raise RuntimeError(f"Expected audit failure containing {error!r}: {output}")
    else:
        print(f"{name}: rejected ({error})", flush=True)


def check_audits():
    math = [*INIT, TOPIC, "OmegaMath"]
    for root, modules in [("OmegaInit", INIT), ("OmegaMath", math), (CONSUMER, [*INIT, TOPIC, CONSUMER])]:
        audit(root, modules, [LIB])
    with tempfile.TemporaryDirectory(prefix="omega-olean-") as tmp:
        tmp = Path(tmp)
        for name, source, reason in [
            ("UnusedAxiom", "prelude\nimport OmegaMath\naxiom hiddenAssumption : Prop\n",
             "hiddenAssumption"),
            ("ImplicitInit", "import OmegaMath\n", "unknown module prefix 'Init'"),
        ]:
            lean = tmp / f"{name}.lean"
            lean.write_text(source)
            run("lake", "env", "lean", "-R", tmp, "-o", tmp / f"{name}.olean", lean)
            audit(name, [*math, name], [tmp, LIB], reason)


def check_root_d5_import():
    # Give the elaborator the existing file name and a source overlay in memory.
    filename = Path(LEGACY.replace(".", "/") + ".lean")
    source = (ROOT / filename).read_text()
    at = source.index("\nimport ")
    overlay = source[:at] + "\nimport OmegaMath.Projective" + source[at:]
    overlay += """
example (p q k : Omega.Nat) :
    Omega.Ratio.Equivalent
      (Omega.Projective.kappa (p.mul k.succ) (q.mul k.succ))
      (Omega.Projective.kappa p q) :=
  Omega.Projective.kappa_scale p q k
"""
    subprocess.run(["lake", "env", "lean", "--stdin", str(filename)], cwd=ROOT,
                   input=overlay, text=True, check=True)
    print(f"{LEGACY}: source overlay importing {TOPIC} passed", flush=True)


def versions():
    modules = [*INIT, TOPIC, "OmegaMath", CONSUMER, "OmegaChecks.Examples", "OmegaChecks.Mixed", LEGACY]
    files = {m: LIB / (m.replace(".", "/") + ".olean") for m in modules}
    files["Mathlib.Data.Nat.Prime.Basic"] = (
        ROOT / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Data/Nat/Prime/Basic.olean")
    return {name: path.stat().st_mtime_ns for name, path in files.items()}


def check_incremental():
    probes = [
        ("src/OmegaMath/SeparateTopicProbe.lean", "module\nprelude\npublic import OmegaInit\n", set()),
        ("src/OmegaMath/Projective.lean",
         "\npublic theorem Omega.Projective.probe (p : Omega.Nat) : Omega.Eq p p := Omega.Eq.refl\n",
         {TOPIC, "OmegaMath", CONSUMER, "OmegaChecks.Examples", "OmegaChecks.Mixed"}),
        ("src/OmegaInit/Prelude.lean",
         "\npublic theorem Omega.baseProbe (p : Omega.Nat) : Omega.Eq p p := Omega.Eq.refl\n",
         {*INIT, TOPIC, "OmegaMath", CONSUMER, "OmegaChecks.Examples", "OmegaChecks.Mixed"}),
    ]
    for filename, extra, expected in probes:
        path = ROOT / filename
        run("git", "diff", "--quiet", "HEAD", "--", filename)
        before = versions()
        new_file = not expected
        original = b"" if new_file else path.read_bytes()
        modified = original + extra.encode()
        with path.open("xb" if new_file else "wb") as out:
            out.write(modified)
        try:
            build()
            after = versions()
            changed = {m for m in after if before[m] != after[m]}
            print(f"{filename}: rebuilt {sorted(changed)}", flush=True)
            if changed != expected:
                raise RuntimeError(f"Expected {sorted(expected)}")
        finally:
            if path.read_bytes() != modified:
                raise RuntimeError(f"{filename} changed during the probe; leaving it intact")
            if new_file:
                path.unlink()
            else:
                path.write_bytes(original)
            build()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--incremental", action="store_true")
    args = parser.parse_args()
    manifest = ROOT / "lake-manifest.json"
    initial = manifest.read_bytes()
    build()
    check_audits()
    check_root_d5_import()
    if args.incremental:
        check_incremental()
    if manifest.read_bytes() != initial:
        raise RuntimeError("Lake manifest changed")
    print("manifest SHA-256:", hashlib.sha256(initial).hexdigest())
