"""Run from anywhere in this checkout. --incremental temporarily edits two clean sources."""
import argparse
import hashlib
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
LIB = ROOT / ".lake/build/lib/lean"
SRC = ROOT / "src"


def source_modules(root):
    return [root, *(
        ".".join(path.relative_to(SRC).with_suffix("").parts)
        for path in sorted((SRC / root).rglob("*.lean"))
    )]


INIT = source_modules("OmegaInit")
MATH = [*(name for name in INIT if name != "OmegaInit"), *source_modules("OmegaMath")]
FOUNDATION = ["OmegaInit.Prelude", "OmegaInit.Core", "OmegaInit.Data.Nat.Basic", "OmegaInit.Data.Nat.Lemmas"]
DATA = [*FOUNDATION, "OmegaMath.Data.Nat", "OmegaMath.Data.Ratio"]
BASIC = "OmegaMath.Projective.Basic"
TOPIC = "OmegaMath.Projective"
CONSUMER = "OmegaChecks.ProjectiveOverlap"
LEGACY = "D5.S1.Digit.Admissibility.SquarePrependOneAppendTwentyFive"
TARGETS = ["OmegaInit", "OmegaMath", CONSUMER, "OmegaChecks.Examples", "OmegaChecks.Mixed", LEGACY]


def run(*args):
    return subprocess.run(args, cwd=ROOT, text=True, check=True)


def build():
    run("make", "lean", "LEAN_TARGETS=" + " ".join(TARGETS))


def audit(name, modules, paths, error=None):
    args = ["lake", "env", "lean", "--run", "src/OmegaChecks/Audit.lean", "--exact", name,
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
    for root, modules in [("OmegaInit", INIT), ("OmegaMath", MATH), (CONSUMER, [*DATA, BASIC, TOPIC, CONSUMER])]:
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
            audit(name, [*MATH, name], [tmp, LIB], reason)
    # Temporary modules exercise the naming check against the installed upstream artifacts.
    init = "OmegaInit.Data.Nat.Basic"
    prime = "OmegaMath.Data.Nat.Prime.Defs"
    original = "OmegaMath.Projective.Local"
    with tempfile.TemporaryDirectory(prefix="omega-name-") as tmp:
        tmp = Path(tmp)
        for name, declaration, error in [
            (init, "def Omega.Nat.add", "official owner of Nat.add is Init.Prelude"),
            (init, "def OutsideOmega", "public name outside Omega"),
            (init, "def Omega.Nat.unknownOfficialName", "missing official declaration Nat.unknownOfficialName"),
            (prime, "def Omega.Nat.Prime", None),
            (prime, "def Omega.Nat.unknownMathlibName", "missing official declaration Nat.unknownMathlibName"),
            (prime, "def Omega.Nat.add", "official owner of Nat.add is Init.Prelude"),
            (original, "def Omega.Projective.localValue", None),
            (original, "axiom Omega.Projective.unused", "inadmissible declaration Omega.Projective.unused"),
        ]:
            source = tmp / (name.replace(".", "/") + ".lean")
            source.parent.mkdir(parents=True, exist_ok=True)
            marker = "/-! Omega original. -/\n" if name == original else ""
            body = "" if declaration.startswith("axiom ") else " := ∀ p : Prop, p → p"
            source.write_text(f"module\nprelude\n{marker}public {declaration} : Prop{body}\n")
            run("lake", "env", "lean", "-R", tmp, "-o", source.with_suffix(".olean"), source)
            audit(name, [name], [tmp], error)
    example = """prelude
import OmegaInit.Data.Nat.Basic
open Omega
example (a b : Nat) : Eq (Nat.add a b) (Nat.add b a) := Nat.add_comm a b
"""
    subprocess.run(["lake", "env", "lean", "--stdin"], cwd=ROOT, input=example, text=True, check=True)


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
    modules = [*MATH, "OmegaInit", CONSUMER, "OmegaChecks.Examples", "OmegaChecks.Mixed", LEGACY]
    files = {m: LIB / (m.replace(".", "/") + ".olean") for m in modules}
    files["Mathlib.Data.Nat.Prime.Basic"] = (
        ROOT / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Data/Nat/Prime/Basic.olean")
    return {name: path.stat().st_mtime_ns for name, path in files.items()}


def check_incremental():
    probes = [
        ("src/OmegaMath/SeparateTopicProbe.lean", None,
         "module\nprelude\npublic import OmegaInit\n", set()),
        ("src/OmegaMath/Projective.lean", "he.symm\n", "he.symm.symm.symm\n", {TOPIC}),
        ("src/OmegaMath/Projective.lean", None,
         "\npublic theorem Omega.Projective.probe (p : Omega.Nat) : Omega.Eq p p := Omega.Eq.refl\n",
         {TOPIC, "OmegaMath", CONSUMER, "OmegaChecks.Mixed"}),
        ("src/OmegaInit/Prelude.lean", None,
         "\npublic theorem Omega.congrFun' {α β : Sort u} {f g : α → β} (h : Omega.Eq f g) (a : α) : Omega.Eq (f a) (g a) := Omega.congrArg (fun k : α → β => k a) h\n",
         {*INIT, *MATH, CONSUMER, "OmegaChecks.Examples", "OmegaChecks.Mixed"}),
    ]
    for filename, replace, text, expected in probes:
        path = ROOT / filename
        run("git", "diff", "--quiet", "HEAD", "--", filename)
        before = versions()
        new_file = not expected
        original = b"" if new_file else path.read_bytes()
        if replace is None:
            modified = original + text.encode()
        else:
            if original.count(replace.encode()) != 1:
                raise RuntimeError(f"Expected one proof fragment in {filename}")
            modified = original.replace(replace.encode(), text.encode())
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
