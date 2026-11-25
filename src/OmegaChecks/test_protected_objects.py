"""Compile protected and candidate OmegaMath fixtures through the publication comparator."""
import os
from pathlib import Path
import subprocess
import tempfile

from portable import AUDIT, ROOT, output
from strict_lake import strict_config

MODULE = "OmegaMath.StandaloneFixture"
HEADER = "module\nprelude\npublic import OmegaInit.Prelude\n@[expose] public section\nnamespace Omega\n"
OBJECT = "def Subject (p : Prop) : Prop := p\n"
THEOREM = "theorem stable (p : Prop) (h : p) : Subject p := h\n"


def compile_source(lean, search, folder, body, header=HEADER):
    file = folder.joinpath(*MODULE.split(".")).with_suffix(".lean")
    file.parent.mkdir(parents=True, exist_ok=True)
    file.write_text(header + body + "end Omega\n")
    subprocess.run([lean, "-R", folder, "-o", file.with_suffix(".olean"), file],
                   cwd=ROOT, env={**os.environ, "LEAN_PATH": search}, check=True)
    return os.pathsep.join([str(folder), search])


def check():
    lean = output("lake", "env", "printenv", "LEAN").strip()
    for profile in (["-f", strict_config()], []):
        search = output("lake", *profile, "env", "printenv", "LEAN_PATH").strip()
        with tempfile.TemporaryDirectory(prefix="omega-protected-") as temp:
            base = compile_source(lean, search, Path(temp) / "base", OBJECT + THEOREM)
            for body, marker in [
                (OBJECT + THEOREM + "theorem extra (p : Prop) : p → p := fun x => x\n", ""),
                (OBJECT + THEOREM + "private def hiddenPrime (p : Prop) : Prop := p\n", "new OmegaMath object"),
                (OBJECT + THEOREM + "structure HiddenObject where value : Nat\n", "new OmegaMath object"),
                (OBJECT + THEOREM + "axiom fake : ∀ p : Prop, p\n", "new OmegaMath object"),
                ("def Subject (_p : Prop) : Prop := True\ntheorem stable (p : Prop) (_h : p) : Subject p := True.intro\n",
                 "Subject"),
                (OBJECT, "removed protected declaration"),
                (OBJECT + "theorem stable (p : Prop) : p → p → p := fun h _ => h\n", "stable"),
                (OBJECT + "def stable := Subject\n", "kind changed"),
            ]:
                new = compile_source(lean, search, Path(temp) / "candidate", body)
                result = subprocess.run([AUDIT, "--protected-objects", base, new, MODULE, "--", MODULE],
                                        cwd=ROOT, capture_output=True, text=True)
                if bool(result.returncode) != bool(marker) or marker not in result.stderr:
                    raise RuntimeError(f"Expected {marker!r}: {result.stdout}{result.stderr}")
            result = subprocess.run([AUDIT, "--protected-objects", base, new, MODULE, "--"],
                                    cwd=ROOT, capture_output=True, text=True)
            if not result.returncode or "removed protected OmegaMath module" not in result.stderr:
                raise RuntimeError(f"Expected missing module: {result.stdout}{result.stderr}")
            for folder, modifier in [("base", "public "), ("candidate", "")]:
                directory = Path(temp) / folder
                file = directory / "OmegaMath.lean"
                file.write_text(f"module\nprelude\n{modifier}import {MODULE}\n")
                subprocess.run([lean, "-R", directory, "-o", file.with_suffix(".olean"), file], cwd=ROOT,
                               env={**os.environ, "LEAN_PATH": str(directory) + os.pathsep + search}, check=True)
            result = subprocess.run([AUDIT, "--protected-objects", base, new, "OmegaMath", "--", "OmegaMath"],
                                    cwd=ROOT, capture_output=True, text=True)
            if not result.returncode or "no longer re-exports protected module" not in result.stderr:
                raise RuntimeError(f"Expected hidden public import: {result.stdout}{result.stderr}")
            legacy = ("inductive Carrier where | one\n"
                      "def Predicate (_ : Nat) : Prop := True\n"
                      "theorem Helper (n : Nat) : Predicate n := True.intro\n")
            base = compile_source(lean, search, Path(temp) / "base", legacy)
            for addition, marker in [
                ("theorem extra (r : Carrier) : Eq r r := Eq.refl r\n", "statement uses project object Omega.Carrier"),
                ("theorem extra (n : Nat) : Predicate n := Helper n\n",
                 "statement uses project object Omega.Predicate"),
                ("def extra (n : Nat) : Predicate n := Helper n\n", "statement uses project object Omega.Predicate"),
                ("namespace More\nexport Omega (Helper)\nend More\n", "statement uses project object Omega.Predicate"),
                ("private theorem inner (n : Nat) : Predicate n := Helper n\n"
                 "theorem extra (n : Nat) : True := inner n\n", ""),
            ]:
                new = compile_source(lean, search, Path(temp) / "candidate", legacy + addition)
                result = subprocess.run([AUDIT, "--protected-objects", base, new, MODULE, "--", MODULE],
                                        cwd=ROOT, capture_output=True, text=True)
                if bool(result.returncode) != bool(marker) or marker not in result.stderr:
                    raise RuntimeError(f"Expected {marker!r}: {result.stdout}{result.stderr}")
            port_header = HEADER.replace("OmegaInit.Prelude", "OmegaMathlib.Data.Nat.Prime.Defs")
            old_helper = "def Historical (p : Prop) : Prop := And p True\n"
            old_object = "def Subject (n : Nat) : Prop := Historical (OmegaMathlib.Nat.Prime n)\n"
            alias = "abbrev Subject := OmegaMathlib.Nat.Prime\n"
            witness = ("theorem bridge (n : Nat) : Iff (Historical (OmegaMathlib.Nat.Prime n)) "
                       "(OmegaMathlib.Nat.Prime n) := Iff.intro And.left (fun h => And.intro h True.intro)\n")
            base = compile_source(lean, search, Path(temp) / "base", old_helper + old_object, port_header)
            for body, expected in [
                (alias + witness, ""),
                (old_object + "abbrev direct := OmegaMathlib.Nat.Prime\n", ""),
                (old_object + "abbrev copy := Subject\n", "new OmegaMath object"),
                (alias, "missing all-input correspondence"),
                (alias + "theorem bridge (n : Nat) : Iff (Subject n) (Subject n) := "
                 "Iff.intro (fun h => h) (fun h => h)\n", "missing all-input correspondence"),
            ]:
                new = compile_source(lean, search, Path(temp) / "candidate", old_helper + body, port_header)
                result = subprocess.run([AUDIT, "--protected-objects", base, new, MODULE, "--", MODULE],
                                        cwd=ROOT, capture_output=True, text=True)
                if bool(result.returncode) != bool(expected) or expected not in result.stderr:
                    raise RuntimeError(f"Expected {expected!r}: {result.stdout}{result.stderr}")


if __name__ == "__main__":
    check()
