"""Check the public list and array search equations after replacing a Fin bound proof."""

import json
import os
from pathlib import Path
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SITES = {("Init.Data." + c + ".Find", c + ".findFinIdx?_eq_pmap_findIdx?") for c in ("List", "Array")}


def sites(certificates):
    result = {tuple(site) for site in certificates}
    if not result <= SITES or len(result) != len(certificates):
        raise ValueError("invalid finite-index proof replacement certificate")
    return result


def certificates(product):
    library = product / "lib"
    if not any((library / ("Omega" + owner.replace(".", "/") + ".olean")).is_file() for owner, _ in SITES):
        return []
    result = subprocess.run(["lake", "env", "lean", "--run", HERE / "FinBoundCheck.lean", library],
                            cwd=ROOT, stdout=subprocess.PIPE, text=True, check=True)
    checked = [json.loads(line) for line in result.stdout.splitlines()]
    with tempfile.TemporaryDirectory(dir=product) as temp:
        client = Path(temp) / "FinSearchClient.lean"
        for owner, name in sorted(sites(checked)):
            carrier = name.partition(".")[0]
            for strict in (False, True):
                imports = "import Omega" + owner + "\nopen Omega" if strict else "import " + owner
                env = dict(os.environ, LEAN_PATH=str(library)) if strict else os.environ
                header = (f"module\nprelude\n{imports}\nuniverse u\n"
                          f"example {{α : Type u}} {{xs : {carrier} α}} {{p : α → Bool}} :\n"
                          f"    Eq ({carrier}.findFinIdx? p xs) ")
                value = f" :=\n  @{name} α xs p\n"
                endpoint = (f"(Option.pmap (fun i hit => Fin.mk i (And.left "
                            f"(Iff.mp {carrier}.findIdx?_eq_some_iff_findIdx_eq hit))) "
                            f"({carrier}.findIdx? p xs) (fun _ h => h))")
                client.write_text(header + endpoint + value)
                subprocess.run(["lean", client], cwd=ROOT, env=env, check=True)
                client.write_text(header + "Option.none" + value)
                invalid = subprocess.run(["lean", client], cwd=ROOT, env=env, capture_output=True, text=True)
                if invalid.returncode == 0 or "type mismatch" not in (invalid.stdout + invalid.stderr).lower():
                    raise ValueError(f"changed index-search result was not rejected as a type mismatch for {name}")
    return checked
