"""Verify ordinary imports of complete explicit signatures and diagnostics for their changed versions."""
import json
import os
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]


def check(library, directory, names, changed):
    for variant in ("Official", "Strict"):
        env = dict(os.environ, LEAN_PATH=str(library)) if variant == "Strict" else os.environ
        prefix = "Omega." if variant == "Strict" else ""
        subprocess.run(["lean", directory / (variant + ".lean")], env=env, cwd=ROOT, check=True)
        negative = subprocess.run(["lean", "--json", directory / (variant + changed + ".lean")],
                                  env=env, cwd=ROOT, capture_output=True, text=True)
        errors = [r["data"].splitlines() for line in negative.stdout.splitlines()
                  if (r := json.loads(line))["severity"] == "error"]
        if (not negative.returncode or len(errors) != len(names) or
                any(len(lines) < 2 or lines[0] != "Type mismatch" for lines in errors) or
                {lines[1].strip().removeprefix("@") for lines in errors} != {prefix + name for name in names}):
            raise ValueError(f"{variant} did not reject the changed result at every public declaration")
