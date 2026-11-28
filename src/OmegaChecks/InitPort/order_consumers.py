"""Compile common order propositions and reject reversed comparisons on both public backends."""
import json
from pathlib import Path
import subprocess
import tempfile

import public_clients


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
OWNERS = ["Init.Internal.Order.Basic", "Init.Internal.Order.Lemmas", "Init.Internal.Order.MonadTail"]
TRANSFORMERS = {"Lean.Order.monotone_readerTRun": "instPartialOrderReaderT",
                "Lean.Order.monotone_stateTRun": "instPartialOrderStateT",
                "Lean.Order.monotone_stateRefT'Run": "instPartialOrderStateRefT'"}


def gap(name):
    operand = TRANSFORMERS.get(name, "instOrderPi")
    return (f"missing type dependencies: Omega.Lean.Order.{operand}. "
            "A definitionally equal reformulation checks in the public kernels.")


def sites(checks):
    result = set()
    for owner, name in checks:
        parts = name.split(".")
        if owner == "Init.Internal.Order.Lemmas":
            supported = (len(parts) == 4 and parts[:2] == ["Lean", "Order"] and
                         parts[2] in {"List", "Array", "Option"} and parts[3].startswith("monotone_"))
        elif owner == "Init.Internal.Order.MonadTail":
            supported = name == "Lean.Order.MonadTail.monotone_bind_right"
        else:
            supported = (owner == "Init.Internal.Order.Basic" and parts[:2] == ["Lean", "Order"] and
                         len(parts) == 3 and (parts[2].startswith("monotone_") or parts[2] in {"chain_apply", "is_meet_pi"}))
        if not supported or (owner, name) in result:
            raise ValueError(f"invalid pointwise order certificate for {name}")
        result.add((owner, name))
    return result


def certificates(product):
    library = product / "lib"
    all_checked = []
    for owner in OWNERS:
        if (library / ("Omega" + owner.replace(".", "/") + ".olean")).is_file():
            all_checked.extend(_check_module(product, library, owner))
    return all_checked


def _check_module(product, library, owner):
    with tempfile.TemporaryDirectory(dir=product) as temp:
        result = subprocess.run(["lake", "env", "lean", "--run", HERE / "PointwiseOrderCheck.lean", library, owner, temp],
                                cwd=ROOT, stdout=subprocess.PIPE, text=True, check=True)
        checked = [json.loads(line) for line in result.stdout.splitlines()]
        names = {name for _, name in sites(checked)}
        if not names:
            return []
        public_clients.check(library, Path(temp), names, "Reversed")
        return checked
