#!/usr/bin/env python3
"""Exact coefficient certificate excluding a single-row positive head gate.

Reads only the pinned Report640 coefficient JSON. The ordinary proof supplies
H_T >= H_empty and the four legal selector lower bounds; this program verifies
their complete coefficient charge. No optimizer, layout scan, or Lean claim.
"""
from argparse import ArgumentParser
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import json

PIN640 = "dd00b0e9f6a93713d437394c368a4ef81407cabd5ecb931ae7753926d9d8c3e4"
parser = ArgumentParser(description=__doc__)
parser.add_argument("--directory", type=Path, default=Path(__file__).resolve().parent)
parser.add_argument("--output", type=Path, default=Path(__file__).with_suffix(".json"))
args = parser.parse_args()
checks = []


def ck(name, condition):
    if not condition:
        raise RuntimeError(name)
    checks.append(name)


source = args.directory / "remaining33_global_root_exclusion_certificate.json"
raw = source.read_bytes()
ck("pinned_report640", sha256(raw).hexdigest() == PIN640)
data = json.loads(raw)
base = [F(x) for x in data["combined512_coefficients"]]
g = F(data["constants"]["g"])
ck("complete512_length", len(base) == 512)
ck("complete512_nonnegative", all(x >= 0 for x in base))
ck("mass_coefficient", g == F(200163067, 201247200))
ck("unit_mass_identity", g + F(data["constants"]["c"]) == 1)

# Reports661--664 add the same guarded9q^2 costs at mode(2,1), index9.
full = base.copy()
guarded = []
for bit, q in enumerate((7, 11, 13, 17, 19)):
    if q == 7:
        continue
    index = 32 * 9 + (1 << bit)
    increment = g / (q * (q - 2))
    full[index] += increment
    guarded.append({"prime": q, "mode": 9, "support_mask": 1 << bit,
                    "index": index, "increment": str(increment)})
ck("guarded_fees_nonnegative", all(F(row["increment"]) > 0 for row in guarded))

# At the weak corner i=l, w_l=1/9. Whole/root/leaf/deep ternary
# selectors and WHOLE quinary selectors give screen >= M,M,M,9M.
mode_weights = ((0, 1), (4, 1), (8, 1), (12, 9))
rows = []
charge = F(0)
for mode, multiplier in mode_weights:
    indices = range(32 * mode, 32 * (mode + 1))
    subtotal = sum((full[index] for index in indices), F(0))
    base_subtotal = sum((base[index] for index in indices), F(0))
    ck("guard_mode9_does_not_change_mode_" + str(mode), subtotal == base_subtotal)
    rows.append({"ternary_mode": mode // 4, "quinary_mode": mode % 4,
                 "mode": mode, "support_count": 32,
                 "screen_mass_multiplier": multiplier,
                 "coefficient_sum": str(subtotal),
                 "weighted_charge": str(multiplier * subtotal)})
    charge += multiplier * subtotal

delta = charge - g
ck("selected_charge_exact", charge == F(5410561403800247066694067,
                                         4539696895445741568000000))
ck("strict_homogeneous_gap", delta > 0)
ck("gap_exact", delta == F(895320178864953734214067,
                            4539696895445741568000000))
ck("all_other_fees_can_only_lower_gate", all(x >= 0 for x in full))

result = {
    "schema": "single-row-complete-gate-obstruction-v1",
    "status": "PASS",
    "scope": "For any fixed live row l and any admitted matching response, "
             "every field supported on that row has gate <= -delta*M at each "
             "corner with weak3=l. Hence every single-row-supported95 family "
             "has minimum head gate <=0; the zero family attains0. This is an "
             "envelope-method obstruction, not an actual-survivor assertion.",
    "source640_sha256": PIN640,
    "producer_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
    "new_lean_verification": False,
    "g": str(g),
    "selected_modes": rows,
    "guarded_mode9_additions": guarded,
    "selected_total_charge": str(charge),
    "selected_total_charge_decimal": float(charge),
    "delta": str(delta),
    "delta_decimal": float(delta),
    "weak_corner_mass": "1/9",
    "gate_upper_bound": "-delta * source_mass",
    "best_single_row_uniform_head_gate": "0",
    "ordinary_proof_premises": [
        "All induced physical-support matching responses are positive.",
        "Every coordinate mass satisfies0<Z_q<=1 and every edge cap is nonnegative.",
        "Fields vanish off one fixed live ternary row.",
        "The complete selectors retain delta_l at deep ternary mode."
    ],
    "all_general_priority_families_excluded": False,
    "actual_survivor_nonexistence_claimed": False,
    "check_count": len(checks),
    "checks": checks,
}
args.output.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({key: result[key] for key in
                  ("status", "selected_total_charge", "delta", "check_count")}))
