#!/usr/bin/env python3
"""Portable export/check of saved-candidate pure9 primal/dual certificates.

All input and output paths are explicit CLI arguments. No optimizer is
included, and checking does not construct private products or quotients.
"""
import argparse
from collections import defaultdict
from decimal import Decimal, localcontext
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path


PINS = {
    "148": "5f04960e119182d927214b4da9ed542455fda088cef940c2bc1ad655911b9d21",
    "146": "5fa2dd84a74f115d1e78bab45dbe2ea29f187470504303727028b17121233cad",
    "145": "4ae73a9a4e17120630602fbef88ffccdc74f34a33ad3f7ac878c633c656aaa04",
    "144": "bad5b8c850742e0bb7277ea316bf5e96dc06f963317a28033cc6ed8e1ebb06bb",
}
CHECKS = defaultdict(int)
ZERO, ONE, HALF = Q(0), Q(1), Q(1, 2)


def check(ok, label):
    if not ok:
        raise RuntimeError("failed check: " + label)
    CHECKS[label] += 1


def dec(x):
    with localcontext() as ctx:
        ctx.prec = 35
        return str(Decimal(x.numerator) / Decimal(x.denominator))


def read_input(path, key):
    raw = Path(path).read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    check(digest == PINS[key], "input_sha256_" + key)
    return json.loads(raw), {"path": str(Path(path)), "sha256": digest}


def vector_add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def vector_sub(a, b):
    return (a[0] - b[0], a[1] - b[1])


def dot(v, x):
    return v[0] * x + v[1] * (ONE - x)


def root_maxima(rows):
    vals, indices = [], []
    for r in range(2):
        value = max(row["values"][r] for row in rows)
        index = next(i for i, row in enumerate(rows) if row["values"][r] == value)
        vals.append(value)
        indices.append(index)
    return vals, indices


def build_base(data, table):
    c148 = data["148"]["cases"][table]
    c146 = data["146"]["cases"][table]
    c145 = data["145"]["cases"][table]
    c144 = data["144"]["cases"][table]
    roots = data["148"]["root_order"]
    check(roots == [1, 2], "root_order")
    cell_index = {tuple(addr): i for i, addr in enumerate(data["148"]["joint_cell_order"])}
    check(len(cell_index) == 70, "joint_cell_order_size")
    weights = {
        r: {h: list(map(Q, c148["head_weights"][str(r)][str(h)])) for h in (5, 7)}
        for r in roots
    }
    quotients = c148["outside_P_quotients_by_supported_private_mask"]
    contractions = c148["head_contractions_by_supported_private_mask"]
    blocks = []
    support_keys = set()

    for si, support in enumerate(c148["new_support_results"]):
        heads = support["supported_heads"]
        mask = support["private_mask"]
        key = (tuple(heads), mask, support["head_depth_lower"])
        check(key not in support_keys, "distinct_full_support_slots")
        support_keys.add(key)
        cap = Q(support["complete_supported_private_cap"])
        check(cap == Q(data["148"]["complete_supported_private_caps_by_mask"][mask]),
              "saved_supported_cap_match")
        if not heads:
            addresses = [()]
        elif heads == [5]:
            addresses = [(i,) for i in range(5)]
        elif heads == [7]:
            addresses = [(j,) for j in range(7)]
        else:
            check(heads == [5, 7], "supported_head_shape")
            addresses = [(i, j) for i in range(5) for j in range(7)]
        for bi, block in enumerate(support["blocks"]):
            bits = block["deep_tail_bits_in_head_order"]
            rows = []
            for addr in addresses:
                values = []
                for ri, root in enumerate(roots):
                    factors = []
                    for h, row, deep in zip(heads, addr, bits):
                        w = weights[root][h][row]
                        factors.append(ONE if deep and w > 0 else ZERO if deep else w)
                    if not heads:
                        x = HALF * Q(contractions[mask]["T0"][ri])
                    elif heads == [5]:
                        x = HALF * factors[0] * Q(contractions[mask]["T5"][ri][addr[0]])
                    elif heads == [7]:
                        x = HALF * factors[0] * Q(contractions[mask]["T7"][ri][addr[0]])
                    else:
                        oi = cell_index[(root, addr[0], addr[1])]
                        x = HALF * factors[0] * factors[1] * Q(quotients[mask][oi])
                    values.append(x)
                rows.append({"address": addr, "values": values})
            blocks.append({
                "input": "148", "support_index": si, "block_index": bi,
                "supported_heads": heads, "private_mask": mask,
                "head_depth_lower": support["head_depth_lower"],
                "deep_tail_bits": bits, "weight": cap * Q(block["depth_weight"]),
                "depth_weight": Q(block["depth_weight"]), "private_cap": cap,
                "gamma_restored_here": True, "rows": rows,
            })

    check(len(c148["new_support_results"]) == 2017, "new_support_count")
    check(len(blocks) == 4554, "new_depth_block_count")
    for pi, pair in enumerate(c145["pair_supports"]):
        h, p = pair["head"], pair["private_prime"]
        mask = 1 << data["148"]["private_prime_order"].index(p)
        key = ((h,), mask, 2)
        check(key not in support_keys, "distinct_full_support_slots")
        support_keys.add(key)
        saved = {(row["root"], row["row"]): row for row in pair["paired_root_rows"]}
        rows = []
        for addr in range(h):
            values = [Q(saved[(root, addr)]["masked_V_P"]) for root in roots]
            for root, value in zip(roots, values):
                record = saved[(root, addr)]
                w, c = Q(record["row_mass"]), Q(record["saved_C_P"])
                check(c == w * value, "145_saved_candidate_recovery_identity")
                if w == 0:
                    check(value == 0, "145_zero_mask")
            rows.append({"address": (addr,), "values": values})
        blocks.append({
            "input": "145", "pair_index": pi, "supported_heads": [h],
            "private_mask": mask, "head_depth_lower": 2, "deep_tail_bits": [1],
            "weight": Q(pair["supported_private_cap_sum"]) * Q(pair["complete_head_tail_factor"]),
            "depth_weight": Q(pair["complete_head_tail_factor"]),
            "private_cap": Q(pair["supported_private_cap_sum"]),
            "gamma_restored_here": False, "rows": rows,
        })
    check(len(c145["pair_supports"]) == 18, "cached_deep_pair_count")

    key = ((5, 7), 0, 1)
    check(key not in support_keys, "distinct_full_support_slots")
    support_keys.add(key)
    source = [ZERO, ZERO]
    for bi, block in enumerate(c146["depth_blocks"]):
        saved = {(row["root"], row["head5_row"], row["head7_row"]): row
                 for row in block["paired_root_candidates"]}
        rows = []
        for i in range(5):
            for j in range(7):
                values = [Q(saved[(root, i, j)]["X_P"]) for root in roots]
                rows.append({"address": (i, j), "values": values})
                if block["alpha"] == 0 and block["beta"] == 0:
                    source = [source[r] + values[r] for r in range(2)]
        blocks.append({
            "input": "146", "block_index": bi, "supported_heads": [5, 7],
            "private_mask": 0, "head_depth_lower": 1,
            "deep_tail_bits": [block["alpha"], block["beta"]],
            "weight": Q(block["depth_weight"]), "depth_weight": Q(block["depth_weight"]),
            "private_cap": ONE, "gamma_restored_here": False, "rows": rows,
        })
    check(len(support_keys) == 2036, "all_support_count")
    check(len(blocks) == 4576, "all_depth_block_count")

    shallow = []
    for pi, pair in enumerate(c145["pair_supports"]):
        pair144 = c144["pair_supports"][pi]
        check((pair["head"], pair["private_prime"]) ==
              (pair144["head"], pair144["private_prime"]), "144_145_pair_index_match")
        saved = {(row["root"], row["row"]): row for row in pair["paired_root_rows"]}
        control = {(row["root"], row["row"]): row for row in pair144["candidates"]}
        rows = []
        for i in range(pair["head"]):
            values = [Q(saved[(root, i)]["saved_C_P"]) for root in roots]
            for root, v in zip(roots, values):
                check(v == Q(control[(root, i)]["selected_candidate_P"]),
                      "independent_144_shallow_candidate_match")
            rows.append({"address": (i,), "values": values})
        shallow.append({
            "input": "145", "control_input": "144", "pair_index": pi,
            "head": pair["head"], "private_prime": pair["private_prime"],
            "weight": Q(pair["supported_private_cap_sum"]), "rows": rows,
        })

    for block in blocks + shallow:
        block["root_maxima"], block["root_maximizing_row_indices"] = root_maxima(block["rows"])
    check(sum(source) == Q(c148["saved_group_mass_Abar"]), "unit_source_saved_interface")
    return {
        "source_vector_L_A_over_2": source, "blocks": blocks, "shallow_pairs": shallow,
        "source_formula": "sum rootwise shallow/shallow X_P from146; gamma already included",
    }


def block_map(base):
    entries = []
    for block in base["blocks"]:
        if block["input"] == "148":
            entries.append(["148", block["support_index"], block["block_index"], str(block["weight"])])
        elif block["input"] == "145":
            entries.append(["145", block["pair_index"], None, str(block["weight"])])
        elif block["input"] == "146":
            entries.append(["146", block["block_index"], None, str(block["weight"])])
        else:
            raise RuntimeError("unknown base input")
    return entries


def export_completed(args):
    raw = Path(args.completed_result).read_bytes()
    completed = json.loads(raw)
    cert = {
        "schema": "pure9-two-root-primal-dual-v1",
        "source_revision": completed["source_revision"],
        "input_pins": {k: v["sha256"] for k, v in completed["inputs"].items()},
        "completed_result_sha256": hashlib.sha256(raw).hexdigest(),
        "preregistration_sha256": completed["preregistration"]["sha256"],
        "optimization_consumer_sha256": completed["consumer_sha256"],
        "formula": completed["formula"],
        "reconstruction": {
            "block_map_columns": ["input_id", "support_or_pair_or_block_index", "block_index_for148_else_null", "complete_weight"],
            "root_order": [1, 2],
            "block_order": "148 new support then depth-block order;145 pair order;146 depth-block order",
            "raw_rows": "physical addresses: [] or head row0..h-1 or (head5row,head7row) lexicographic; two root values per address",
            "148_raw_values": "gamma=1/2 times saved T0, or supported head factor times T5/T7, or both supported factors times saved outside-P quotient; shallow factor=w, deep factor=1_(w>0)",
            "145_raw_values": "saved masked_V_P; gamma already included",
            "146_raw_values": "saved X_P; gamma already included",
            "source_L": "rootwise sum of146 shallow/shallow X_P",
            "shallow_values": "145 saved_C_P, checked against144 selected_candidate_P",
            "term_order": "free all blocks; height-one selected all blocks; higher selected all blocks; higher shallow all18 pairs",
            "free_choices": "zero-based raw row index, one physical address shared by both root coordinates",
            "selected_choices": "0 or1 for root1 or2, using selected_root_witnesses physical row indices",
            "higher_scaling": "multiply selected coordinate j by1/(2 theta_j), theta_h=2/3, other theta=1",
            "dual": "left_choices plus sparse right_changes; each term mixes left/right with global probability on right",
        },
        "tables": {}, "cases": {},
        "finite_N": {
            "E_N": "norm_inf(L_N-L)+sum_k max_c norm_inf(v_kc_N-v_kc), over FULL physical candidate menus",
            "bound": "abs(K_N-K)<=E_N; if E_N<=(-K)/2 then K_N<=K/2<0 for each certified case",
            "per_coefficient_bound": "if every source/candidate coordinate error<=(−K)/(2*(term_count+1)), the displayed E_N condition holds",
            "explicit_numerical_N": None,
            "eventual_scope": "existing finite-signature convergence, stable masks, unchanged source gates; no finiteN source was evaluated",
        },
        "scope": completed["boundary"],
    }
    for table, base in completed["bases"].items():
        cert["tables"][table] = {
            "source_L": base["source_vector_L_A_over_2"], "block_map": block_map(base),
            "selected_root_witnesses": [b["root_maximizing_row_indices"] for b in base["blocks"]],
            "shallow_map": [["145", b["pair_index"], b["weight"]] for b in base["shallow_pairs"]],
            "shallow_root_witnesses": [b["root_maximizing_row_indices"] for b in base["shallow_pairs"]],
        }
        cert["cases"][table] = {}
        for hole, old in completed["cases"][table].items():
            left = old["dual"]["left_choices"]
            right = old["dual"]["right_choices"]
            cert["cases"][table][hole] = {
                "hole_root": old["hole_root"], "x": old["primal"]["x"], "K": old["optimum"],
                "term_count": old["term_count"],
                "dual_probability_on_right": old["dual"]["mixture_weight_on_right_selection"],
                "left_choices": left,
                "right_changes": [[i, r] for i, (l, r) in enumerate(zip(left, right)) if l != r],
                "dual_cost_minus_source": old["dual"]["cost_minus_source_coordinates"],
                "finite_gap_half": old["finite_N_robustness"]["strict_gap_if_aggregate_error_le"],
            }
    encoded = json.dumps(cert, separators=(",", ":"), default=str) + "\n"
    Path(args.output).write_text(encoded)
    print("exported compact certificate; bytes=" + str(len(encoded.encode())), flush=True)


def candidate_terms(base, hole):
    theta = [ONE, ONE]
    theta[hole - 1] = Q(2, 3)
    for kind in ("free", "height_one_selected", "higher_selected"):
        for block in base["blocks"]:
            w = block["weight"]
            if kind == "free":
                yield [(w * row["values"][0], w * row["values"][1]) for row in block["rows"]]
            elif kind == "height_one_selected":
                yield [(w * block["root_maxima"][0], ZERO), (ZERO, w * block["root_maxima"][1])]
            else:
                yield [(HALF * w * block["root_maxima"][0] / theta[0], ZERO),
                       (ZERO, HALF * w * block["root_maxima"][1] / theta[1])]
    for block in base["shallow_pairs"]:
        w = block["weight"]
        yield [(HALF * w * block["root_maxima"][0] / theta[0], ZERO),
               (ZERO, HALF * w * block["root_maxima"][1] / theta[1])]


def check_compact(args):
    cert_raw = Path(args.certificate).read_bytes()
    cert = json.loads(cert_raw)
    check(cert["schema"] == "pure9-two-root-primal-dual-v1", "schema")
    check(cert["input_pins"] == PINS, "certificate_input_pins")
    data = {k: read_input(getattr(args, "input" + k), k)[0] for k in PINS}
    reports = {}
    for table in ("FC110", "FC131"):
        base = build_base(data, table)
        mapping = cert["tables"][table]
        check(mapping["block_map"] == block_map(base), "compact_block_weight_map")
        check(mapping["selected_root_witnesses"] ==
              [b["root_maximizing_row_indices"] for b in base["blocks"]], "compact_selected_physical_witnesses")
        check(mapping["shallow_root_witnesses"] ==
              [b["root_maximizing_row_indices"] for b in base["shallow_pairs"]], "compact_shallow_physical_witnesses")
        check(mapping["shallow_map"] ==
              [["145", b["pair_index"], str(b["weight"])] for b in base["shallow_pairs"]], "compact_shallow_weight_map")
        L = tuple(base["source_vector_L_A_over_2"])
        check(list(map(Q, mapping["source_L"])) == list(L), "compact_source_vector")
        reports[table] = {}
        for hole in (1, 2):
            sol = cert["cases"][table][str(hole)]
            check(sol["hole_root"] == hole, "compact_hole_label")
            x, K, t = Q(sol["x"]), Q(sol["K"]), Q(sol["dual_probability_on_right"])
            check(0 <= x <= 1 and 0 <= t <= 1, "compact_primal_and_mixture_feasible")
            left = sol["left_choices"]
            right = list(left)
            seen = set()
            for ti, choice in sol["right_changes"]:
                check(isinstance(ti, int) and 0 <= ti < len(left) and ti not in seen,
                      "compact_sparse_changes_legal")
                seen.add(ti)
                right[ti] = choice
            cost_left = (ZERO, ZERO)
            cost_right = (ZERO, ZERO)
            primal_cost = ZERO
            nt = 0
            for ti, vectors in enumerate(candidate_terms(base, hole)):
                check(ti < len(left), "compact_selection_exists")
                l, r = left[ti], right[ti]
                check(isinstance(l, int) and isinstance(r, int) and
                      0 <= l < len(vectors) and 0 <= r < len(vectors), "compact_choice_is_original_candidate")
                value = max(dot(v, x) for v in vectors)
                primal_cost += value
                check(dot(vectors[l], x) == value and dot(vectors[r], x) == value,
                      "compact_dual_choices_active_at_primal")
                cost_left = vector_add(cost_left, vectors[l])
                cost_right = vector_add(cost_right, vectors[r])
                nt += 1
            check(nt == len(left) == sol["term_count"], "compact_term_inventory_complete")
            excess = tuple((ONE - t) * cost_left[j] + t * cost_right[j] - L[j] for j in range(2))
            check(dot(L, x) - primal_cost == K, "compact_primal_exact")
            check(excess == (-K, -K) and K < 0, "compact_dual_strict_both_coordinates")
            check(list(map(Q, sol["dual_cost_minus_source"])) == list(excess), "compact_saved_excess")
            check(Q(sol["finite_gap_half"]) == -K / 2, "compact_finite_gap")
            reports[table][str(hole)] = {
                "x": x, "K": K, "K_decimal_display": dec(K), "dual_excess": excess,
                "global_upper": K, "primal_lower": K, "term_count": nt,
                "mixed_choice_terms": len(seen), "finite_half_gap": -K / 2,
            }
            print(table + " root" + str(hole) + " compact primal/dual PASS", flush=True)
    receipt = {
        "certificate_sha256": hashlib.sha256(cert_raw).hexdigest(),
        "verifier_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "verification": "exact pinned-candidate primal/dual check; no optimization or envelope reconstruction",
        "cases": reports, "checks": dict(CHECKS),
        "optimizer_executed": False, "private_products_rebuilt": False,
        "quotients_rebuilt": False, "finite_N_evaluated": False,
    }
    Path(args.output).write_text(json.dumps(receipt, default=str, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("export", "check"))
    parser.add_argument("--completed-result")
    parser.add_argument("--certificate")
    for k in PINS:
        parser.add_argument("--input" + k)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    needed = ["completed_result"] if args.mode == "export" else ["certificate"] + ["input" + k for k in PINS]
    for name in needed:
        if not getattr(args, name):
            parser.error("missing --" + name.replace("_", "-"))
    if args.mode == "export":
        export_completed(args)
    else:
        check_compact(args)


if __name__ == "__main__":
    main()
