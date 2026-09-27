#!/usr/bin/env python3
"""Exact original-congruence experiments for a balanced prefix budget.

Only Python's standard library is needed. Radix cells partition complete
coordinates into sets on which every literal congruence is constant. This
does not enumerate the full CRT period or project away untested digits.
"""

import argparse
from collections import defaultdict
from fractions import Fraction as F
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def crt(conditions):
    value, modulus = 0, 1
    for factor, residue in conditions:
        value += modulus * ((residue - value) * pow(modulus, -1, factor) % factor)
        modulus *= factor
        value %= modulus
    return modulus, value


def label(conditions):
    modulus, residue = crt(conditions)
    return {"modulus": modulus, "residue": residue}


def prefix_cells(prime, height, tests):
    """Disjoint complete-coordinate cylinders, with pure 0 mod p removed."""
    tests = tuple(sorted(set(tests) | {(0, 1)}))
    require(all(1 <= e <= height and 0 <= a < prime**e for a, e in tests),
            "invalid prefix or incomplete coordinate")
    leaves = []

    def visit(a, depth):
        if any(e > depth and b % prime**depth == a for b, e in tests):
            for digit in range(prime):
                visit(a + digit * prime**depth, depth + 1)
        elif a % prime:
            leaves.append((a, depth, F(prime**(height-depth),
                                      prime**height-prime**(height-1))))

    visit(0, 0)
    require(sum(w for _, _, w in leaves) == 1, "pure-base mass")
    for a, depth, _ in leaves:
        for b, e in tests:
            require(depth >= e or a != b % prime**depth,
                    "a literal test varies inside an unsplit cell")
    return leaves


def prefixes(prime, n):
    return [((prime**(e-1)+1)//2, e) for e in range(1, n+1)]


def clipped(alpha, delta, forbidden):
    require(0 <= alpha <= 1 and 0 < delta < 1, "clipping domain")
    if forbidden:
        require(alpha > 0, "forbidden atom with zero mass")
        return max(alpha-delta, F(0))/(alpha*(1-delta))
    return F(1)/(1-min(alpha, delta))


def make_head(n, current, zeta, extra_r=(), extra_s=()):
    r, s, p = 3, 5, 7
    require(zeta > 0 and len(current) == n, "positive cap and Latin order")
    cp, dp = prefixes(r, n), prefixes(s, n)
    si = [F(1, (r-1)*r**(e-1)) for _, e in cp]
    tj = [F(1, (s-1)*s**(e-1)) for _, e in dp]
    vl = [F(1, (p-1)*p**(a-1)) for _, a in current]
    require(sum(vl) == 1, "current prefixes do not partition the pure base")
    for i, (a, e) in enumerate(current):
        for b, f in current[i+1:]:
            require((a-b) % p**min(e, f) != 0, "current prefixes overlap")
    tau = min(si[i]*tj[j]*min(zeta/vl[(i+j) % n],
                              1/(1-vl[(i+j) % n]))
              for i in range(n) for j in range(n))
    head = [label([(q, 0)]) for q in (r, s, p)]
    for i, (a, e) in enumerate(cp):
        for j, (b, f) in enumerate(dp):
            c, h = current[(i+j) % n]
            head.append(label([(r**e, a), (s**f, b), (p**h, c)]))
    require(len({a["modulus"] for a in head}) == len(head), "repeated modulus")
    require(all(a["modulus"] > 1 and a["modulus"] % 2 for a in head),
            "non-odd or unit modulus")
    rh = max([n] + [e for _, e in extra_r])
    sh = max([n] + [e for _, e in extra_s])
    ph = max(e for _, e in current)
    rs = prefix_cells(r, rh, cp + list(extra_r))
    ss = prefix_cells(s, sh, dp + list(extra_s))
    ps = prefix_cells(p, ph, current)
    full_period = r**rh*s**sh*p**ph
    rows = []
    physical_pair = [defaultdict(F) for _ in range(3)]
    base_pair = [defaultdict(F) for _ in range(3)]
    physical = survivor = reference_survivor = F(0)
    delta_min, delta_max = F(1), F(0)
    tested_cells = 0
    for ir, (x, _, wx) in enumerate(rs):
        im = [i for i, (a, e) in enumerate(cp) if x % r**e == a]
        require(len(im) <= 1, "old r-prefixes overlap")
        for js, (y, _, wy) in enumerate(ss):
            jm = [j for j, (b, f) in enumerate(dp) if y % s**f == b]
            require(len(jm) <= 1, "old s-prefixes overlap")
            if im and jm:
                i, j = im[0], jm[0]
                leaf = (i+j) % n
                u = tau*vl[leaf]/(si[i]*tj[j])
                delta = u/(1+u)
            else:
                leaf, u, delta = None, F(0), F(1, 2)
            require(0 < delta < 1 and u <= zeta, "invalid source policy")
            if leaf is not None:
                delta_min, delta_max = min(delta_min, delta), max(delta_max, delta)
            forbidden_atoms = []
            for z, _, wz in ps:
                _, word = crt([(r**rh, x), (s**sh, y), (p**ph, z)])
                hits = [a for a in head if word % a["modulus"] == a["residue"]]
                require(len(hits) <= 1, "unexpected head intersection")
                forbidden_atoms.append(bool(hits))
            alpha = sum((wz for (_, _, wz), bad in zip(ps, forbidden_atoms) if bad), F(0))
            require(alpha == (vl[leaf] if leaf is not None else 0),
                    "literal head and Latin prefix union differ")
            row_mass = F(0)
            for kp, ((z, _, wz), bad) in enumerate(zip(ps, forbidden_atoms)):
                density = clipped(alpha, delta, bad)
                require(isinstance(density, F), "non-rational density")
                require(density >= 0 and density <= 1+zeta, "row density cap")
                if not bad:
                    require(density == 1+u, "good density")
                wb, wm = wx*wy*wz, wx*wy*wz*density
                row_mass += wz*density
                physical += wm
                if not bad:
                    survivor += wm
                    reference_survivor += wb
                indices = ((ir, js), (ir, kp), (js, kp))
                for h, key in enumerate(indices):
                    physical_pair[h][key] += wm
                    base_pair[h][key] += wb
                rows.append((x, y, z, wb, wm, bad))
                tested_cells += 1
            require(row_mass == 1, "unnormalized actual row")
    require(physical == 1, "physical normalization")
    require(physical_pair == base_pair, "full pair marginals differ")
    exact_surplus = n*(1-sum(v*v for v in vl))*tau
    require(survivor-reference_survivor == exact_surplus, "head surplus formula")
    uniform_bound = zeta*F(r, r-1)*(p-1)*F(1, r**(p-1))
    require(exact_surplus <= uniform_bound, "all-height bound")
    return rows, {
        "complete_coordinate_sizes": [r**rh, s**sh, p**ph],
        "complete_period": full_period,
        "constant_test_cell_count": tested_cells,
        "full_point_enumeration": False,
        "head_labels": head,
        "latin_order": n,
        "current_prefixes": [{"residue": a, "depth": e} for a, e in current],
        "zeta": zeta, "tau": tau,
        "active_threshold_interval": [delta_min, delta_max],
        "physical_mass": physical, "survivor_mass": survivor,
        "reference_survivor_mass": reference_survivor,
        "exact_head_surplus": exact_surplus,
        "all_height_upper_bound": uniform_bound,
        "all_full_pair_marginals_equal_product": True,
        "threshold_policy": "history dependent; delta=u/(1+u), u=tau*v/(s_i*t_j)",
    }


def future_label(prime, old_prime, depth, old_residue, color):
    out = label([(old_prime**depth, old_residue), (prime, color)])
    out.update(old_prime=old_prime, old_depth=depth, old_residue=old_residue,
               current_prime=prime, current_color=color)
    return out


def future_probability(row, labels, delta, old_sizes):
    x, y, z = row[:3]
    old = {3: x, 5: y, 7: z}
    prime = labels[0]["current_prime"]
    require(all(a["current_prime"] == prime for a in labels), "mixed stages")
    colors = {a["current_color"] for a in labels
              if old[a["old_prime"]] % a["old_prime"]**a["old_depth"]
              == a["old_residue"]}
    # Check the color computation against every actual original AP.
    for color in range(prime):
        _, word = crt(list(zip(old_sizes, (x, y, z)))+[(prime, color)])
        literal = any(word % a["modulus"] == a["residue"] for a in labels)
        require(literal == (color in colors), "future CRT discrepancy")
    alpha = F(len(colors), prime)
    return max(alpha-delta, F(0))/(1-delta)


def run():
    zeta = F(1, 35)
    current = [(c, 1) for c in range(1, 7)]
    rows, sharp = make_head(6, current, zeta, [(1, 2), (4, 3)], [(1, 2), (6, 3)])
    old_sizes = sharp["complete_coordinate_sizes"]
    epsilon = F(1, 212625000)
    require(sharp["tau"] == 6*epsilon, "sharp allocation")
    require(sharp["exact_head_surplus"] == 30*epsilon == F(1, 7087500),
            "sharp excess value")
    one = [future_label(11, 3, 1, 1, 0), future_label(11, 5, 1, 1, 1),
           future_label(11, 7, 1, 3, 2)]
    one_cost = reference_cost = relaxed_cost = F(0)
    relaxed_pairs = [defaultdict(F) for _ in range(3)]
    base_pairs = [defaultdict(F) for _ in range(3)]
    for row in rows:
        x, y, z, wb, wm, bad = row
        beta = future_probability(row, one, F(2, 11), old_sizes)
        require(beta == (F(1, 9) if x % 3 == y % 5 == 1 and z == 3 else 0),
                "one-stage trigger")
        h3, h5 = (1 if x % 3 == 1 else -1), (F(1) if y % 5 == 1 else -F(1, 3))
        h7 = int(z == 3)-int(z == 4)
        comp = 1+zeta*h3*h5*h7
        require(0 <= comp <= 1+zeta, "relaxed row cap")
        for h, key in enumerate(((x, y), (x, z), (y, z))):
            relaxed_pairs[h][key] += wb*comp
            base_pairs[h][key] += wb
        if not bad:
            one_cost += wm*beta
            reference_cost += wb*beta
            relaxed_cost += wb*comp*beta
    require(relaxed_pairs == base_pairs, "relaxed full pair marginals")
    require(one_cost == F(1, 432)+epsilon/54 == F(13289063, 5740875000),
            "sharp original-source first-hit cost")
    require(reference_cost == F(1, 432) and relaxed_cost == F(1, 420),
            "reference/cap comparator costs")
    require(relaxed_cost-one_cost == F(54241, 820125000), "strict improvement")
    overlap11 = [future_label(11, 3, 2, 1, 0), future_label(11, 3, 3, 4, 0),
                 future_label(11, 5, 2, 1, 1), future_label(11, 7, 1, 3, 2)]
    overlap13 = [future_label(13, 3, 2, 1, 0), future_label(13, 5, 2, 1, 1),
                 future_label(13, 5, 3, 6, 1), future_label(13, 7, 1, 3, 2)]
    total = reference_total = naive = overlap = F(0)
    masses = [F(0), F(0), F(0)]
    for row in rows:
        x, y, z, wb, wm, bad = row
        g1 = (x % 9 == 1 or x % 27 == 4) and y % 25 == 1 and z == 3
        g2 = x % 9 == 1 and (y % 25 == 1 or y % 125 == 6) and z == 3
        b11 = future_probability(row, overlap11, F(2, 11), old_sizes)
        b13 = future_probability(row, overlap13, F(2, 13), old_sizes)
        require(b11 == F(g1, 9) and b13 == F(g2, 11), "overlap triggers")
        require(not (bad and (g1 or g2)), "trigger is not head-good")
        if not bad:
            total += wm*(b11+(1-b11)*b13)
            reference_total += wb*(b11+(1-b11)*b13)
            naive += wm*(b11+b13)
            overlap += wm*b11*b13
            for i, event in enumerate((g1, g2, g1 and g2)):
                masses[i] += wm*event
    require(masses == [F(1, 540)+2*epsilon/135, F(1, 600)+epsilon/75,
                       F(1, 720)+epsilon/90], "joint trigger masses")
    require(total == naive-overlap == F(4877086121, 14208665625000),
            "two-stage common-law first hit")
    require(0 <= total-reference_total <= sharp["exact_head_surplus"],
            "shared extra-leakage budget")
    for extension in (one, overlap11+overlap13):
        family = sharp["head_labels"]+extension
        require(len({a["modulus"] for a in family}) == len(family),
                "extension repeats a numerical modulus")
        require(all(2 % a["modulus"] != a["residue"] for a in family),
                "avoiding integer fails")
    mixed_leaves = [(c, 1) for c in range(2, 7)]+[(1+7*k, 2) for k in range(7)]
    _, mixed = make_head(12, mixed_leaves, F(1, 100))
    fixed_policy = []
    for delta in (F(1, 96), F(1, 5)):
        actual_pairs = [defaultdict(F), defaultdict(F)]
        reference_pairs = [defaultdict(F), defaultdict(F)]
        cp, dp = prefixes(3, 6), prefixes(5, 6)
        mass = surplus = F(0)
        for x, y, z, wb, _, bad in rows:
            active = (any(x % 3**e == a for a, e in cp)
                      and any(y % 5**e == a for a, e in dp))
            density = clipped(F(1, 6) if active else F(0), delta, bad)
            require(isinstance(density, F), "non-rational fixed-policy density")
            mass += wb*density
            if not bad:
                surplus += wb*(density-1)
            for axis, key in enumerate(((x, z), (y, z))):
                actual_pairs[axis][key] += wb*density
                reference_pairs[axis][key] += wb
        require(mass == 1 and surplus > 0, "fixed-policy normalization")
        distances = [sum((abs(v-reference_pairs[i][k]) for k, v in d.items()), F(0))/2
                     for i, d in enumerate(actual_pairs)]
        ratios = [v/surplus for v in distances]
        kappas = [max((1-F(1, q**k))/(1-F(1, q**6))-F(k, 6)
                      for k in range(7)) for q in (5, 3)]
        require(ratios == [F(6, 5)*v for v in kappas]
                == [F(2474, 3255), F(304, 455)], "fixed-policy sharp TV ratios")
        fixed_policy.append({
            "delta7": delta, "head_surplus": surplus,
            "pair_total_variation_rp_sp": distances,
            "pair_TV_divided_by_surplus_rp_sp": ratios,
            "full_pair_product_assumption": False,
            "balanced_zeta_cap_assumption": False,
            "same_original_39_label_head": True,
        })
    return {
        "scope": "restricted Latin-prefix sources: balanced history-dependent policies and fixed-threshold stability; not unrestricted Erdos 7",
        "sharp_head": sharp,
        "one_stage_consumer": {
            "extension_labels": one, "delta11": F(2, 11),
            "first_hit": one_cost, "reference_first_hit": reference_cost,
            "cap_only_first_hit": relaxed_cost, "strict_gap": relaxed_cost-one_cost,
            "cap_comparator_reachability_claimed": False,
        },
        "overlapping_consumer": {
            "extension_labels": overlap11+overlap13,
            "delta11": F(2, 11), "delta13": F(2, 13),
            "joint_trigger_masses": masses, "first_hit": total,
            "reference_first_hit": reference_total, "overlap_saving": overlap,
            "additional_first_hit": total-reference_total,
            "single_available_extra_budget": sharp["exact_head_surplus"],
            "avoiding_integer": 2,
        },
        "mixed_current_heights_head": mixed,
        "fixed_threshold_stability": fixed_policy,
        "fixed_current_leaf_policy": "impossible under the stated Latin, full pair-product, positive-threshold and distinct-modulus assumptions; see manuscript proof",
    }


def encode(value):
    if isinstance(value, F):
        return str(value)
    raise TypeError(type(value).__name__)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = json.dumps(run(), default=encode, indent=2, sort_keys=True)+"\n"
    if args.output:
        args.output.write_text(result, encoding="utf-8")
    else:
        print(result, end="")
