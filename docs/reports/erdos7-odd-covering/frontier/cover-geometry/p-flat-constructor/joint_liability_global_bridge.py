"""Audit actual odd noncovers against proposed height-budget shortcuts.

These finite controls preserve distinct original labels, divisor closure,
normalized prime phases, irredundancy, trivial complete private hulls, the
listed projection/inventory tests, and one explicitly selected liability law.
The law is supported in E_J intersect union(J).  E_J itself is NOT assumed
covered by J: holes elsewhere are enumerated and reported.  Thus these are
countercontrols to the listed local implication, not to Erdős #7 or any
statement retaining the whole-cover premise.  All paths are explicit.
"""

import argparse
import json
from fractions import Fraction
from math import gcd, lcm


def require(condition, message):
    if not condition:
        raise ValueError(message)


def crt(a, m, b, n):
    require(gcd(m, n) == 1, "CRT inputs must be coprime")
    return (a + m * ((b - a) * pow(m, -1, n) % n)) % (m * n)


def valuation(n, p):
    require(n != 0, "valuation of zero is not used")
    exponent = 0
    while n % p == 0:
        exponent += 1
        n //= p
    return exponent


def prime_factors(n):
    primes = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            primes.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        primes.append(n)
    return primes


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def family(q, auxiliary=False):
    r = 3
    height = q - r + 1
    classes = [(0, r)]
    classes += [
        (1 + r ** (k - 1), r**k) for k in range(2, height + 1)
    ]
    classes += [(0, q)]
    classes += [
        (crt(1, r**a, a, q), r**a * q) for a in range(1, height)
    ]
    if auxiliary:
        require(q > 5, "auxiliary prime must differ from q")
        classes += [
            (0, 5),
            (crt(1, 3, 2, 5), 15),
            (crt(q - 2, q, 1, 5), 5 * q),
            (crt(1, 15, q - 1, q), 15 * q),
        ]
    return classes, r, q, height


def shell_weight(classes, x, p):
    total = Fraction(0)
    for residue, modulus in classes:
        height = valuation(modulus, p)
        if height == 0:
            continue
        difference = residue - x
        if difference % modulus == 0:
            continue
        if difference % (modulus // p**height) != 0:
            continue
        agreement = valuation(difference, p)
        require(agreement < height, "invalid shell depth")
        total += Fraction(1, p ** (height - agreement - 1))
    return total


def projection_budget(classes, r, q, live_witnesses, selected_u, include_full_height=True):
    """Exact counting on one fixed actual cofactor section over selected_u."""
    period = lcm(*(d for _, d in classes))
    height = valuation(period, r)
    q_height = valuation(period, q)
    cofactor = period // r**height // q**q_height
    tau = len(divisors(cofactor))
    selected_u = set(selected_u)
    anchors = {
        residue % r**height for residue, modulus in classes
        if modulus % q == 0 and valuation(modulus, r) == height
    }
    require(include_full_height or not selected_u & anchors, "low-only budget has an anchor")
    maximum_height = height if include_full_height else height - 1
    q_sum = sum((Fraction(1, q**e) for e in range(1, q_height + 1)), Fraction())
    coarse = tau * sum(r ** (height - a) for a in range(maximum_height + 1)) * q_sum
    raw = Fraction()
    prefix = Fraction()
    section = Fraction()
    original_terms = []
    for residue, modulus in classes:
        e = valuation(modulus, q)
        a = valuation(modulus, r)
        if not e or (not include_full_height and a == height):
            continue
        s = modulus // r**a // q**e
        matching_prefix = [u for u in selected_u if (u - residue) % r**a == 0]
        matching_section = [
            u for u in matching_prefix if (live_witnesses[u] - residue) % s == 0
        ]
        raw_term = Fraction(r ** (height - a), q**e)
        prefix_term = Fraction(len(matching_prefix), q**e)
        section_term = Fraction(len(matching_section), q**e)
        raw += raw_term
        prefix += prefix_term
        section += section_term
        original_terms.append({
            "modulus": modulus, "r_height": a, "q_height": e,
            "raw_capacity": str(raw_term),
            "actual_prefix_capacity": str(prefix_term),
            "fixed_section_incidence": str(section_term),
        })
    literal_incidence = 0
    source_holes = []
    for u in sorted(selected_u):
        for xi in range(q**q_height):
            point = crt(
                crt(u, r**height, xi, q**q_height),
                r**height * q**q_height, live_witnesses[u], cofactor,
            )
            owners = [d for residue, d in classes if (point - residue) % d == 0]
            require(all(d % q == 0 for d in owners), "q-free section owner")
            require(
                include_full_height or all(valuation(d, r) < height for d in owners),
                "full-height owner at unanchored u",
            )
            literal_incidence += len(owners)
            if not owners:
                source_holes.append(point)
    require(section == Fraction(literal_incidence, q**q_height), "section counting identity")
    require(section <= prefix <= raw <= coarse, "capacity bounds are not ordered")
    if not source_holes:
        require(len(selected_u) <= section, "complete q-lines violate the union bound")
    return {
        "selected_u_count": len(selected_u),
        "selected_u": sorted(selected_u),
        "uses_full_height_inventory": include_full_height,
        "coarse_bound": str(coarse),
        "actual_numerical_inventory": str(raw),
        "actual_prefix_inventory": str(prefix),
        "fixed_section_incidence": str(section),
        "coarse_slack": str(coarse - len(selected_u)),
        "numerical_inventory_slack": str(raw - len(selected_u)),
        "prefix_inventory_slack": str(prefix - len(selected_u)),
        "fixed_section_slack": str(section - len(selected_u)),
        "source_hole_count": len(source_holes),
        "first_source_hole": None if not source_holes else source_holes[0],
        "original_terms": original_terms,
    }


def audit(q, auxiliary):
    classes, r, q, height = family(q, auxiliary)
    period = lcm(*(modulus for _, modulus in classes))
    inventory = {modulus for _, modulus in classes}
    require(all(d > 1 and d % 2 for d in inventory), "not odd nonunit")
    require(len(inventory) == len(classes), "duplicate original labels")
    require(
        all(e in inventory for d in inventory for e in divisors(d) if e > 1),
        "inventory is not divisor closed",
    )
    events = [
        tuple(i for i, (a, d) in enumerate(classes) if (x - a) % d == 0)
        for x in range(period)
    ]
    holes = [x for x, owners in enumerate(events) if not owners]
    require(holes, "unexpected whole cover")
    private = [
        [x for x, owners in enumerate(events) if owners == (i,)]
        for i in range(len(classes))
    ]
    require(all(private), "an original class is redundant")
    hulls = {}
    for (_, modulus), points in zip(classes, private):
        gamma = period
        for x in points:
            gamma = gcd(gamma, x - points[0])
        hulls[modulus] = gamma
    require(
        all(hulls[d] == d for d in inventory),
        "an original has an expanded complete private hull",
    )
    for i, (a, d) in enumerate(classes):
        for j, (b, e) in enumerate(classes):
            if i != j and e % d == 0:
                require((a - b) % d != 0, "comparable originals intersect")
    primes = prime_factors(period)
    require(
        all(next(a for a, d in classes if d == p) == 0 for p in primes),
        "a prime class is not normalized",
    )

    retained = [
        i for i, (_, d) in enumerate(classes)
        if d % q or valuation(d, r) == height
    ]
    removed = [i for i in range(len(classes)) if i not in retained]
    cofactor = period // r**height // q
    u, v = 1, 1 % cofactor
    law = []
    for xi in range(height):
        point = crt(crt(u, r**height, xi, q), r**height * q, v, cofactor)
        require(len(events[point]) == 1, "law point is not globally private")
        require(
            all(i in removed for i in events[point]),
            "law is not supported in E_J intersect union(J)",
        )
        law.append(point)
    require(len(set(law)) == height, "law points repeat")
    require(height == q - r + 1, "wrong blocked branching")
    require(
        all(sum(point % q == xi for point in law) <= 1 for xi in range(q)),
        "q-prefix cap failed",
    )
    masses = {
        d: Fraction(sum((point - a) % d == 0 for point in law), height)
        for a, d in classes
    }
    require(
        all(masses[r**a * q] == Fraction(1, height) for a in range(height)),
        "one mass unit per original r-height was not attained",
    )

    # Check the individual complete-hull/descendant conclusions DR3--DR6.
    for _, d in classes:
        gamma = hulls[d]
        largest_multiple = max(e for e in inventory if e % d == 0)
        require(
            all(e in inventory for e in divisors(gamma)
                if 1 < e < largest_multiple),
            "DR3 violation",
        )
        phase_groups = {}
        for residue, child in classes:
            if child > d and child % d == 0:
                phase_groups.setdefault(residue % d, []).append(child)
        for children in phase_groups.values():
            if len(children) >= 2:
                require(
                    all(e in inventory for e in divisors(gamma) if e > 1),
                    "DR4 violation",
                )
                require(all(gamma % e != 0 for e in children), "DR5 violation")
        if gamma not in inventory:
            require(
                all(len(children) <= 1 for children in phase_groups.values()),
                "DR6 violation",
            )

    # Check the stated EP4 and LA5 consequences, not every whole-cover theorem.
    projections = []
    for p in primes:
        prime_free_period = period // p ** valuation(period, p)
        residual = [
            x for x in range(prime_free_period)
            if not any((x - a) % d == 0 for a, d in classes if d % p)
        ]
        for larger in primes:
            if larger > p:
                roots = sorted({x % larger for x in residual})
                require(len(roots) >= larger - p + 1, "EP4 violation")
                projections.append({"p": p, "larger": larger, "roots": roots})
    inventory_checks = []
    for small in primes:
        for large in primes:
            if small < large:
                h = valuation(period, small)
                other = period // small**h // large ** valuation(period, large)
                tau = len(divisors(other))
                require(large - small < h * tau, "LA5 violation")
                inventory_checks.append(
                    {"r": small, "q": large, "H": h, "tau": tau}
                )

    geometric = sum((Fraction(1, r**a) for a in range(height)), Fraction())
    tau = len(divisors(cofactor))
    require(q - r >= tau * geometric, "geometric shortcut was not refuted")
    complete_line = []
    if auxiliary:
        for xi in range(q):
            point = crt(crt(u, r**height, xi, q), r**height * q, v, cofactor)
            require(events[point], "designated complete q-line has a hole")
            complete_line.append(point)

    # Local private laws do not give every required whole-cover shell.
    shell_failures = []
    for point in law:
        owner = classes[events[point][0]][1]
        for p in prime_factors(owner):
            actual = shell_weight(classes, point, p)
            demand = valuation(owner, p) * (p - 1)
            if actual < demand:
                shell_failures.append({
                    "point": point, "private_owner": owner, "prime": p,
                    "shell_weight": str(actual), "whole_cover_demand": demand,
                })
    require(shell_failures, "the intended missing shell boundary disappeared")

    # E_u is the projection of complement(K), not of its covered part.
    live_u, bad_u, anchored_u, inclusion_failures = [], [], set(), []
    live_witnesses = {}
    for a, d in classes:
        if d % q == 0 and valuation(d, r) == height:
            anchored_u.add(a % r**height)
    for old_u in range(r**height):
        live_v = [
            old_v for old_v in range(cofactor)
            if not any(
                (old_u - a) % r ** valuation(d, r) == 0
                and (old_v - a) % (d // r ** valuation(d, r)) == 0
                for a, d in classes if d % q
            )
        ]
        if live_v:
            live_u.append(old_u)
            live_witnesses[old_u] = live_v[0]
        liability_roots, active_roots = set(), set()
        for xi in range(q):
            for old_v in live_v:
                point = crt(
                    crt(old_u, r**height, xi, q), r**height * q,
                    old_v, cofactor,
                )
                if not any(i in retained for i in events[point]):
                    liability_roots.add(xi)
                if any(i in removed for i in events[point]):
                    active_roots.add(xi)
        if len(liability_roots) >= q - r + 1:
            bad_u.append(old_u)
        if liability_roots - active_roots:
            inclusion_failures.append(old_u)
    require(
        set(live_u) - anchored_u <= set(bad_u) <= set(live_u),
        "L minus V subset U subset L failed",
    )
    require(len(anchored_u) <= tau, "full-height anchoring bound failed")
    require(inclusion_failures, "noncover did not expose E_u subset F_u failure")

    return {
        "original": classes,
        "Q": period, "r": r, "q": q, "H": height, "G": 1, "M": cofactor,
        "private_counts": [len(points) for points in private],
        "private_hulls": hulls,
        "holes": len(holes), "first_hole": holes[0],
        "selected_covered_liability_law": {
            "points": law, "weights": [str(Fraction(1, height))] * height,
            "original_masses": {str(d): str(masses[d]) for d in sorted(inventory)},
            "scope": "Supported in E_J intersect union(J); not all E_J is covered.",
        },
        "designated_complete_qline": complete_line,
        "old_inventory_conditions": inventory_checks,
        "old_prime_projection_conditions": projections,
        "geometric_sum": str(geometric),
        "geometric_inventory_exact": str(tau * geometric),
        "q_minus_r": q - r,
        "DR3_to_DR6_pass": True,
        "missing_whole_cover_shells": shell_failures,
        "live_projection_budget": projection_budget(classes, r, q, live_witnesses, live_u),
        "unanchored_projection_budget": projection_budget(
            classes, r, q, live_witnesses, set(live_u) - anchored_u,
            include_full_height=False,
        ),
        "liability_projection": {
            "live_u": live_u, "bad_u": bad_u,
            "full_height_anchors": sorted(anchored_u),
            "E_not_subset_F_at_u": inclusion_failures,
        },
        "scope": (
            "Odd distinct divisor-closed irredundant NONCOVER. All private hulls "
            "equal original labels. Satisfies the listed selected-law, hull, "
            "projection and inventory tests. Fails whole coverage, E_u subset "
            "F_u at some u, and the explicitly listed whole-cover shell demands."
        ),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    output = [audit(5, False), audit(7, True)]
    with open(args.output, "w") as handle:
        json.dump(output, handle, sort_keys=True, indent=2)
        handle.write("\n")
    print(json.dumps([
        {"Q": item["Q"], "classes": len(item["original"]),
         "holes": item["holes"],
         "geometric_bound": item["geometric_inventory_exact"],
         "q_minus_r": item["q_minus_r"]}
        for item in output
    ]))


if __name__ == "__main__":
    main()
