#!/usr/bin/env python3
"""Exact finite checks for the source-preserving private-bucket factorization.

The indexed control has repeated numerical modulus 3q, so it is deliberately
outside the odd-distinct/EB1 class.  It checks the exact §233 bucket definitions,
the product decomposition of saturated flows, core compatibility, the
lambda=tau and Lambda=min Gamma identities, and the §240 service correction.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from itertools import combinations, product
from math import gcd, lcm


@dataclass(frozen=True)
class AP:
    name: str
    modulus: int
    residue: int


def crt_residue(modulus_a: int, residue_a: int, modulus_b: int, residue_b: int) -> int:
    period = lcm(modulus_a, modulus_b)
    hits = [x for x in range(period)
            if x % modulus_a == residue_a % modulus_a
            and x % modulus_b == residue_b % modulus_b]
    assert len(hits) == 1
    return hits[0]


def control_source(q: int = 5) -> tuple[int, list[AP], int]:
    assert q > 3 and q % 2 == 1
    source = [AP("A", 3, 0), AP("B", q, 0)]
    for r in range(1, q):
        for c in (1, 2):
            source.append(AP(f"C{r},{c}", 3 * q,
                             crt_residue(3, c, q, r)))
    return 3 * q, source, q


def check_cover_and_private(period: int, source: list[AP]) -> dict[str, object]:
    owners = {
        x: [i for i, ap in enumerate(source) if x % ap.modulus == ap.residue]
        for x in range(period)
    }
    assert all(owners[x] for x in range(period))
    private = {i: [x for x, labels in owners.items() if labels == [i]]
               for i in range(len(source))}
    assert all(private[i] for i in range(len(source)))
    return {"period": period, "private_sizes": [len(private[i])
                                                   for i in range(len(source))]}


def induced_set(ap: AP, H: int, r: int, component_period: int) -> set[int]:
    g = gcd(ap.modulus, H)
    if (r - ap.residue) % g:
        return set()
    period = lcm(H, ap.modulus, component_period)
    return {
        t for t in range(component_period)
        if any(x % H == r % H
               and x % ap.modulus == ap.residue % ap.modulus
               and x % component_period == t
               for x in range(period))
    }


def minimal_cores(active: list[int], classes: dict[int, set[int]], universe: set[int]) -> list[tuple[int, ...]]:
    out = []
    for size in range(1, len(active) + 1):
        for subset in combinations(active, size):
            union = set().union(*(classes[i] for i in subset))
            if union != universe:
                continue
            if all(set().union(*(classes[i] for i in subset if i != j)) != universe
                   for j in subset):
                out.append(tuple(subset))
        if out:
            return out
    return out


def run_factorization_control(q: int = 5) -> dict[str, object]:
    period, source, H = control_source(q)
    check_cover_and_private(period, source)
    component_period = 3
    external = [i for i, ap in enumerate(source) if ap.modulus // gcd(ap.modulus, H) > 1]
    assert len(external) == 2 * q - 1
    U = list(range(1, q))

    classes: dict[tuple[int, int], set[int]] = {}
    private_classes: dict[tuple[int, int], set[int]] = {}
    active_by_r: dict[int, list[int]] = {}
    for r in U:
        active = []
        for i in external:
            C = induced_set(source[i], H, r, component_period)
            classes[r, i] = C
            if C:
                active.append(i)
        active_by_r[r] = active
        assert len(active) == 3
        for i in active:
            others = set().union(*(classes[r, j] for j in active if j != i))
            private_classes[r, i] = classes[r, i] - others
        assert set().union(*(classes[r, i] for i in active)) == set(range(3))
        assert set().union(*(private_classes[r, i] for i in active))

    buckets = [(r, t) for r in U for t in range(component_period)]
    neighbourhoods = {
        i: {(r, t) for r in U for t in private_classes.get((r, i), set())}
        for i in external
    }
    assert all(neighbourhoods[i] for i in external)
    assert all(neighbourhoods[i].isdisjoint(neighbourhoods[j])
               for i, j in combinations(external, 2))

    flows = list(product(*(sorted(neighbourhoods[i]) for i in external)))
    assert len(flows) == q - 1
    assert all(len(set(flow)) == len(flow) for flow in flows)

    core_sets = {}
    for r in U:
        cores = minimal_cores(active_by_r[r],
                              {i: classes[r, i] for i in active_by_r[r]},
                              set(range(component_period)))
        core_sets[r] = cores
        assert cores == [tuple(active_by_r[r])]
        assert all(all(i in core for i in active_by_r[r]
                       if private_classes[r, i]) for core in cores)

    for flow in flows:
        by_r = {r: [] for r in U}
        for i, bucket in zip(external, flow):
            by_r[bucket[0]].append(i)
        for r, labels in by_r.items():
            assert all(set(labels) <= set(core) for core in core_sets[r])

    # One quotient coordinate v=(3,1): each fibre has three unit buckets.
    label_count = len(external)
    M = {r: 3 for r in U}
    tau = q - 1  # the two labels C_{r,1}, C_{r,2} force every fibre.
    kappa = next(k for k in range(1, q)
                 if sum(sorted(M.values(), reverse=True)[:k]) >= label_count)
    lam = next(k for k in range(1, q)
               if k >= tau and sum(sorted(M.values(), reverse=True)[:k]) >= label_count)
    assert kappa == (2 * q - 1 + 2) // 3
    assert lam == tau

    def gamma(flow: tuple[tuple[int, int], ...]) -> int:
        return 2 * len({r for r, _ in flow})

    gammas = [gamma(flow) for flow in flows]
    Lambda = min(gammas)
    B_budget = sum(len(active_by_r[r]) - 1 for r in U)
    assert all(value == 2 * (q - 1) for value in gammas)
    assert Lambda == B_budget == 2 * (q - 1)

    multiplicities = {i: sum(i in core for cores in core_sets.values() for core in cores)
                      for i in external}
    D = sum(len(core) for cores in core_sets.values() for core in cores) - len(external)
    assert multiplicities[external[0]] == q - 1
    assert D == q - 2

    return {
        "q": q,
        "period": period,
        "external_labels": label_count,
        "flow_count": len(flows),
        "neighbourhoods_disjoint": True,
        "tau": tau,
        "kappa": kappa,
        "lambda": lam,
        "Lambda": Lambda,
        "budget": B_budget,
        "gamma_values": sorted(set(gammas)),
        "core_multiplicity_first_label": multiplicities[external[0]],
        "completion_excess": D,
    }


def run_service_correction() -> dict[str, object]:
    # §240's displayed partial-height numbers: q=3, p=5, e=2, L=231,
    # R=1155, N=3465.  Retaining [0]_9 services only F_0.
    q, R, candidate = 3, 1155, AP("u=9", 9, 0)
    period = 3 * R
    A = AP("A", R, 0)
    fibres = {
        j: {x for x in range(period)
            if x % R == 0 and x % period == (j * R) % period}
        for j in range(q)
    }
    union = {x for x in range(period) if x % candidate.modulus == candidate.residue}
    E = {x for x in range(period) if x % A.modulus == A.residue} - union
    private_indices = {j for j in range(q) if E & fibres[j]}
    serviced = {j for j in private_indices if fibres[j] <= union}
    assert private_indices == {1, 2}
    assert serviced == set()
    return {
        "q": q,
        "R": R,
        "candidate_label": candidate.modulus,
        "private_indices": sorted(private_indices),
        "G_indices": sorted(serviced),
        "g": len(serviced),
        "correction": "G is empty under E_A=A\\U; the retained-service fixture is not realizable.",
    }


def main() -> None:
    result = {
        "status": "PASS",
        "scope": (
            "Exact source-preserving private-bucket factorization and core "
            "multiplicity control; the indexed source repeats modulus 3q and "
            "does not certify an odd-distinct EB1 cover."
        ),
        "factorization": run_factorization_control(),
        "service_correction": run_service_correction(),
    }
    print(json.dumps(result, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
