#!/usr/bin/env python3
"""Exact second moments for all independent height-two power-grid layouts.

Requires NumPy; no optimizer is used. For coprime integers p,q > 1, the nine
labels are p**a * q**b, 0 <= a,b <= 2. These are all divisors of p**2*q**2
when p and q are primes. Composite inputs still test just these nine labels.

Without arguments, verify three explicit laws on the repeated type-B source.
Research input: --source-json PATH, with an object of the form
  {"p": 5, "q": 7, "points": [[x, y], ...], "weights": [w, ...]}.
Coordinates are canonical residues modulo p**2 and q**2; points are unique.
Weights are nonnegative integers with positive sum and are normalized by
that sum. All checks remain enabled under -O.

The maximum is for the supplied law, not a minimax over supported laws.
The program does not certify source-tree hypotheses for arbitrary input.
"""

import argparse
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations, islice, product
import json
from math import gcd, prod
from pathlib import Path

import numpy as np


INT64_MAX = int(np.iinfo(np.int64).max)


class ProgramLimitError(ValueError):
    """An implementation or explicitly requested resource bound was exceeded."""


def check(condition, message):
    if not condition:
        raise ValueError(message)


def integer(value):
    return type(value) is int


@dataclass(frozen=True)
class LayoutMaximum:
    numerator: int
    denominator: int
    layout: dict
    baseline_choices: int

    @property
    def value(self):
        return Fraction(self.numerator, self.denominator)

    def output(self):
        return dict(
            exact_maximum=str(self.value),
            maximum_numerator=self.numerator,
            law_denominator=self.denominator,
            attaining_layout={str(d): a for d, a in self.layout.items()},
            baseline_choices=self.baseline_choices,
        )


class HeightTwoLayoutOracle:
    """Full independent-phase maximum for one finite, integer-weighted law."""

    def __init__(self, p, q, points):
        check(integer(p) and integer(q) and p > 1 and q > 1,
              "p and q must be integers greater than one")
        check(gcd(p, q) == 1, "p and q must be coprime")
        self.p, self.q = p, q
        self.p2, self.q2 = p * p, q * q
        self.carrier = self.p2 * self.q2
        if self.carrier > INT64_MAX:
            raise ProgramLimitError("carrier exceeds NumPy int64 range; no mathematical conclusion")
        self.points = tuple(tuple(point) for point in points)
        check(self.points, "source must be nonempty")
        check(all(len(point) == 2 and all(integer(v) for v in point)
                  for point in self.points), "points must be integer coordinate pairs")
        check(all(0 <= x < self.p2 and 0 <= y < self.q2 for x, y in self.points),
              "coordinates must be canonical residues modulo p squared and q squared")
        check(len(set(self.points)) == len(self.points), "source points must be unique")

        inverse = pow(self.p2, -1, self.q2)
        self.values = np.array([
            x + self.p2 * (((y - x) * inverse) % self.q2)
            for x, y in self.points
        ], dtype=np.int64)
        self.moduli = (1, p, self.p2, q, self.q2, p * q,
                       self.p2 * q, p * self.q2, self.carrier)
        self.base_moduli = (p, self.p2, q, self.q2, p * q)
        self.b_modulus, self.c_modulus = self.p2 * q, p * self.q2
        self.point_residues = {d: self.values % d for d in self.moduli}
        self.residues = {d: np.unique(self.point_residues[d]) for d in self.moduli}
        self.baseline_count = prod(len(self.residues[d]) for d in self.base_moduli)
        self.b_index = np.searchsorted(self.residues[self.b_modulus],
                                       self.point_residues[self.b_modulus])
        self.c_index = np.searchsorted(self.residues[self.c_modulus],
                                       self.point_residues[self.c_modulus])
        self.b_groups = [np.flatnonzero(self.b_index == i)
                         for i in range(len(self.residues[self.b_modulus]))]
        self.c_groups = [np.flatnonzero(self.c_index == i)
                         for i in range(len(self.residues[self.c_modulus]))]
        check(len(set(zip(self.b_index.tolist(), self.c_index.tolist()))) == len(self.points),
              "last two cylinder partitions must have singleton intersections")

    def weights(self, weights):
        weights = tuple(weights)
        check(len(weights) == len(self.points), "one weight is required per point")
        check(all(integer(w) and w >= 0 for w in weights),
              "weights must be nonnegative integers")
        denominator = sum(weights)
        check(denominator > 0, "weights must have positive sum")
        # A complete load is at most nine. This also bounds every nonnegative
        # intermediate sum used by the separation and reconstruction formulas.
        if 81 * denominator > INT64_MAX:
            raise ProgramLimitError("81 times total weight exceeds int64; rescale weights exactly")
        return np.array(weights, dtype=np.int64), denominator

    def layout_costs(self, layout):
        """Evaluate the literal nine-label squared load independently."""
        check(set(layout) == set(self.moduli), "layout must assign every power-grid label")
        check(all(integer(a) and 0 <= a < d for d, a in layout.items()),
              "layout residues must be canonical integers")
        load = np.zeros(len(self.points), dtype=np.int64)
        for d in self.moduli:
            load += self.point_residues[d] == layout[d]
        return load * load

    def separate(self, weights, chunk_size=512, max_baselines=None):
        w, denominator = self.weights(weights)
        check(integer(chunk_size) and chunk_size > 0, "chunk size must be positive")
        if max_baselines is not None:
            check(integer(max_baselines) and max_baselines > 0,
                  "max baselines must be positive when supplied")
            if self.baseline_count > max_baselines:
                raise ProgramLimitError(
                    f"{self.baseline_count} baselines exceed requested limit {max_baselines}; "
                    "enumeration was not completed")

        choices = product(*(range(len(self.residues[d])) for d in self.base_moduli))
        best, best_ids, examined = -1, None, 0
        while True:
            block = list(islice(choices, chunk_size))
            if not block:
                break
            ids = np.array(block, dtype=np.int64)
            examined += len(block)
            v = np.ones((len(block), len(self.points)), dtype=np.int64)
            for j, d in enumerate(self.base_moduli):
                v += (self.point_residues[d][None, :]
                      == self.residues[d][ids[:, j]][:, None])
            baseline = (v * v * w).sum(axis=1)
            h = (2 * v + 1) * w
            gb = np.column_stack([h[:, group].sum(axis=1) for group in self.b_groups])
            gc = np.column_stack([h[:, group].sum(axis=1) for group in self.c_groups])
            boosted = h + 2 * w
            hb = np.column_stack([boosted[:, group].max(axis=1) for group in self.b_groups])
            hc = np.column_stack([boosted[:, group].max(axis=1) for group in self.c_groups])
            h0, gb0, gc0 = h.max(axis=1), gb.max(axis=1), gc.max(axis=1)

            # B and C are partitions and B intersect C contains at most one
            # source point. Nonintersection terms separate; all possible
            # intersection corrections are covered by the final point scan.
            m0 = gb0 + gc0 + h0
            mb = (gb + hb).max(axis=1) + gc0
            mc = gb0 + (gc + hc).max(axis=1)
            intersection = gb[:, self.b_index] + gc[:, self.c_index] + 2 * w
            point_term = np.maximum(
                np.maximum(h0[:, None], hb[:, self.b_index]),
                np.maximum(hc[:, self.c_index], h + 4 * w))
            mi = (intersection + point_term).max(axis=1)
            totals = baseline + np.maximum(np.maximum(m0, mb), np.maximum(mc, mi))
            j = int(totals.argmax())
            if int(totals[j]) > best:
                best, best_ids = int(totals[j]), tuple(map(int, ids[j]))
        check(examined == self.baseline_count, "all baseline choices must be visited")

        layout = {1: 0, **{d: int(self.residues[d][j])
                           for d, j in zip(self.base_moduli, best_ids)}}
        v = np.ones(len(self.points), dtype=np.int64)
        for d in self.base_moduli:
            v += self.point_residues[d] == layout[d]
        # At only the winning baseline, reconstruct the three remaining phases
        # by direct B,C enumeration and point maximization. This independently
        # checks the compressed value before returning a literal witness.
        local_best, local_choices = -1, None
        for ib, ic in product(range(len(self.b_groups)), range(len(self.c_groups))):
            u = v + (self.b_index == ib) + (self.c_index == ic)
            gains = (2 * u + 1) * w
            iz = int(gains.argmax())
            score = int(np.dot(u * u, w)) + int(gains[iz])
            if score > local_best:
                local_best, local_choices = score, (ib, ic, iz)
        check(local_best == best, "winning baseline must agree with direct reconstruction")
        ib, ic, iz = local_choices
        layout.update({self.b_modulus: int(self.residues[self.b_modulus][ib]),
                       self.c_modulus: int(self.residues[self.c_modulus][ic]),
                       self.carrier: int(self.values[iz])})
        check(int(np.dot(self.layout_costs(layout), w)) == best,
              "literal attaining layout must match the full maximum")
        return LayoutMaximum(best, denominator, layout, examined)

    def brute_force(self, weights):
        """Independent small-source control; exponential in eight labels."""
        w, denominator = self.weights(weights)
        best, count = -1, 0
        for values in product(*(self.residues[d] for d in self.moduli[1:])):
            layout = {1: 0, **dict(zip(self.moduli[1:], map(int, values)))}
            best = max(best, int(np.dot(self.layout_costs(layout), w)))
            count += 1
        return Fraction(best, denominator), count


ROOT_B = ((1, 1), (2, 2), (2, 3), (3, 2), (3, 4), (4, 2), (4, 5))


def default_verification(chunk_size=512):
    controls = []
    for p, q, points, weights in (
        (5, 7, ((1, 1), (6, 8), (2, 9)), (2, 3, 5)),
        (5, 7, ((1, 1), (6, 1), (1, 8)), (0, 7, 4)),
        (4, 9, ((1, 1), (5, 10), (2, 11)), (2, 3, 5)),
    ):
        oracle = HeightTwoLayoutOracle(p, q, points)
        result = oracle.separate(weights, chunk_size)
        direct, layouts = oracle.brute_force(weights)
        check(result.value == direct, "small-source full independent enumeration disagrees")
        controls.append(dict(p=p, q=q, points=len(points), layouts=layouts,
                             integer_weights=list(weights), exact_maximum=str(direct)))

    # The default source's root graph meets every required root rectangle.
    rectangle_count = 0
    for rows, cols in product(combinations(range(5), 3), combinations(range(7), 5)):
        check(any(x in rows and y in cols for x, y in ROOT_B), "root product-tree condition")
        rectangle_count += 1
    check(len({y for _, y in ROOT_B}) == 5, "standalone seven-root projection condition")

    root332 = [62 if x == 1 else 35 if y == 2 else 55 for x, y in ROOT_B]
    root_maximum = max(
        sum(w * (1 + (x == a) + (y == b) + ((x, y) == (u, v))) ** 2
            for (x, y), w in zip(ROOT_B, root332))
        for a, b, u, v in product(range(5), range(7), range(5), range(7)))
    check(Fraction(root_maximum, 332) == Fraction(631, 166), "specified root332 law maximum")

    points = tuple((u[0] + 5 * v[0], u[1] + 7 * v[1])
                   for u, v in product(ROOT_B, repeat=2))
    oracle = HeightTwoLayoutOracle(5, 7, points)
    check(len(points) == 49 and oracle.baseline_count == 56000, "default source dimensions")
    kinds = [0 if x == 1 else 1 if y == 2 else 2 for x, y in ROOT_B]
    laws = (
        ("root18_product", (3, 2, 3), (3, 2, 3), 18, Fraction(2117, 324)),
        ("root332_product", (62, 35, 55), (62, 35, 55), 332, Fraction(361237, 55112)),
        ("low_high300_product", (54, 35, 47), (63, 27, 52), 300, Fraction(6157, 1000)),
    )
    target = Fraction(529, 81)
    results = []
    for name, low, high, denominator, expected in laws:
        check(low[0] + 3 * low[1] + 3 * low[2] == denominator,
              "low-position probability normalizes")
        check(high[0] + 3 * high[1] + 3 * high[2] == denominator,
              "high-position probability normalizes")
        weights = [low[kinds[i]] * high[kinds[j]] for i, j in product(range(7), repeat=2)]
        result = oracle.separate(weights, chunk_size)
        check(result.value == expected, "explicit product-law full maximum")
        results.append(dict(
            law=name, type_order=["isolated", "hub", "private"], type_sizes=[1, 3, 3],
            low_per_point_numerators=list(low), high_per_point_numerators=list(high),
            digit_law_denominator=denominator, target=str(target),
            target_minus_maximum=str(target - result.value), meets_target=result.value <= target,
            **result.output(),
        ))
    return dict(
        scope="Exact full independent-divisor maximum for three specified laws; no minimax or all-source theorem",
        p=5, q=7, source="two digit positions in type B", points=len(points),
        root_points=[list(point) for point in ROOT_B],
        root_rectangle_checks=rectangle_count, small_brute_controls=controls,
        root332_full_root_layouts=1225, root332_exact_root_maximum=str(Fraction(root_maximum, 332)),
        total_baselines=sum(result["baseline_choices"] for result in results), laws=results,
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-json", type=Path, help="integer-weighted source JSON; omit for default checks")
    parser.add_argument("--chunk-size", type=int, default=512, help="baseline chunk size (default: 512)")
    parser.add_argument("--max-baselines", type=int, help="optional research-input enumeration limit")
    args = parser.parse_args()
    try:
        if args.source_json is None:
            check(args.max_baselines is None, "--max-baselines applies only with --source-json")
            output = default_verification(args.chunk_size)
        else:
            data = json.loads(args.source_json.read_text(encoding="utf-8"))
            check(isinstance(data, dict), "source JSON must be an object")
            check(set(data) == {"p", "q", "points", "weights"},
                  "source JSON fields must be p, q, points, weights")
            oracle = HeightTwoLayoutOracle(data["p"], data["q"], data["points"])
            result = oracle.separate(data["weights"], args.chunk_size, args.max_baselines)
            output = dict(
                scope="Maximum for nine power-grid labels; all divisors only when p and q are primes",
                p=oracle.p, q=oracle.q, source_points=len(oracle.points),
                carrier=oracle.carrier, layout_moduli=list(oracle.moduli),
                **result.output(),
            )
    except (ValueError, TypeError, KeyError, OSError) as error:
        parser.exit(2, f"{type(error).__name__}: {error}\n")
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
