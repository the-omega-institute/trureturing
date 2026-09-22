#!/usr/bin/env python3
"""Exact endpoint certificates for the full type-B column-cap tradeoff.

The continuum assertion is proved by affine interpolation in the companion
note. This checker verifies literal independent layouts at its endpoints
and the pointwise dual profiles proving both new supporting lines. The
third lower bound is the existing unrestricted minimax from report392.
All checks remain active under -O; standard library only.
"""

from fractions import Fraction as F
from itertools import product
import json


B = ((1, 1), (2, 2), (2, 3), (3, 2), (3, 4), (4, 2), (4, 5))
I = (1, 1)
H = {(2, 2), (3, 2), (4, 2)}
P = {(2, 3), (3, 4), (4, 5)}
FIRST_BREAK = F(5, 24)
SECOND_BREAK = F(105, 332)


def check(condition, message):
    if not condition:
        raise ValueError(message)


def loss(point, layout):
    row, col, point_row, point_col = layout
    r, c = point
    return (1 + (r == row) + (c == col) + (point == (point_row, point_col)))**2


def lower_envelope(beta):
    check(type(beta) in (int, F), "exact rational column cap required")
    beta = F(beta)
    check(beta >= F(1, 5), "five active columns require a cap of at least one fifth")
    return max(6 - 9 * beta, F(19, 4) - 3 * beta, F(631, 166))


def optimal_capped_root_law(beta):
    """Return an attaining actual law for any rational cap beta>=1/5."""
    value = lower_envelope(beta)
    beta = F(beta)
    if beta <= FIRST_BREAK:
        isolated, hub, private = beta, beta / 3, (1 - 2 * beta) / 3
    elif beta <= SECOND_BREAK:
        isolated, hub, private = F(1, 4) - beta / 5, beta / 3, F(1, 4) - 4 * beta / 15
    else:
        isolated, hub, private = F(62, 332), F(35, 332), F(55, 332)
    law = {point: isolated if point == I else hub if point in H else private for point in B}
    check(sum(law.values()) == 1 and min(law.values()) >= 0, "actual root law normalizes")
    return law, value


def root_maximum(law):
    best, witness, count = F(-1), None, 0
    for layout in product(range(5), range(7), range(5), range(7)):
        score = sum((weight * loss(point, layout) for point, weight in law.items()), F(0))
        if score > best:
            best, witness = score, layout
        count += 1
    return best, witness, count


def verify():
    private_centres = [(r, c, r, c) for r, c in sorted(P)]
    isolated_centre = (1, 1, 1, 1)
    hub_private = [(r, 2, r, c) for r, c in sorted(P)]
    profiles = []
    for point in B:
        private_average = sum((F(loss(point, layout), 3) for layout in private_centres), F(0))
        four_average = (loss(point, isolated_centre)
                        + sum(loss(point, layout) for layout in private_centres)) / F(4)
        old_dual = (F(31, 166) * loss(point, isolated_centre)
                    + F(30, 166) * sum(loss(point, layout) for layout in hub_private)
                    + F(15, 166) * sum(loss(point, layout) for layout in private_centres))
        check(private_average == (1 if point == I else 2 if point in H else 6),
              "private-centre dual profile")
        check(four_average == (F(7, 4) if point in H else F(19, 4)),
              "four-centre dual profile")
        check(old_dual == F(631, 166), "existing unrestricted minimax dual")
        profiles.append(dict(point=point, private_average=str(private_average),
                             four_average=str(four_average), existing_dual=str(old_dual)))
    endpoints = []
    total_layouts = 0
    for beta in (F(1, 5), FIRST_BREAK, F(1, 4), SECOND_BREAK):
        law, target = optimal_capped_root_law(beta)
        columns = {col: sum(weight for (row, c), weight in law.items() if c == col) for col in range(7)}
        check(max(columns.values()) <= beta, "all column caps hold")
        maximum, witness, count = root_maximum(law)
        total_layouts += count
        check(maximum == target, "complete independent-layout maximum equals the lower curve")
        endpoints.append(dict(beta=str(beta), maximum=str(maximum), witness=witness,
                              isolated=str(law[I]), hub_each=str(law[2, 2]), private_each=str(law[2, 3]),
                              max_column=str(max(columns.values()))))
    check(6 - 9 * FIRST_BREAK == F(19, 4) - 3 * FIRST_BREAK == F(33, 8), "first breakpoint")
    check(F(19, 4) - 3 * SECOND_BREAK == F(631, 166), "second breakpoint")
    check(lower_envelope(F(1, 5)) == F(21, 5), "full-five root cap obstruction")
    check(lower_envelope(F(1, 4)) == 4, "sharp cap threshold for root target four")
    return dict(endpoints=endpoints, dual_profiles=profiles, total_layouts=total_layouts,
                scope="All actual laws on the exact type-B root graph, not selected component mixtures",
                status="exact endpoint and pointwise certificates; analytic interpolation proves the continuum")


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2, sort_keys=True))
