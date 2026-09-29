"""Finite divisor geometry and actual sharp witnesses for thin-fibre bounds.

The all-phase conclusion is proved in report759. This checks every small
budget allocation and reconstructs the explicit numerical CRT witnesses.
No phase search or optimizer is part of the retained consumer.
"""
from itertools import combinations
from math import gcd
from pathlib import Path
import json


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def compositions(total, parts):
    if parts == 1:
        yield (total,)
    else:
        for first in range(total + 1):
            for rest in compositions(total - first, parts - 1):
                yield (first,) + rest


def max_promoted(values, threshold, budget):
    deficits = sorted(max(0, threshold - value) for value in values)
    used = 0
    count = 0
    for deficit in deficits:
        if used + deficit > budget:
            break
        used += deficit
        count += 1
    return count


def calculate():
    D = (3, 5, 7, 9, 15, 21, 35, 45, 63, 105, 315)
    pair_geometry = {}
    for threshold in (7, 8, 9, 10):
        lower = 2 * threshold - len(D)
        allowed_gcds = sorted({gcd(delta, 315) for delta in range(1, 315)
                              if sum(delta % d == 0 for d in D) >= lower})
        pair_geometry[str(threshold)] = allowed_gcds
    need(pair_geometry == {'7': [15, 21, 35, 45, 63, 105],
                           '8': [45, 63, 105], '9': [105], '10': []},
         'exact common-label difference geometry')

    # Once a common coordinate line has been established, the three rows below
    # are the complete small allocation problems in the prose, not a phase sample.
    grid_checks = []
    for columns in (5, 7):
        count = 0
        maximum = -1
        witness = None
        for line3 in compositions(2, 3):
            for linep in compositions(4, columns):
                count += 1
                value = max_promoted([a + b for a in line3 for b in linep], 4, 2)
                if value > maximum:
                    maximum, witness = value, [line3, linep]
        need(maximum == 4, 'complete 3 by p threshold4 allocation bound')
        grid_checks.append(dict(shape=[3, columns],line_budget=[2,4],point_budget=2,
                                allocations_checked=count,maximum=maximum,witness=witness))

    group_max = -1
    group_witness = None
    group_count = 0
    for amounts in compositions(4, 3):
        group_count += 1
        value = max_promoted([v for v in amounts for _ in range(3)], 4, 4)
        if value > group_max:
            group_max, group_witness = value, amounts
    need(group_max == 4, 'complete three groups of three allocation bound')

    core = [(3,0),(5,0),(7,0),(9,4),(15,11),(21,8),
            (35,9),(45,1),(63,1),(105,59),(315,179)]
    X = [x for x in range(315) if all(x % m != a for m,a in core)]
    need(len(X) == 75, 'actual core carrier')
    D0 = (3,5,7,15,21,35,105)
    top = (9,45,63,315)
    examples = []

    # Every example retains distinct numerical labels 11*d and a pure11 zero.
    for threshold in (10,9,8,7):
        if threshold == 10:
            phases = {d: 2 % d for d in D}
            colors = {d: 1+i%10 for i,d in enumerate(D)}
        elif threshold == 9:
            phases = {d: (2 if d in D0 or d in (9,45) else 107) % d for d in D}
            colors = {d: 1+D0.index(d) for d in D0}
            colors.update({9:8,45:9,63:8,315:9})
        elif threshold == 8:
            phases = {d: 2 % d for d in D0}
            phases.update({9:2%9,45:107%45,63:212%63,315:2})
            colors = {d: 1+D0.index(d) for d in D0}
            colors.update({9:8,45:8,63:8,315:9})
        else:
            phases = {d: (17 if d in (9,45,63,315) else 2) % d for d in D}
            colors = {3:1,5:2,15:3,7:4,21:5,35:6,105:7,
                      9:4,45:5,63:6,315:7}
        hits = {x:sum(x%d == phases[d] for d in D) for x in range(315)}
        live = {x:10-len({colors[d] for d in D if x%d == phases[d]}) for x in range(315)}
        high_rows = [x for x in range(315) if hits[x] >= threshold]
        thin_rows = [x for x in range(315) if live[x] <= 10-threshold]
        need(len(high_rows) == 11-threshold, 'sharp hit threshold example')
        need(len(thin_rows) == 11-threshold and set(thin_rows) <= set(X),
             'sharp actual thin-fibre example on the same core')
        literal = [[11,0]]
        for d in D:
            a = phases[d]
            while a % 11 != colors[d]:
                a += d
            need(0 <= a < 11*d, 'literal CRT phase')
            literal.append([11*d,a])
        for x in range(315):
            actual = [y for y in range(11)
                      if all(not (x % gcd(m,315) == a % gcd(m,315) and y == a % 11)
                             for m,a in literal)]
            need(len(actual) == live[x], 'literal root count agrees with color construction')
        examples.append(dict(threshold=threshold,bound=11-threshold,
                             high_rows=high_rows,thin_rows=thin_rows,
                             actual_originals=literal))

    out = dict(scope="Complete finite geometry and sharp actual witnesses for report759; universal phase bounds use the accompanying proof",divisors=D,pair_geometry=pair_geometry,
               grid_budget_checks=grid_checks,
               grouped_budget_check=dict(allocations_checked=group_count,maximum=group_max,
                                         witness=group_witness),
               actual_core=core,sharp_examples=examples,lean_verification=False)
    return json.loads(json.dumps(out))


if __name__ == "__main__":
    result = calculate()
    expected = json.loads(Path(__file__).with_suffix(".json").read_text())
    need(result == expected, "retained result agrees with exact recomputation")
    print(json.dumps(result, indent=2))
