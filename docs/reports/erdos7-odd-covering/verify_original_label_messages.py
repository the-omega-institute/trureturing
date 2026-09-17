#!/usr/bin/env python3
"""Exact message certificate on one literal, nonradial 315/17/19 law.
No optimizer, floating arithmetic, symmetry consolidation, or Lean claim.
"""
import json
from fractions import Fraction as F
from pathlib import Path
from math import lcm

def need(ok, msg):
    if not ok:
        raise ArithmeticError(msg)

def unique(pairs):
    out = {}
    for k, v in pairs:
        need(k not in out, 'duplicate JSON key ' + k)
        out[k] = v
    return out

def run(path):
    c = json.loads(Path(path).read_text(), object_pairs_hook=unique)
    Q = 315
    ds = [d for d in range(2, Q + 1) if Q % d == 0]
    bad = [(3, 0), (5, 0), (7, 0), (9, 2), (15, 4)]
    xs = [x for x in range(Q) if all((x % d != r for d, r in bad))]
    N = len(xs)
    need(N == 102 and c['old_survivors'] == N, 'literal source')
    need(c['source'] == 'uniform on literal old survivors', 'source law')
    co = [3, 9, 15, 21, 45, 63, 105, 315, 5, 7, 35]
    masks = {17: [(d, 1 if i < 8 else 2, i + 1) for i, d in enumerate(co)], 19: [(d, 1 if i < 8 else 3, i + 1) for i, d in enumerate(co)]}
    need(c['old_forbidden'] == [list(z) for z in bad], 'source label inventory')
    need(c['masks'] == {str(p): [list(z) for z in rows] for p, rows in masks.items()}, 'mixed label inventory')
    qs = {}
    ts = {}
    bs = {}
    goods = {}
    for p in (17, 19):
        qs[p] = []
        ts[p] = []
        bs[p] = []
        goods[p] = []
        for x in xs:
            good = [y for y in range(1, p) if all((x % d != r or y != z for d, r, z in masks[p]))]
            a = F(p - 1 - len(good), p - 1)
            de = F(7, p - 2)
            g = 1 / (1 - min(a, de))
            beta = max(F(), a - de) / (1 - de)
            need((16 if p == 17 else 18) in good, 'literal globally clean root')
            need(F(len(good)) * g / (p - 1) == 1 - beta, 'killed row mass')
            qs[p].append(1 - beta)
            ts[p].append(g / (p - 1))
            bs[p].append(beta)
            goods[p].append(good)
    q = [a * b for a, b in zip(qs[17], qs[19])]
    u = [a * b for a, b in zip(ts[17], qs[19])]
    v = [a * b for a, b in zip(qs[17], ts[19])]
    w = [a * b for a, b in zip(ts[17], ts[19])]
    H = [[q, u, v, w], [u, u, w, w], [v, w, v, w], [w, w, w, w]]
    labels = [(g, d) for g in range(4) for d in ds]
    doms = [sorted({x % d for x in xs}) for g, d in labels]
    n = len(labels)
    need(c['labels'] == [list(z) for z in labels] and c['domains'] == doms, 'all nonempty original old domains')
    need(c['charge17'] == str(sum(bs[17]) / N) == str(F(1, 1632)), 'positive17 charge')
    need(c['charge19_physical17'] == str(sum(bs[19]) / N) == str(F(1, 1836)), 'physical19 charge')
    need(c['eta_mass'] == str(sum(q) / N) == str(F(9781, 9792)), 'same final killed mass')
    scale = lcm(*(z.denominator * N for row in H for f in row for z in f))
    need(scale == c['scale'], 'scale')
    HH = [[[int(z * scale / N) for z in f] for f in row] for row in H]
    index = [{r: i for i, r in enumerate(dd)} for dd in doms]
    unary = []
    pair = {}
    for i, (g, d) in enumerate(labels):
        row = [0] * len(doms[i])
        for k, x in enumerate(xs):
            row[index[i][x % d]] += HH[g][g][k] + 2 * sum((HH[g][h][k] for h in range(4)))
        unary.append(row)
    for i, (g, d) in enumerate(labels):
        for j, (h, e) in enumerate(labels[:i]):
            mat = [[0] * len(doms[j]) for _ in doms[i]]
            for k, x in enumerate(xs):
                mat[index[i][x % d]][index[j][x % e]] += 2 * HH[g][h][k]
            pair[i, j] = mat
    const = sum((sum((sum(f) for f in row)) for row in HH))
    adj = [[F(z) for z in row] for row in unary]
    seen = set()
    pmax = []
    for i, j, aa, bb in c['messages']:
        need((i, j) in pair and (i, j) not in seen, 'unique original pair')
        seen.add((i, j))
        a = list(map(F, aa))
        b = list(map(F, bb))
        need(len(a) == len(doms[i]) and len(b) == len(doms[j]), 'complete message domains')
        for r in range(len(a)):
            adj[i][r] -= a[r]
        for s in range(len(b)):
            adj[j][s] -= b[s]
        pmax.append(max((pair[i, j][r][s] + a[r] + b[s] for r in range(len(a)) for s in range(len(b)))))
    pmax.extend((max(map(max, mat)) for ij, mat in pair.items() if ij not in seen))
    bound = F(const + sum(map(max, adj)) + sum(pmax), scale)
    entry = F(const + sum(map(max, unary)) + sum((max(map(max, mat)) for mat in pair.values())), scale)
    assigned = c['maximizer']
    need([x[:2] for x in assigned] == [list(z) for z in labels], 'maximizer labels')
    rr = [index[i][t[2]] for i, t in enumerate(assigned)]
    value = F(const + sum((unary[i][r] for i, r in enumerate(rr))) + sum((pair[i, j][rr[i]][rr[j]] for i, j in pair)), scale)
    need(bound == value == F(846619, 55488), 'exact upper and actual assignment match')
    need(str(bound) == c['message_bound'] == c['attained'], 'reported maximum')
    need(entry == F(c['entrywise_bound']), 'reported entrywise bound')
    need(bound - value == F(c['gap']) == 0, 'reported upper/lower gap')
    need(entry - bound == F(c['improvement']) == F(12393530887, 19995655680), 'exact strict improvement')
    profiles = {}
    for m in (9, 15):
        cells = [sum((q[k] for k, x in enumerate(xs) if x % m == r), F()) / N for r in range(m)]
        profiles[m] = [max((cells[r] for r in range(m) if r % 3 == a)) for a in range(3)]
    star_gap = 2 * (max(profiles[9]) + max(profiles[15]) - max((a + b for a, b in zip(profiles[9], profiles[15]))))
    need(profiles == {9: [F(), F(3, 17), F(4, 17)], 15: [F(), F(3, 17), F(2, 17)]} and star_gap == F(2, 17), 'actual shared modulus3 conflict')
    need(c['divisibility_star'] == {'central_original_modulus': 3, 'neighbor_original_moduli': [9, 15], 'M9': list(map(str, profiles[9])), 'M15': list(map(str, profiles[15])), 'gap': str(star_gap), 'L1_coefficient': 4}, 'reported local cut')
    mass = F()
    moment = F()
    for k, x in enumerate(xs):
        loads = [1 + sum((x % d == assigned[g * len(ds) + j][2] for j, d in enumerate(ds))) for g in range(4)]
        for y in goods[17][k]:
            for z in goods[19][k]:
                atom = ts[17][k] * ts[19][k] / N
                L = loads[0] + (y == 16) * loads[1] + (z == 18) * loads[2] + (y == 16 and z == 18) * loads[3]
                mass += atom
                moment += atom * L * L
    need(mass == F(c['eta_mass']) and moment == bound, 'direct actual point scan')
    mods = [d for d, r in bad] + [17, 19] + [d * p for p in (17, 19) for d, r, y in masks[p]]
    need(len(mods) == len(set(mods)) == 29 and all((d > 1 and d % 2 for d in mods)), 'literal distinct odd forbidden labels')
    need(lcm(*mods) == 101745, 'literal period')
    print(json.dumps({'maximum': str(bound), 'signed_final_Q': str(bound - 484 * mass), 'strict_entrywise_improvement': str(entry - bound), 'distinct_odd_forbidden': 29, 'full_original_tests': 48, 'all_nonempty_old_residue_choices': sum(map(len, doms)), 'local_shared_label_cut': str(star_gap), 'verification': 'exact stdlib reconstruction; no Lean'}, indent=2))
    if __name__ != '__main__':
        return locals()
if __name__ == '__main__':
    import sys
    run(sys.argv[1] if len(sys.argv) > 1 else Path(__file__).with_name('original_label_message_certificate.json'))
