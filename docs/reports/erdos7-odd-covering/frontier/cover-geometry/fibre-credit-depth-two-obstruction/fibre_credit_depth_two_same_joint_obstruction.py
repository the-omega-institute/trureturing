#!/usr/bin/env python3
"""Independent exact SAME85 dual check: prefix-count squares, not pair enumeration."""
from fractions import Fraction as F
from collections import defaultdict, Counter
from itertools import product
from math import gcd, prod
from pathlib import Path
import json
import hashlib
import argparse

def need(ok, message):
    if not ok:
        raise RuntimeError(message)

def rat(d):
    need(type(d['num']) is int and type(d['den']) is int and d['den'] > 0, 'rational schema')
    return F(d['num'], d['den'])


def calculate(path):
    obj = json.loads(path.read_text())
    head = obj['heads']['same']
    classes = [(d['modulus'], d['residue']) for d in obj['common_classes'] + head['extra_classes']]
    need(all(type(m) is int and type(a) is int and m > 1 and m % 2 and 0 <= a < m
             for m, a in classes), 'literal integer originals')
    need(classes == [(3,0),(9,1),(5,0),(7,0),(15,1),(45,22),(21,1),(63,16),(35,3),(105,74),(315,47)], 'actual SAME85 head')
    rows = [x for x in range(315) if all(x % m != a for m,a in classes)]
    need(len(rows) == 85 == head['expected_residue_count'], '85 actual rows')
    beta = rat(head['beta'])
    need(beta == F(1653,31250) and beta > F(1,19), 'actual threshold, not 1/19')
    lambda_sum = defaultdict(F)
    cyl = {x:F(0) for x in rows}
    for entry in head['lambda']:
        j,D = entry['j'],tuple(entry['D'])
        need(type(j) is int and j in range(3) and D in ((),(5,),(7,),(5,7)), 'first-mode type')
        m,a,w = entry['modulus'],entry['residue'],rat(entry['weight'])
        need(type(m) is int and type(a) is int and m == 3**j*prod(D) and 0 <= a < m and w >= 0, 'cylinder parameters')
        lambda_sum[j,D] += w
        for x in rows:
            if x % m == a:
                cyl[x] += w
    for (j,D),total in lambda_sum.items():
        need(total <= prod((F(p,p-1) for p in D),start=F(1))-1, 'all cylinder budgets')

    def lift_phase(j,e,f,a):
        value,modulus = 0,1
        for n,r in ((3**j,a%(3**j)),(5**e,a%5),(7**f,a%7)):
            if n > 1:
                value += modulus*((r-value)*pow(modulus,-1,n)%n)
                modulus *= n
        need(0 <= value < modulus, 'one globally fixed full CRT phase')
        return value,modulus

    def delta_numerators(p,H):
        den = p**max(H-1,0)
        t = [den//p**max(h-1,0) for h in range(H+1)]
        return [t[h]-t[h+1] if h < H else t[h] for h in range(H+1)],den

    checked_pairs = 0
    def finite_vector(layout):
        nonlocal checked_pairs
        E,G = layout['E'],layout['F']
        need(type(E) is int and type(G) is int and 0 <= E <= 8 and 0 <= G <= 8, 'finite heights')
        slots = list(product(range(3),range(E+1),range(G+1)))
        labels = layout['labels']
        need(len(slots) == len(labels), 'one label per numerical slot, f-fast order')
        phases = []
        for (j,e,f),a in zip(slots,labels):
            b = 3**j*(5 if e else 1)*(7 if f else 1)
            need(type(a) is int and 0 <= a < b, 'first-digit label domain')
            phase,n = lift_phase(j,e,f,a)
            need(phase % b == a, 'full phase projects to supplied label')
            phases.append((phase,n,a,b))
        for i,(p,n,a,b) in enumerate(phases):
            for pp,nn,aa,bb in phases[i:]:
                need(((p-pp)%gcd(n,nn) == 0) == ((a-aa)%gcd(b,bb) == 0), 'higher zero digits introduce no extra pair incompatibility')
                checked_pairs += 1
        d5,n5 = delta_numerators(5,E)
        d7,n7 = delta_numerators(7,G)
        result = {}
        for x in rows:
            prefix = [[0]*(G+1) for _ in range(E+1)]
            for (_,e,f),(_,_,a,b) in zip(slots,phases):
                if x % b == a:
                    prefix[e][f] += 1
            for h in range(E+1):
                for k in range(G+1):
                    if h: prefix[h][k] += prefix[h-1][k]
                    if k: prefix[h][k] += prefix[h][k-1]
                    if h and k: prefix[h][k] -= prefix[h-1][k-1]
            num = sum(d5[h]*d7[k]*prefix[h][k]**2 for h in range(E+1) for k in range(G+1))
            result[x] = F(num,n5*n7)
        return result

    finite = dict(cyl)
    coherent = []
    weight_total = F(0)
    heights = Counter()
    for entry in head['layouts']:
        w = rat(entry['weight'])
        need(w >= 0,'nonnegative layout weight')
        weight_total += w
        layout = entry['layout']
        if layout['kind'] == 'finite':
            vec = finite_vector(layout)
            heights[layout['E'],layout['F']] += 1
            for x in rows: finite[x] += w*vec[x]
        else:
            need(layout['kind'] == 'coherent_infinite' and type(layout['a']) is int and 0 <= layout['a'] < 315, 'coherent CRT centre')
            coherent.append((layout['a'],w))
    need(weight_total <= beta, 'total layout budget')

    def coherent_factor(p,H):
        if H is None:
            r = F(1,p)
            return 1 + 2/(1-r)**2 + 1/(1-r)
        return 1+sum((F(2*h+1,p**(h-1)) for h in range(1,H+1)),F(0))

    def combined(H):
        f5,f7 = coherent_factor(5,H),coherent_factor(7,H)
        answer = dict(finite)
        for a,w in coherent:
            for x in rows:
                J = 1+(x%3==a%3)+(x%9==a%9)
                answer[x] += w*J**2*(f5 if x%5==a%5 else 1)*(f7 if x%7==a%7 else 1)
        return answer

    answer = combined(None)
    minimum = min(answer.values())
    need(minimum == rat(head['claimed_minimum']) == F(172873706451315756773,172872000000000000000) > 1, 'independent exact dual minimum')
    finite_minima = {}
    for H in range(7,16):
        vals = combined(H)
        lo = min(vals.values())
        finite_minima[H] = {'minimum':str(lo),'gap':str(lo-1),'minimizers':[x for x in rows if vals[x]==lo]}
        if lo > 1:
            break
    need(H == 8 and lo == F(32169707786555332783494109, 32169648437500000000000000) > 1,
         'declared exact finite height8 witness')
    need(len(coherent) == 59 and heights == Counter({(6, 6): 11, (7, 7): 9}),
         'all query components embed into common height8')
    out = {
        'common_finite_height':8, 'common_finite_period':9*5**8*7**8,
        'finite_rowwise_lower':{str(x):str(vals[x]) for x in rows},
        'certificate_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
        'method':'Independent prefix-count multiscale squares; canonical global CRT lift checked separately.',
        'head':'SAME85', 'rows':len(rows),'beta':str(beta),'layout_weight':str(weight_total),
        'lambda_count':len(head['lambda']),'coherent_count':len(coherent),
        'finite_height_counts':{str(k):v for k,v in heights.items()},'global_phase_pair_checks':checked_pairs,
        'exact_minimum':str(minimum),'strict_gap':str(minimum-1),
        'minimizers':[x for x in rows if answer[x]==minimum],
        'coherent_finite_truncations':finite_minima,'first_checked_strict_finite_height':H,
        'scope':'At beta=1653/31250; no claim at beta=1/19. Ordinary proof and exact finite check, not Lean. Blocks this common-source scalar sufficient criterion, not covering.'
    }
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path, default=Path(__file__).resolve().with_name('fibre_credit_depth_two_same_joint_obstruction_witnesses.json'))
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = json.loads(json.dumps(calculate(args.certificate)))
    rendered = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output is None:
        need(json.loads(Path(__file__).resolve().with_suffix('.json').read_text()) == result,
             'retained result agrees with the exact finite dual reconstruction')
        print(rendered, end='')
    else:
        args.output.write_text(rendered)


if __name__ == '__main__':
    main()
