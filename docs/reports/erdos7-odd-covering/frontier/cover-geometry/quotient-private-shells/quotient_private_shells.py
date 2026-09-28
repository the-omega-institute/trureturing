"""Exact fixed controls for same-private-point quotient/shell identities.

Standard library only; all checks remain active under optimization.
The symbolic proof and whole-cover boundaries belong to the Library note.
"""
import argparse
import json
from fractions import Fraction
from math import gcd, lcm
from pathlib import Path


def demand(ok, text):
    if not ok:
        raise ValueError(text)


def valuation(n, p):
    demand(n != 0, 'valuation at zero')
    e = 0
    while n % p == 0:
        e += 1
        n //= p
    return e


def factors(n):
    out = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            out.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        out.append(n)
    return out


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def one_case(name, classes, points, expected_cover):
    period = lcm(*(m for a, m in classes))
    primes = factors(period)
    checks = {'labelwise_quotient_equalities': 0, 'aggregate_shell_equalities': 0, 'slack_negative': 0, 'slack_zero': 0, 'slack_positive': 0}
    for x in points:
        hits = [i for i, (a, m) in enumerate(classes) if (x-a) % m == 0]
        demand(len(hits) == 1, 'point is not private')
        owner = hits[0]
        for p in primes:
            H = valuation(period, p)
            e = valuation(classes[owner][1], p) if classes[owner][1] % p == 0 else 0
            line_step = period // p**H
            shells = [[] for _ in range(H)]
            for k in range(p**H):
                y = (x + k*line_step) % period
                delta = (y-x) % p**H
                if delta:
                    b = valuation(delta, p)
                    mult = sum((y-a) % m == 0 for a, m in classes)
                    shells[b].append(mult)
            shell_excess = [Fraction(sum(v)-len(v), len(v)) for v in shells]
            if expected_cover:
                demand(all(c >= 1 for s in shells for c in s), 'missing complete line point')
            for cut in divisors(period):
                ell = valuation(cut, p) if cut % p == 0 else 0
                z = x % cut
                t = (x-z) // cut
                original_sum = Fraction(0)
                quotient_sum = Fraction(0)
                for a, m in classes:
                    h = valuation(m, p) if m % p == 0 else 0
                    cofactor = m // p**h
                    delta = a-x
                    original = Fraction(0)
                    if h and delta % cofactor == 0 and delta % m != 0:
                        b = valuation(delta, p)
                        if b >= ell:
                            original = Fraction(1, p**(h-b-1))
                    g = gcd(m, cut)
                    r = m//g
                    quotient = Fraction(0)
                    if (a-z) % g == 0 and r % p == 0:
                        theta = (((a-z)//g) * pow(cut//g, -1, r)) % r
                        ht = valuation(r, p)
                        dt = theta-t
                        if dt % (r//p**ht) == 0 and dt % r != 0:
                            bt = valuation(dt, p)
                            quotient = Fraction(1, p**(ht-bt-1))
                    demand(original == quotient, f'labelwise mismatch {name,x,p,cut,a,m}')
                    original_sum += original
                    quotient_sum += quotient
                    checks['labelwise_quotient_equalities'] += 1
                slack = quotient_sum - max(e-ell, 0)*(p-1)
                direct_slack = (p-1) * sum(shell_excess[ell:], Fraction(0))
                demand(slack == direct_slack, f'shell slack mismatch {name,x,p,cut}')
                checks['aggregate_shell_equalities'] += 1
                checks['slack_negative' if slack < 0 else ('slack_positive' if slack > 0 else 'slack_zero')] += 1
                if expected_cover and ell < e:
                    demand(slack >= 0, 'whole-cover valid Lettl-Sun cut fails')
    return {'name': name, 'period': period, 'private_points_checked': len(points), **checks}


parser = argparse.ArgumentParser()
parser.add_argument('--output', default=str(Path(__file__).with_suffix('.json')))
args = parser.parse_args()
raw = {'cases': [{'name': 'distinct_even_period12',
            'classes': [[0, 2], [0, 3], [1, 4], [5, 6], [7, 12]],
            'whole_cover': True,
            'private_points': 'all'},
           {'name': 'even_height_four_period48',
            'classes': [[0, 2], [0, 3], [1, 4], [5, 6], [7, 24], [19, 48], [43, 48]],
            'whole_cover': True,
            'private_points': 'all'},
           {'name': 'odd_repeated_height_three_other_prime',
            'classes': [[0, 3],
                        [1, 3],
                        [2, 9],
                        [5, 9],
                        [8, 27],
                        [17, 27],
                        [26, 135],
                        [53, 135],
                        [80, 135],
                        [107, 135],
                        [134, 135]],
            'whole_cover': True,
            'private_points': 'all'},
           {'name': 'uncut_does_not_imply_suffix',
            'classes': [[0, 9], [10, 15], [7, 21], [22, 33], [13, 39]],
            'whole_cover': False,
            'private_points': [0, 10, 7, 22, 13],
            'hole': 2,
            'focused': {'point': 0,
                        'prime': 3,
                        'expected_shell_services': ['4', '0'],
                        'expected_suffix_slacks': ['0', '-2', '0']}},
           {'name': 'all_suffixes_do_not_imply_shell_coverage',
            'classes': [[1, 3], [0, 9], [30, 45], [21, 63], [33, 99]],
            'whole_cover': False,
            'private_points': [1, 0, 30, 21, 33],
            'hole': 2,
            'focused': {'point': 0,
                        'prime': 3,
                        'expected_shell_services': ['1', '3'],
                        'expected_suffix_slacks': ['0', '1', '0']}}],
 'scope': 'Fixed arithmetic controls, not Lean verification. Whole covers are even or have '
          'repeated moduli. Noncover conclusions are restricted to the displayed original '
          'private point and prime; normalized parameterized controls also have distinct odd '
          'divisor-closed labels.'}

def crt(residues, moduli):
    total = 1
    for modulus in moduli:
        total *= modulus
    return sum(a*(total//m)*pow(total//m,-1,m) for a,m in zip(residues,moduli)) % total


def normalized_closed_family(p, e, qs):
    demand(p >= 3 and e >= 2 and len(qs) == p-1, 'family parameters')
    demand(factors(p) == [p] and all(q%2 and factors(q) == [q] and q != p for q in qs), 'primality parameters')
    demand(len(set(qs)) == len(qs), 'duplicate q primes')
    carrier = [p**e]+qs
    Q = 1
    for modulus in carrier:
        Q *= modulus
    classes = []
    witnesses = []
    for k in range(1,e+1):
        a = p**(k-1) if k < e else 0
        classes.append((a,p**k))
        witnesses.append(crt([a]+[2]*len(qs),carrier))
    for j,q in enumerate(qs):
        classes.append((1,q))
        cofactors = [2]*len(qs)
        cofactors[j] = 1
        witnesses.append(crt([2*p**(e-1)]+cofactors,carrier))
        for r in range(1,e+1):
            a = 2*p**(r-1) if r < e else p**(e-1)
            classes.append((crt([a,0],[p**r,q]),p**r*q))
            cofactors = [2]*len(qs)
            cofactors[j] = 0
            witnesses.append(crt([a]+cofactors,carrier))
    classes = [((a-1)%m,m) for a,m in classes]
    witnesses = [(x-1)%Q for x in witnesses]
    return {'name':f'normalized_divisor_closed_p{p}_height{e}', 'classes':classes,
            'whole_cover':False,'private_points':sorted(set(witnesses+[Q-1])),
            'hole':(crt([2*p**(e-1)]+[0]*len(qs),carrier)-1)%Q,
            'closed_control':True,
            'failed_private_direction':{'point':(crt([2*p**(e-1)]+[1]+[2]*(len(qs)-1),carrier)-1)%Q,'prime':qs[0]},
            'focused':{'point':Q-1,'prime':p,
                       'expected_shell_services':[str(p)]*(e-1)+[str(p-1)],
                       'expected_suffix_slacks':[str(e-1-ell) for ell in range(e)]+['0']}}

raw['cases'].extend([normalized_closed_family(3,2,[5,7]),normalized_closed_family(3,3,[5,7])])
results = []
for fixture in raw['cases']:
    classes = fixture['classes']
    period = lcm(*(m for a, m in classes))
    if fixture['whole_cover']:
        demand(all(any((x-a) % m == 0 for a,m in classes) for x in range(period)), 'claimed full cover fails')
    else:
        demand(all((fixture['hole']-a) % m != 0 for a,m in classes), 'claimed hole fails')
    points = fixture['private_points']
    if points == 'all':
        points = [x for x in range(period) if sum((x-a) % m == 0 for a,m in classes) == 1]
    demand(all(any((x-a) % m == 0 and sum((x-aa) % mm == 0 for aa,mm in classes) == 1 for x in points) for a,m in classes), 'not every original has a checked private point')
    item = one_case(fixture['name'], classes, points, fixture['whole_cover'])
    item['class_count'] = len(classes)
    if fixture.get('closed_control'):
        palette = {m for a,m in classes}
        demand(len(palette) == len(classes) and all(m > 1 and m%2 for m in palette), 'distinct odd palette')
        demand(all(d in palette for m in palette for d in divisors(m) if d > 1), 'divisor closure')
        demand(all((a-b)%gcd(m,n) != 0 for i,(a,m) in enumerate(classes) for b,n in classes[i+1:] if m%n == 0 or n%m == 0), 'comparable original intersection')
        demand(all(a == 0 for a,m in classes if factors(m) == [m]), 'prime normalization')
        owners = [[i for i,(a,m) in enumerate(classes) if (x-a)%m == 0] for x in range(period)]
        private_counts = [sum(hits == [i] for hits in owners) for i in range(len(classes))]
        item['full_period'] = {'holes':sum(not hits for hits in owners), 'minimum_private_size':min(private_counts),
                              'divisor_closed':True,'comparable_originals_disjoint':True,'prime_classes_normalized':True}
        item['literal_originals_residue_modulus'] = classes
        item['checked_private_witnesses'] = points
        item['hole'] = fixture['hole']
        failed = fixture['failed_private_direction']
        fx,fp = failed['point'],failed['prime']
        demand([m for a,m in classes if (fx-a)%m == 0] == [fp], 'failed direction owner not the original prime')
        failed_sum = Fraction(0)
        for a,m in classes:
            h = valuation(m,fp) if m%fp == 0 else 0
            delta = a-fx
            if h and delta%(m//fp**h) == 0 and delta%m != 0:
                b = valuation(delta,fp)
                failed_sum += Fraction(1,fp**(h-b-1))
        demand(failed_sum == 0, 'other private direction was not zero')
        item['different_private_direction_failure'] = {'point':fx,'prime':fp,'lhs':str(failed_sum),'positive_demand':fp-1}
    if 'focused' in fixture:
        focus = fixture['focused']
        x, p = focus['point'], focus['prime']
        H = valuation(period,p)
        owner = next(m for a,m in classes if (x-a) % m == 0)
        e = valuation(owner,p)
        services = [Fraction(0) for b in range(H)]
        means = [[] for b in range(H)]
        for a,m in classes:
            h = valuation(m,p) if m % p == 0 else 0
            delta = a-x
            if h and delta % (m//p**h) == 0 and delta % m != 0:
                b = valuation(delta,p)
                services[b] += Fraction(1,p**(h-b-1))
        for k in range(p**H):
            y = (x + k*(period//p**H)) % period
            delta = (y-x) % p**H
            if delta:
                means[valuation(delta,p)].append(sum((y-a) % m == 0 for a,m in classes))
        slacks = [sum(services[ell:],Fraction(0))-max(e-ell,0)*(p-1) for ell in range(H+1)]
        demand(list(map(str,services)) == focus['expected_shell_services'], 'focused shell service differs')
        demand(list(map(str,slacks)) == focus['expected_suffix_slacks'], 'focused suffix slack differs')
        item['focused'] = {'point':x,'prime':p,'shell_services':list(map(str,services)),
             'shell_mean_multiplicities':[str(Fraction(sum(v),len(v))) for v in means],
             'suffix_slacks':list(map(str,slacks)), 'scope':'Only this original private point and this prime.'}
    results.append(item)
result = {'schema':'same-private-quotient-shell-controls-v1','result':'PASS', 'scope':raw['scope'],
          'totals':{key:sum(item[key] for item in results) for key in
                    ('private_points_checked','labelwise_quotient_equalities','aggregate_shell_equalities')},
          'cases':results}
Path(args.output).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
