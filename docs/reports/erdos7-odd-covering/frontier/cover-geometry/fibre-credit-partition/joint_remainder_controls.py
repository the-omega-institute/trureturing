"""Independent exact actual-family controls for joint grouped-survivor fees."""
import argparse
from fractions import Fraction as F
from itertools import combinations, product
from math import prod
from pathlib import Path
import json
import random

ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('--output', required=True)
args = ap.parse_args()
checks = 0


def need(ok, message):
    global checks
    checks += 1
    if not ok:
        raise ValueError(message)


def mul(values):
    return prod(values, start=F(1))


P, Q = (5,7), (11,13)
V = P+Q
SUPPORTS = [tuple(d) for k in range(2,len(V)+1) for d in combinations(V,k)]
GROUP_SUPPORTS = {(p,q) for p in P for q in Q}
REMAINDER = [d for d in SUPPORTS if d not in GROUP_SUPPORTS]
stats = {'squarefree_actual_families':0,'full_product_points':0,
         'individual_remaining_original_bounds':0,'weighted_comparisons':0,
         'supported_deep_head_controls':0,'strict_fee_improvements':0}


def actual_crt(phases, root):
    moduli = list(phases)
    if root is not None:
        moduli.append(3)
    modulus = prod(moduli)
    residue = 0
    for p in moduli:
        value = root if p == 3 else phases[p]
        part = modulus//p
        residue += value*part*pow(part,-1,p)
    return modulus,residue%modulus


def fees_for_support(d, rows, g, w, x, y):
    fixed = tuple(p for p in P if p in d)
    terms = {}
    for values in product(*(range(p) for p in fixed)):
        a = dict(zip(fixed,values))
        terms[values] = {}
        for r in (1,2):
            K = F(0)
            for i,j in product(range(5),range(7)):
                pair = {5:i,7:j}
                if any(pair[p] != a[p] for p in fixed):
                    continue
                term = mul(w[p][r][pair[p]] for p in P if p not in d)
                term *= mul(1-max(x[q][r][i],y[q][r][j]) for q in Q if q not in d)
                K += term
            terms[values][r] = mul(g[q][r] for q in Q if q not in d)*K
            old = mul(g[p][r] for p in V if p not in d)
            need(0 <= terms[values][r] <= old, 'JR9 each supported-address fee dominated by marginal fee')
    return fixed,terms


for seed in range(24):
    rng = random.Random(850000+seed)
    pure = {p:rng.randrange(p) for p in V}
    base = {p:set(range(p))-{pure[p]} for p in V}
    den = prod(len(base[p]) for p in V)
    c = {p:F(p,len(base[p])) for p in V}
    stars = {p:{1:set(),2:set()} for p in V}
    for p in V:
        stars[p][1+rng.randrange(2)].add(rng.randrange(p))
    keep = {p:{r:base[p]-stars[p][r] for r in (1,2)} for p in V}
    g = {p:{r:F(len(keep[p][r]),len(base[p])) for r in (1,2)} for p in V}
    w = {p:{r:[F(int(i in keep[p][r]),len(base[p])) for i in range(p)] for r in (1,2)}
         for p in P}
    groups, rest = [], []
    moduli = {3} | set(V) | {3*p for p in V}
    for d in SUPPORTS:
        for kind in ('free','selected'):
            root = None if kind == 'free' else 1+rng.randrange(2)
            phases = {p:rng.randrange(p) for p in d}
            modulus,residue = actual_crt(phases,root)
            need(modulus not in moduli and modulus > 1 and modulus % 2 == 1,
                 'Globally distinct odd nonunit numerical labels')
            moduli.add(modulus)
            need(all(residue % p == a for p,a in phases.items()) and
                 (root is None or residue % 3 == root), 'One globally fixed CRT phase')
            label = {'D':d,'kind':kind,'root':root,'phase':phases,
                     'modulus':modulus,'cap':mul(c[p]/p for p in d)}
            (groups if d in GROUP_SUPPORTS else rest).append(label)
    projections = {p:{q:{r:[set() for _ in range(p)] for r in (1,2)} for q in Q} for p in P}
    for m in groups:
        p = next(p for p in P if p in m['D'])
        q = next(q for q in Q if q in m['D'])
        for r in (1,2):
            if m['root'] is None or m['root']==r:
                projections[p][q][r][m['phase'][p]].add(m['phase'][q])
    probs = {p:{q:{r:[F(len(a & keep[q][r]),len(keep[q][r]))
                         for a in projections[p][q][r]] for r in (1,2)} for q in Q} for p in P}
    x,y = probs[5],probs[7]
    for q in Q:
        for r in (1,2):
            need(sum(x[q][r])+sum(y[q][r]) <= 1, 'Actual normalized raw-budget guard')
    exact_group, exact_survive = {1:0,2:0},{1:0,2:0}
    residual_hits = {m['modulus']:{1:0,2:0} for m in rest}
    for r in (1,2):
        active_group = [m for m in groups if m['root'] is None or m['root']==r]
        active_rest = [m for m in rest if m['root'] is None or m['root']==r]
        for point in product(*(sorted(base[p]) for p in V)):
            stats['full_product_points'] += 1
            assignment = dict(zip(V,point))
            if not all(assignment[p] in keep[p][r] for p in V):
                continue
            if any(all(assignment[p]==a for p,a in m['phase'].items()) for m in active_group):
                continue
            exact_group[r] += 1
            covered = False
            for m in active_rest:
                if all(assignment[p]==a for p,a in m['phase'].items()):
                    residual_hits[m['modulus']][r] += 1
                    covered = True
            if not covered:
                exact_survive[r] += 1
    lower = {}
    for r in (1,2):
        G = mul(g[q][r] for q in Q)
        lower[r] = G*sum(w[5][r][i]*w[7][r][j]*mul(1-x[q][r][i]-y[q][r][j] for q in Q)
                         for i,j in product(range(5),range(7)))
        exact_from_coordinates = G*sum(
            w[5][r][i]*w[7][r][j]*mul(
                F(len(keep[q][r]-(projections[5][q][r][i]|projections[7][q][r][j])),len(keep[q][r]))
                for q in Q) for i,j in product(range(5),range(7)))
        need(exact_from_coordinates == F(exact_group[r],den), 'Independent full-product group residual')
        need(lower[r] <= F(exact_group[r],den), 'JR7 guarded group survivor lower bound')
    fee_tables = {d:fees_for_support(d,None,g,w,x,y) for d in REMAINDER}
    for m in rest:
        fixed,table = fee_tables[m['D']]
        address = tuple(m['phase'][p] for p in fixed)
        for r in (1,2):
            if m['root'] is None or m['root']==r:
                need(F(residual_hits[m['modulus']][r],den) <= m['cap']*table[address][r],
                     'JR3 actual remainder/group-complement intersection versus fixed-address fee')
                stats['individual_remaining_original_bounds'] += 1
    for gamma1 in (F(0),F(1,3),F(1,2),F(1)):
        gamma = {1:gamma1,2:1-gamma1}
        fee,new_direct,old_fee = F(0),F(0),F(0)
        for d in REMAINDER:
            _,table = fee_tables[d]
            A = max(sum(gamma[r]*v[r] for r in (1,2)) for v in table.values())
            B = max(gamma[r]*v[r] for v in table.values() for r in (1,2))
            R = mul(c[p]/p for p in d)
            fee += R*(A+B)
            old_A = sum(gamma[r]*mul(g[p][r] for p in V if p not in d) for r in (1,2))
            old_B = max(gamma[r]*mul(g[p][r] for p in V if p not in d) for r in (1,2))
            need(A <= old_A and B <= old_B, 'Same-address and selected-once fee comparisons')
            old_fee += R*(old_A+old_B)
        for m in rest:
            fixed,table = fee_tables[m['D']]
            address = tuple(m['phase'][p] for p in fixed)
            if m['root'] is None:
                actual = sum(gamma[r]*F(residual_hits[m['modulus']][r],den) for r in (1,2))
                direct = m['cap']*sum(gamma[r]*table[address][r] for r in (1,2))
            else:
                r = m['root']
                actual = gamma[r]*F(residual_hits[m['modulus']][r],den)
                direct = m['cap']*gamma[r]*table[address][r]
            need(actual <= direct, 'Free original uses same actual address; selected original one root')
            new_direct += direct
        need(new_direct <= fee <= old_fee, 'Uniform support fee dominates actual address fees')
        combined = sum(gamma[r]*lower[r] for r in (1,2))-fee
        actual_survival = sum(gamma[r]*F(exact_survive[r],den) for r in (1,2))
        need(combined <= actual_survival, 'JR8 full actual-family survivor bound')
        need(combined >= sum(gamma[r]*lower[r] for r in (1,2))-old_fee,
             'New comparison dominates old comparison for same array')
        stats['strict_fee_improvements'] += int(fee < old_fee)
        stats['weighted_comparisons'] += 1
    stats['squarefree_actual_families'] += 1

# Deeper head originals: exact coordinate sets at the original depth.
for seed in range(24):
    rng = random.Random(855000+seed)
    universes = {p:set(range(p*p)) for p in V}
    def cyl(p,e,a):
        return {t for t in universes[p] if t % p**e == a}
    base = {p:universes[p]-cyl(p,1,rng.randrange(p))-cyl(p,2,rng.randrange(p*p)) for p in V}
    stars = {p:{r:set() for r in (1,2)} for p in V}
    for p in V:
        for e in (1,2):
            stars[p][1+rng.randrange(2)] |= cyl(p,e,rng.randrange(p**e))
    keep = {p:{r:base[p]-stars[p][r] for r in (1,2)} for p in V}
    c = {p:F(p*p,len(base[p])) for p in V}
    g = {p:{r:F(len(keep[p][r]),len(base[p])) for r in (1,2)} for p in V}
    w = {p:{r:[F(len(cyl(p,1,i)&keep[p][r]),len(base[p])) for i in range(p)] for r in (1,2)} for p in P}
    sets = {p:{q:{r:[set() for _ in range(p)] for r in (1,2)} for q in Q} for p in P}
    for p,q,e in product(P,Q,(1,2)):
        row,phase = rng.randrange(p),rng.randrange(q**e)
        for r in (1,2):
            sets[p][q][r][row] |= cyl(q,e,phase)
        row,phase,root = rng.randrange(p),rng.randrange(q**e),1+rng.randrange(2)
        sets[p][q][root][row] |= cyl(q,e,phase)
    x = {q:{r:[F(len(a&keep[q][r]),len(keep[q][r])) for a in sets[5][q][r]] for r in (1,2)} for q in Q}
    y = {q:{r:[F(len(a&keep[q][r]),len(keep[q][r])) for a in sets[7][q][r]] for r in (1,2)} for q in Q}
    for d,exponents in (((5,11),{5:2,11:1}),((7,13),{7:2,13:2}),
                         ((5,7),{5:2,7:2}),((5,11,13),{5:2,11:1,13:2})):
        phases = {p:rng.randrange(p**exponents[p]) for p in d}
        original = {p:cyl(p,exponents[p],phases[p]) for p in d}
        cap = mul(c[p]/p**exponents[p] for p in d)
        fixed,table = fees_for_support(d,None,g,w,x,y)
        address = tuple(phases[p]%p for p in fixed)
        for r in (1,2):
            exact = F(0)
            for i,j in product(range(5),range(7)):
                headrow = {5:i,7:j}
                term = F(1)
                for p in P:
                    a = cyl(p,1,headrow[p])&keep[p][r]
                    if p in d:
                        a &= original[p]
                    term *= F(len(a),len(base[p]))
                for q in Q:
                    a = keep[q][r]-(sets[5][q][r][i]|sets[7][q][r][j])
                    if q in d:
                        a &= original[q]
                    term *= F(len(a),len(base[q]))
                exact += term
            need(exact <= cap*table[address][r], 'Deep original retains original head-depth cap, no extra head weight')
            stats['supported_deep_head_controls'] += 1

# Literal finite-inventory check of the support coefficients, including {5,7}.
c = {p:F(p-1,p-2) for p in V}
a = {p:c[p]/p for p in P}
b = {p:c[p]*(F(1,p)+F(1,p*p)) for p in V}
for d in SUPPORTS:
    literal = F(0)
    for exponents in product((1,2),repeat=len(d)):
        exp = dict(zip(d,exponents))
        grouped = len(d)==2 and any(p in d and q in d and exp[p]==1 for p in P for q in Q)
        if not grouped:
            literal += mul(c[p]/p**exp[p] for p in d)
    if d in GROUP_SUPPORTS:
        p = next(p for p in P if p in d)
        q = next(q for q in Q if q in d)
        formula = (b[p]-a[p])*b[q]
    else:
        formula = mul(b[p] for p in d)
    need(literal == formula, 'JR6 exact nongroup original inventory coefficient')

# A finite literal deep-private family exposing every raw head row.
# Pure coordinates are 0 mod p; free 5*11^e (1<=e<=5) and 7*11^e
# (1<=e<=7) use head row e-1 and private cylinder 1 mod 11^e.
# The nested-cylinder masses are computed exactly, without expanding 11^7.
g = {p:{r:F(1) for r in (1,2)} for p in V}
w = {p:{r:[F(int(i!=0),p-1) for i in range(p)] for r in (1,2)} for p in P}
x = {q:{r:[F(11,10)/11**(i+1) if q==11 else F(0) for i in range(5)]
         for r in (1,2)} for q in Q}
y = {q:{r:[F(11,10)/11**(j+1) if q==11 else F(0) for j in range(7)]
         for r in (1,2)} for q in Q}
need(sum(x[11][1])+sum(y[11][1]) < 1, 'Literal deep-private family raw guard')
_,table = fees_for_support((5,7),None,g,w,x,y)
new = max(v[1] for v in table.values())
need(new == 1-F(11,10)/11**5 < 1, 'Strict joint-fee gain for finite exact deep-private family')
for i,j in product(range(5),range(7)):
    exact = w[5][1][i]*w[7][1][j]*(1-max(x[11][1][i],y[11][1][j]))
    need(exact <= F(1,24)*table[i,j][1], 'Literal remaining35 exact nested-cylinder intersection bound')
stats['strict_fee_improvements'] += 1

# An exact actual depth-two counterexample to multiplying a supported head's
# original-depth cap by its first-row weight a second time.
pure5_survivors = {t for t in range(25) if t % 5 != 0}
pure11_survivors = set(range(1,11))
head_cylinder_mass = F(len({1} & pure5_survivors),len(pure5_survivors))
private_cylinder_mass = F(len({1} & pure11_survivors),len(pure11_survivors))
actual_275 = head_cylinder_mass*private_cylinder_mass
first_row_mass = F(len({t for t in pure5_survivors if t % 5 == 1}),len(pure5_survivors))
correct_275_cap = F(5,4)/25 * (F(11,10)/11)
need(actual_275 == correct_275_cap == F(1,200), 'Actual 275 original attains depth-two head cap')
need(first_row_mass == F(1,4) and correct_275_cap*first_row_mass == F(1,800) < actual_275,
     'Counterexample: cap times supported-head row weight is a false upper bound')

need(stats['strict_fee_improvements'] > 0, 'Actual controls exercise nontrivial joint-fee improvement')
result = {
    'contract':'Exact finite actual-family controls for JR1-JR9; ordinary proof, no Lean or uniform positivity claim.',
    'checks':checks,'statistics':stats,
    'supported_head_double_payment_counterexample':{
        'original_modulus':275,'head_depth':2,'actual_residual_mass':'1/200',
        'correct_original_depth_cap':'1/200','first_head_row_mass':'1/4',
        'incorrect_cap_times_row_weight':'1/800',
        'source':'Delete 0 mod5 and 0 mod11; no stars or groups. Other source coordinates integrate to one.',
    },
    'limits':[
        'The row probabilities in every fee are actual common-source projection masses, not independent upper budgets.',
        'Positive values for selected arrays do not prove a uniform bound over arbitrary actual families.',
        'No old checker, optimizer or Lean build was run.',
    ],
}
Path(args.output).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'checks':checks,'statistics':stats,'output':args.output}))
