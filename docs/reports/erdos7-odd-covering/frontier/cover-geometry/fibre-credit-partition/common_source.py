"""Exact finite controls for a shared-source two-root scalar boundary.

Only explicitly supplied input/output paths are accessed. No old checker runs.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import permutations, product
from math import prod
from pathlib import Path
import json
import random

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--witness', required=True)
parser.add_argument('--output', required=True)
args = parser.parse_args()
witness_bytes = Path(args.witness).read_bytes()
witness = json.loads(witness_bytes)
checks = 0


def need(condition, message):
    global checks
    checks += 1
    if not condition:
        raise ValueError(message)


def cylinder(p, depth, phase):
    return {x for x in range(p * p) if x % (p ** depth) == phase}


def mass(a, support):
    return F(len(a & support), len(support))


fixture_stats = {
    'actual_phase_families': 0,
    'rows_with_free_selected_overlap': 0,
    'coordinates_with_cross_root_star_overlap': 0,
    'unblocked_root1_private_comparisons': 0,
    'grouped_union_bounds': 0,
    'head_first_row_tail_checks': 0,
}
HEADS = (5, 7)
PRIVATE = (11, 13)
ATOMS = tuple(product((0, 1), repeat=2))

for seed in range(48):
    rng = random.Random(830000 + seed)
    laws, stars, caps, atom_sets, atom_mass, g, weights = {}, {}, {}, {}, {}, {}, {}
    first_star = {}
    for p in HEADS + PRIVATE:
        pure = cylinder(p, 1, rng.randrange(p)) | cylinder(p, 2, rng.randrange(p*p))
        laws[p] = set(range(p*p)) - pure
        caps[p] = F(p*p, len(laws[p]))
        stars[p] = {1: set(), 2: set()}
        phases = [rng.randrange(p), rng.randrange(p*p)]
        if seed % 5 == 0:
            phases[1] = phases[0]
        first_star[p] = None
        for e, phase in enumerate(phases, 1):
            if e == 1 and seed % 7 == 0:
                continue
            root = 2 if p in PRIVATE and seed % 3 == 0 else 1 + rng.randrange(2)
            stars[p][root] |= cylinder(p, e, phase)
            if e == 1:
                first_star[p] = (root,phase)
        atom_sets[p] = {
            ab: {x for x in laws[p]
                 if (int(x in stars[p][1]), int(x in stars[p][2])) == ab}
            for ab in ATOMS
        }
        atom_mass[p] = {ab: mass(a, laws[p]) for ab, a in atom_sets[p].items()}
        need(sum(atom_mass[p].values()) == 1, 'Common four-star atom partition')
        g[p] = {r: 1 - mass(stars[p][r], laws[p]) for r in (1, 2)}
        need(all(g[p][r] > 0 for r in (1, 2)), 'Actual positive carriers')
        need(sum(1-g[p][r] for r in (1, 2)) <= caps[p]*(F(1,p)+F(1,p*p)),
             'Actual height-one shared star inventory')
        if stars[p][1] & stars[p][2] & laws[p]:
            fixture_stats['coordinates_with_cross_root_star_overlap'] += 1
        if p in HEADS:
            h = {i: {ab: mass(cylinder(p,1,i) & atom_sets[p][ab],laws[p])
                     for ab in ATOMS} for i in range(p)}
            weights[p] = {r: [sum(h[i][ab] for ab in ATOMS if ab[r-1] == 0)
                              for i in range(p)] for r in (1,2)}
            for i in range(p):
                ell = sum(h[i].values())
                mu1 = h[i][(1,0)] + h[i][(1,1)]
                mu2 = h[i][(0,1)] + h[i][(1,1)]
                need(0 <= ell <= caps[p]/p, 'Shared physical head row cap')
                need(max(0,mu1+mu2-ell) <= h[i][(1,1)] <= min(mu1,mu2),
                     'Head overlap Frechet bounds')
                for r in (1,2):
                    need(weights[p][r][i] == mass(cylinder(p,1,i)-stars[p][r],laws[p]),
                         'Common head atom reconstruction')
            for r in (1,2):
                need(sum(weights[p][r]) == g[p][r], 'Head carrier mass')
            deletion = {(r,i): mass(cylinder(p,1,i)&stars[p][r],laws[p])
                        for r in (1,2) for i in range(p)}
            first = first_star[p]
            if first is not None:
                need(deletion[first] == mass(cylinder(p,1,first[1]),laws[p]),
                     'Actual first star deletes its whole physical row')
            need(sum(value for cell,value in deletion.items() if cell != first)
                 <= caps[p]/p**2, 'CS11 shared deep-star tail cap outside first cell')
            fixture_stats['head_first_row_tail_checks'] += 1

    free, selected, selected_budget, raw_budget, x = {}, {}, {}, {}, {}
    for p in HEADS:
        for q in PRIVATE:
            free[p,q] = [set() for _ in range(p)]
            selected[p,q] = {r: [set() for _ in range(p)] for r in (1,2)}
            selected_budget[p,q] = {1:F(0), 2:F(0)}
            B = caps[q]*(F(1,q)+F(1,q*q))
            for e in (1,2):
                row, phase = rng.randrange(p), rng.randrange(q**e)
                free[p,q][row] |= cylinder(q,e,phase)
                sr, sp = rng.randrange(p), rng.randrange(q**e)
                if (seed + e + p) % 4 == 0:
                    sr,sp = row,phase
                root = 1 + rng.randrange(2)
                selected[p,q][root][sr] |= cylinder(q,e,sp)
                selected_budget[p,q][root] += caps[q]/q**e
            need(sum(selected_budget[p,q].values()) == B,
                 'Each numerical selected label assigned only once')
            need(sum(mass(a,laws[q]) for a in free[p,q]) <= B,
                 'Shared free original-label cap budget')
            x[p,q] = {r: [] for r in (1,2)}
            increment_totals = {1:F(0),2:F(0)}
            for i in range(p):
                fi = free[p,q][i]
                fs = {ab: mass(fi & atom_sets[q][ab],laws[q]) for ab in ATOMS}
                increments = {r: selected[p,q][r][i]-fi for r in (1,2)}
                ss = {r: {ab: mass(increments[r] & atom_sets[q][ab],laws[q])
                          for ab in ATOMS} for r in (1,2)}
                for r in (1,2):
                    increment_totals[r] += sum(ss[r].values())
                    if selected[p,q][r][i] & fi & laws[q]:
                        fixture_stats['rows_with_free_selected_overlap'] += 1
                    for ab in ATOMS:
                        need(0 <= fs[ab] and 0 <= ss[r][ab] and
                             fs[ab]+ss[r][ab] <= atom_mass[q][ab],
                             'CS3 disjoint free-selected increment within shared atom')
                    value = sum(fs[ab]+ss[r][ab] for ab in ATOMS if ab[r-1] == 0)/g[q][r]
                    actual = mass((fi | selected[p,q][r][i])-stars[q][r],laws[q])/g[q][r]
                    need(value == actual, 'CS5 raw projection reconstruction')
                    x[p,q][r].append(value)
                    z = mass(fi-stars[q][r],laws[q])
                    f = mass(fi,laws[q])
                    t = mass(increments[r]-stars[q][r],laws[q])
                    need(0 <= z <= min(f,g[q][r]) and 0 <= f-z <= 1-g[q][r],
                         'CS6 common-free restriction')
                    need(0 <= t <= g[q][r]-z and g[q][r]*value == z+t,
                         'CS6 selected increment and survivor decomposition')
                t2 = mass(increments[2]-stars[q][2],laws[q])
                need(max(F(0),g[q][2]*x[p,q][2][i]-g[q][1]*x[p,q][1][i])
                     <= t2+fs[(1,0)], 'CS8 both-root conditioning')
            for r in (1,2):
                need(increment_totals[r] <= selected_budget[p,q][r], 'CS4 selected cap')
                raw_budget[p,q,r] = (B+selected_budget[p,q][r])/g[q][r]
                need(sum(x[p,q][r]) <= raw_budget[p,q,r], 'Correct private-normalized raw budget')
            if g[q][1] == 1:
                lhs = sum(max(F(0),g[q][2]*b-a) for a,b in zip(x[p,q][1],x[p,q][2]))
                need(lhs <= selected_budget[p,q][2], 'CS7 shared physical row positive-part bound')
                fixture_stats['unblocked_root1_private_comparisons'] += 1

    for r in (1,2):
        G = prod((g[q][r] for q in PRIVATE), start=F(1))
        actual, upper = F(0), F(0)
        for q in PRIVATE:
            need(sum(raw_budget[p,q,r] for p in HEADS) <= 1, 'CS9 guarded paired budgets')
        for i,j in product(range(5),range(7)):
            exact_residual, relaxed_residual = F(1), F(1)
            for q in PRIVATE:
                a = free[5,q][i] | selected[5,q][r][i]
                b = free[7,q][j] | selected[7,q][r][j]
                kept = laws[q]-stars[q][r]
                exact_residual *= F(len(kept-(a|b)),len(kept))
                relaxed_residual *= 1-x[5,q][r][i]-x[7,q][r][j]
            w = G*weights[5][r][i]*weights[7][r][j]
            actual += w*(1-exact_residual)
            upper += w*(1-relaxed_residual)
        need(0 <= actual <= upper <= G*g[5][r]*g[7][r],
             'CS10 actual coordinate-set grouped union bounded by common-source scalar expression')
        fixture_stats['grouped_union_bounds'] += 1
    fixture_stats['actual_phase_families'] += 1

# Independent small whole-product enumeration checks the grouped mass formula.
whole_product_models = 24
for seed in range(whole_product_models):
    rng = random.Random(835000+seed)
    spaces = (range(3),range(2),range(4),range(5))
    blockers = [{v for v in axis if rng.randrange(4)==0} for axis in spaces]
    # Always leave at least one point so each conditioning law is defined.
    for axis,b in zip(spaces,blockers):
        b.discard(axis[0])
    F5 = [[{v for v in spaces[q+2] if rng.randrange(4)==0} for _ in spaces[0]]
          for q in range(2)]
    F7 = [[{v for v in spaces[q+2] if rng.randrange(4)==0} for _ in spaces[1]]
          for q in range(2)]
    surviving = [set(axis)-b for axis,b in zip(spaces,blockers)]
    hits = 0
    for i,j,u,v in product(*spaces):
        if not all(z in keep for z,keep in zip((i,j,u,v),surviving)):
            continue
        if any(z in F5[q][i] or z in F7[q][j] for q,z in enumerate((u,v))):
            hits += 1
    direct = F(hits,prod(len(a) for a in spaces))
    predicted = F(0)
    G = prod((F(len(surviving[q+2]),len(spaces[q+2])) for q in range(2)),start=F(1))
    for i,j in product(surviving[0],surviving[1]):
        residual = prod((F(len(surviving[q+2]-(F5[q][i]|F7[q][j])),len(surviving[q+2]))
                         for q in range(2)),start=F(1))
        predicted += G*F(1,len(spaces[0])*len(spaces[1]))*(1-residual)
    need(direct == predicted, 'Independent whole-product versus grouped formula')

# Literal arithmetic overlap counterexamples.
support11 = set(range(121))-cylinder(11,1,0)
B11 = cylinder(11,1,1)
losses = [mass(B11,support11),mass(cylinder(11,2,1),support11)]
need(sum(losses) == F(6,55) > mass(B11,support11) == F(1,10),
     'Actual overlapping free rows defeat aggregate deletion budget')
support5 = set(range(25))-cylinder(5,1,0)
head_losses = [mass(cylinder(5,1,1),support5),mass(cylinder(5,2,1),support5)]
need(sum(head_losses) == F(3,10) > mass(cylinder(5,1,1),support5) == F(1,4),
     'Actual cross-root stars can overlap in one physical head row')
Fset = cylinder(11,1,1)
need(mass(Fset|Fset,support11) == F(1,10) < 2*mass(Fset,support11),
     'Selected-free union cannot be replaced by an uncorrected sum')

# All common row matchings reject the old scalar witness; no old optimization.
old = witness['witnesses']
permutation_count = 0
for perm in permutations(range(5)):
    valid = True
    for q in (11,13):
        x1 = list(map(F,old['1']['q_arrays'][str(q)]['x']))
        original2 = list(map(F,old['2']['q_arrays'][str(q)]['x']))
        x2 = [F(0)]*5
        for i,a in enumerate(original2):
            x2[perm[i]] = a
        private_survival = F(q-3,q-2)
        budget = F(1,9) if q == 11 else F(0)
        lhs = sum(max(F(0),private_survival*b-a) for a,b in zip(x1,x2))
        valid = valid and lhs <= budget
    need(not valid, 'No single physical row permutation repairs q11 and q13')
    permutation_count += 1

# The new head weights are admissible measurable padding, not actual full stars.
ell = [F(4,15),F(4,15),F(4,15),F(1,5),F(0)]
mu = [F(0),F(0),F(2,15),F(1,5),F(0)]
deep_cap = F(4,3)*F(1,20)
full_row_max = max((l for l,m in zip(ell,mu) if l == m),default=F(0))
need(sum(ell)==1 and all(0<=m<=l for l,m in zip(ell,mu)), 'Measurable shared head padding feasible')
need(deep_cap==F(1,15) and full_row_max+deep_cap==F(4,15)<sum(mu)==F(1,3),
     'One actual first-depth star plus deep inventory cannot realize full padded deletion')

need(5041 % 5040 == 1 % 5040 and 5041 % 11 == 3 and 1 % 11 == 1,
     'Affine-gcd quotient does not preserve legal mod11 covering readout')
need(fixture_stats['rows_with_free_selected_overlap']>0 and
     fixture_stats['coordinates_with_cross_root_star_overlap']>0,
     'Actual fixtures exercise the overlap cases')

result = {
    'contract':'Common-source necessary scalar boundary; ordinary proof and finite exact controls, no Lean or unrestricted positivity claim.',
    'checks': checks,
    'witness_sha256':sha256(witness_bytes).hexdigest(),
    'actual_phase_fixture_statistics':fixture_stats,
    'independent_whole_product_models':whole_product_models,
    'rejected_common_head_permutations':permutation_count,
    'literal_overlap_controls':{
        'shared_private_blocker_mass':'1/10','sum_overlapping_free_losses':'6/55',
        'shared_head_row_mass':'1/4','sum_cross_root_star_deletions':'3/10',
    },
    'actual_star_padding_boundary':{
        'padded_mass':'1/3','maximum_compatible_actual_star_mass':'4/15',
        'deep_star_allowance':'1/15',
        'warning':'An arbitrary measurable enlargement remains allowed by the older padding contract; this does not justify silently imposing actual-star constraints at fixed padded masses.',
    },
    'limits':[
        'The actual-family map is proved for the declared original inventory and arbitrary globally fixed phases.',
        'Scalar feasibility has an abstract common-probability-source realization, not necessarily an arithmetic cylinder realization.',
        'Excluding the old witness does not prove positivity; stronger interfaces and joint remaining-charge constraints remain open.',
        'No old checker, fixed-scalar optimizer or Lean build was run.',
    ],
}
Path(args.output).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'checks':checks,'actual_families':fixture_stats['actual_phase_families'],
                  'rejected_permutations':permutation_count,'output':args.output}))
