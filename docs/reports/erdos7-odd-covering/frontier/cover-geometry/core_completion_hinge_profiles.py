#!/usr/bin/env python3
"""Exact mixed-height core-completion parameters; no full-period enumeration.

P3--P5 profiles, coupled same-law envelopes, and all switch intervals are
reconstructed using rational arithmetic. None means a full geometric sum,
not a large finite-height approximation. These are parameter certificates,
not actual covering systems or Lean-certified results.
"""
import argparse
import json
from fractions import Fraction as F
from itertools import combinations, product
from math import prod
from pathlib import Path

PRIMES = (5, 7, 11, 13)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def subsets(mask):
    current = mask
    while True:
        yield current
        if current == 0:
            return
        current = (current - 1) & mask


def exponent_cells(mask, coefficients, heights, domains=None):
    """Exact profile sums: bounded digits and certified infinite tails."""
    indices = tuple(i for i in range(4) if mask >> i & 1)
    choices, cutoffs, checks = [], {}, []
    for i in indices:
        if heights[i] is not None:
            choices.append(tuple(range(heights[i] + 1)))
            continue
        ratios = tuple(coefficients[t | 1 << i] / coefficients[t]
                       for t in subsets(mask ^ (1 << i)))
        cutoff = 0
        while PRIMES[i] ** (cutoff + 1) < max(ratios):
            cutoff += 1
        require(all(PRIMES[i] ** (cutoff + 1) >= r for r in ratios), 'tail dominance')
        cutoffs[i] = cutoff
        checks.append(dict(index=i, cutoff=cutoff, maximum_ratio=max(ratios)))
        choices.append(tuple(range(cutoff + 1)) + (None,))
    cells = []
    for exponents in product(*choices):
        tail = sum(1 << i for i, e in zip(indices, exponents) if e is None)
        bounded = sum(1 << i for i, e in zip(indices, exponents) if e is not None and e > 0)
        if not tail | bounded:
            continue
        coefficient = min(coefficients[tail | t] /
                          prod(PRIMES[i] ** e for i, e in zip(indices, exponents)
                               if e is not None and t >> i & 1)
                          for t in subsets(bounded))
        geometric = prod(F(1, PRIMES[i] ** cutoffs[i] * (PRIMES[i] - 1))
                         for i in cutoffs if tail >> i & 1)
        cell = dict(exponents=exponents, tail_support=tail,
                    coefficient=coefficient, geometric=geometric, cap=coefficient * geometric)
        if domains is not None:
            raw_coefficient = prod(1 / domains[i] for i in indices if (tail | bounded) >> i & 1)
            raw_coefficient /= prod(PRIMES[i] ** e for i, e in zip(indices, exponents)
                                    if e is not None and e > 0)
            cell.update(raw=raw_coefficient * geometric, switch=raw_coefficient / coefficient)
        cells.append(cell)
    return cells, checks


def profiles(heights, multiplicity):
    geometric = tuple(F(1, p - 1) if h is None else
                      sum((F(1, p ** e) for e in range(1, h + 1)), F())
                      for p, h in zip(PRIMES, heights))
    domains = tuple(1 - multiplicity * a for a in geometric)
    require(all(d > 0 for d in domains), 'positive pure domains')
    records = {0: dict(c={0: F(1)}, R=F(), f=F(1))}
    for size in range(1, 5):
        for indices in combinations(range(4), size):
            mask = sum(1 << i for i in indices)
            orders = []
            for i in indices:
                old = records[mask ^ (1 << i)]
                gap = 1 - multiplicity * old['R'] * geometric[i] / domains[i]
                if gap <= 0:
                    continue
                caps = {t: old['c'][t & ~(1 << i)] / gap /
                        (domains[i] if t >> i & 1 else 1)
                        for t in subsets(mask) if t}
                orders.append(dict(last=i, gap=gap, caps=caps, f=old['f'] * gap))
            require(bool(orders), 'positive last-coordinate order')
            c = {0: F(1)} | {t: min(row['caps'][t] for row in orders)
                             for t in subsets(mask) if t}
            cells, checks = exponent_cells(mask, c, heights)
            records[mask] = dict(c=c, R=sum((cell['cap'] for cell in cells), F()),
                                 f=max(row['f'] for row in orders), orders=orders,
                                 cells=cells, tail_dominance_checks=checks)
    return dict(geometric=geometric, domains=domains, records=records)


def analyze(heights):
    old, twice = profiles(heights, 1), profiles(heights, 2)
    head, second = old['records'][15], twice['records'][15]
    C = second['f'] * prod(d2 / d for d2, d in zip(twice['domains'], old['domains']))
    ratios = tuple(a / d for a, d in zip(old['geometric'], old['domains']))
    U = sum(ratios, F()) + 2 * sum((prod(xs) for xs in combinations(ratios, 3)), F())
    terms, checks = exponent_cells(15, head['c'], heights, old['domains'])
    points = {head['f'], F(1)}
    if head['f'] <= U + C <= 1:
        points.add(U + C)
    points.update(t['switch'] for t in terms if head['f'] <= t['switch'] <= 1)
    points = sorted(points)

    def evaluate(s):
        R = sum((min(t['cap'], t['raw'] / s) for t in terms), F())
        beta = min(U / s, 1 - C / s)
        require(0 <= beta <= 1 and 0 <= R < 2, 'envelope range')
        return dict(s=s, R=R, beta=beta, G=3 - 2 * R - beta)

    rows, pieces = [evaluate(s) for s in points], []
    for lo, hi in zip(points, points[1:]):
        mid = (lo + hi) / 2
        A = sum((t['cap'] for t in terms if t['cap'] <= t['raw'] / mid), F())
        B = sum((t['raw'] for t in terms if t['cap'] > t['raw'] / mid), F())
        beta0, beta1 = (F(1), -C) if mid < U + C else (F(), U)
        g0, g1 = 3 - 2 * A - beta0, -2 * B - beta1
        for s in (lo, mid, hi):
            row = evaluate(s)
            require(row['R'] == A + B / s and row['beta'] == beta0 + beta1 / s and
                    row['G'] == g0 + g1 / s, 'piecewise rational identities')
        pieces.append(dict(interval=(lo, hi), R_constant=A, R_reciprocal=B,
                           beta_constant=beta0, beta_reciprocal=beta1,
                           G_constant=g0, G_reciprocal=g1))
    return dict(heights=heights, old=old, twice=twice, C=C, U=U, terms=terms,
                tail_dominance_checks=checks, breakpoint_count=len(points),
                breakpoint_values=rows, pieces=pieces, worst=min(rows, key=lambda row: row['G']))


def crt(residues):
    modulus = 1
    for m, _ in residues:
        modulus *= m
    answer = sum(r*(modulus//m)*pow(modulus//m,-1,m) for m,r in residues)%modulus
    return modulus,answer


def actual_hinge_fixture(profile_R, profile_beta):
    primes=(5,7,11)
    Q,H=385,4
    divisors=(5,7,11,35,55,77,385)
    old_residues={5:0,7:0,11:0,35:1,55:2,77:3,385:4}
    originals=[]
    for a in divisors:
        originals.append(dict(modulus=a,residue=old_residues[a],e=0,a=a))
    for e in range(1,H+1):
        # Every e-layer uses one coherent child point; original ternary roots
        # vary with support rank, hence remain actual distinct original phases.
        child_tuple={5:e,7:e+1,11:e+2}
        for index,a in enumerate(divisors):
            support=tuple(p for p in primes if a%p==0)
            ternary_phase=(len(support)-1)+3*((e+index)%3**(e-1))
            modulus,residue=crt([(3**e,ternary_phase)]+[(p,child_tuple[p]) for p in support])
            require(modulus==3**e*a,'retain every original numerical label')
            originals.append(dict(modulus=modulus,residue=residue,e=e,a=a))
    require(len(originals)==35 and len({v['modulus'] for v in originals})==35,
            'one original residue per numerical modulus')
    require(all(v['a']>1 for v in originals),'pure ternary labels excluded from the core load')
    for left,right in combinations(originals,2):
        small,large=sorted((left,right),key=lambda v:v['modulus'])
        if large['modulus']%small['modulus']==0:
            require(large['residue']%small['modulus']!=small['residue'],
                    'comparable originals have disjoint actual congruence classes')
    old=[v for v in originals if v['e']==0]
    pure=[v for v in old if v['a'] in primes]
    pure_domain=[x for x in range(Q) if all(x%v['a']!=v['residue'] for v in pure)]
    survivors=[x for x in range(Q) if all(x%v['a']!=v['residue'] for v in old)]
    require(len(pure_domain)==240 and len(survivors)==219,'actual old pure and complete survivors')
    s=F(len(survivors),len(pure_domain))
    require(s==F(73,80),'actual same-law survival fraction')
    r=F(1,3**(H-1));T=(1-r)/2;target=(3+r)/2
    point_records=[]
    weighted_late=F(0)
    histogram={}
    for x in survivors:
        counts={e:sum(x%v['a']==v['residue']%v['a'] for v in originals if v['e']==e)
                for e in range(1,H+1)}
        g=counts[1]
        late=sum((F(1,3**(e-1))*counts[e] for e in range(2,H+1)),F(0))
        h=late/T
        ell=F(g)+late
        histogram[g]=histogram.get(g,0)+1
        point_records.append(dict(core=x,mass=F(1,len(survivors)),g=g,h=h,
                                  original_layer_counts=counts,completion_load=ell))
        weighted_late+=late/len(survivors)
    require(set(histogram)=={0,1,3,7},'actual first-layer load has zero, one, and multiple hits')
    require({v['residue']%3 for v in originals if v['e']==1}=={0,1,2},
            'first-layer originals retain multiple ternary roots')
    Eg=sum((F(v['g'],len(survivors)) for v in point_records),F(0))
    Eh=sum((v['h']/len(survivors) for v in point_records),F(0))
    beta=F(sum(v['g']>0 for v in point_records),len(survivors))
    p0=1-beta
    excess=sum((F(max(v['g']-2,0),len(survivors)) for v in point_records),F(0))
    hinge=sum((max(target-v['g'],F(0))/len(survivors) for v in point_records),F(0))
    require(excess>0,'fixture retains a substantive third-and-higher-hit contribution')
    require(hinge==(target-1)*(2-Eg)+(2-target)*p0+(target-1)*excess,
            'exact integer hinge under the actual common law')
    require(Eg<=profile_R and Eh<=profile_R and beta<=profile_beta,
            'the supplied profile, late, and union bounds hold for the same physical law')
    require(T*Eh==weighted_late,'normalized later-layer load uses exact ternary weights')
    G=3-2*profile_R-profile_beta
    for record in point_records:
        record['selection_cost'] = record['g'] + record['h'] + int(record['g'] > 0)
    selection_mean=sum((v['selection_cost']/len(survivors) for v in point_records),F(0))
    selected=min(point_records,key=lambda v:v['selection_cost'])
    require(selection_mean==Eg+Eh+beta<=3-G,'one common-law selection cost')
    require(selected['selection_cost']<=3-G<3 and selected['g'] in (0,1),
            'integer first layer at the one selected point')
    require(2*selected['completion_load']<=selected['selection_cost'],
            'same-point weighted completion comparison')
    require(selected['completion_load']<=F(3,2)-G/2,
            'ternary-height-independent selected-point margin')
    profile_gap=(target-1)*(2-profile_R)+(2-target)*(1-profile_beta)-T*profile_R
    require(profile_gap==(1-r)*G/2+r*(2-profile_R),'finite-H parameter scaling')
    require(G>0 and profile_gap>=G/2,'certified positive common-law hinge margin')
    actual_deficit=hinge-T*Eh
    minimum=min(v['completion_load'] for v in point_records)
    witness=next(v['core'] for v in point_records if v['completion_load']==minimum)
    require(minimum==F(1,27),'actual original completion minimum')
    require(profile_gap<=actual_deficit<=target-minimum,'hinge-to-point margin under one law')
    # Independent full-period original-congruence check of each cofactor load.
    # This uses literal original moduli and residues, including their ternary phases.
    ternary_period=3**H
    q_inverse=pow(Q,-1,ternary_period)
    actual_checks=0
    for record in point_records:
        x=record['core'];hit_total=0
        for z in range(ternary_period):
            integer=x+Q*((z-x)*q_inverse%ternary_period)
            require(integer%Q==x and integer%ternary_period==z,'full original CRT word')
            hit_total+=sum(integer%v['modulus']==v['residue'] for v in originals if v['e']>=1)
            actual_checks+=1
        require(F(3*hit_total,ternary_period)==record['completion_load'],
                'literal original ternary fibre average equals weighted cofactor load')
    return dict(scope='Exact actual-family bridge control; it does not enumerate all original phases or replace the mixed-height proof.',
                core_modulus=Q,ternary_height=H,original_labels=originals,
                original_label_count=len(originals),pure_ternary_labels_in_load=0,
                old_pure_domain_count=len(pure_domain),old_complete_survivor_count=len(survivors),
                uniform_old_survivor_law=point_records,s=s,first_layer_histogram=histogram,
                first_layer_ternary_roots=[0,1,2],Eg=Eg,Pr_g_positive=beta,Eh=Eh,
                actual_excess_over_two=excess,target=target,r=r,T=T,
                certified_profile_R=profile_R,certified_union_beta=profile_beta,G=G,
                selection_cost_mean=selection_mean,selected_core_point=selected['core'],
                selected_completion_load=selected['completion_load'],
                selected_margin_below_three_halves=F(3,2)-selected['completion_load'],
                exact_hinge_mean=hinge,weighted_late_mean=T*Eh,
                certified_hinge_margin=profile_gap,actual_hinge_deficit=actual_deficit,
                minimum_original_completion_load=minimum,actual_margin=target-minimum,
                minimizing_core_point=witness,full_original_CRT_word_checks=actual_checks)


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def compact_case(case):
    result = dict(case)
    for name in ('old', 'twice'):
        profile = case[name]
        records = {}
        for mask, record in profile['records'].items():
            row = {k: v for k, v in record.items() if k not in ('cells', 'orders')}
            if 'orders' in record:
                row['valid_orders'] = [{k: v for k, v in order.items() if k != 'caps'}
                                       for order in record['orders']]
            records[mask] = row
        result[name] = dict(geometric=profile['geometric'], domains=profile['domains'], records=records)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    cases = {
        'five_height_three': (3, None, None, None),
        'seven_height_two': (None, 2, None, None),
        'eleven_height_one': (None, None, 1, None),
        'thirteen_height_one': (None, None, None, 1),
        'minimal_failed_corner': (4, 3, 2, 2),
    }
    results = {name: analyze(heights) for name, heights in cases.items()}
    five = results['five_height_three']
    require(five['old']['records'][15]['R'] == F(40553, 37204), 'five-strip old envelope')
    require(five['twice']['records'][15]['R'] == F(10607, 3392), 'five-strip twice envelope')
    require(five['C'] == F(3392, 23265) and five['U'] == F(35789, 46530), 'five-strip same-law bounds')
    require(five['worst']['s'] == F(9301, 11515) and
            five['worst']['G'] == F(1765, 1841598) > F(1, 1050), 'five-strip all-height margin')
    require(results['seven_height_two']['worst']['G'] == F(420, 35761), 'seven-strip gap')
    require(results['eleven_height_one']['worst']['G'] == F(1986, 36575), 'eleven-strip gap')
    require(results['thirteen_height_one']['worst']['G'] == F(544, 17577), 'thirteen-strip gap')
    require(results['minimal_failed_corner']['worst']['s'] == F(82397006, 101984519) and
            results['minimal_failed_corner']['worst']['G'] == -F(10914212547, 30626143160140),
            'minimal excluded corner fails this envelope')
    positive_cases = ('five_height_three', 'seven_height_two', 'eleven_height_one', 'thirteen_height_one')
    require(all(results[name]['worst']['G'] > F(1, 1050) for name in positive_cases),
            'one common all-ternary-height core margin 1/2100')
    summary = {name: dict(heights=row['heights'], old_R=row['old']['records'][15]['R'],
                          twice_R=row['twice']['records'][15]['R'], C=row['C'], U=row['U'],
                          exponent_cell_count=len(row['terms']), breakpoint_count=row['breakpoint_count'],
                          worst=row['worst']) for name, row in results.items()}
    fixture_s = F(73, 80)
    fixture_R = sum((min(t['cap'], t['raw'] / fixture_s) for t in five['terms']), F())
    fixture_beta = min(five['U'] / fixture_s, 1 - five['C'] / fixture_s)
    actual = actual_hinge_fixture(fixture_R, fixture_beta)
    output = dict(actual_original_control=actual, scope='All original a>1 cofactors; finite arbitrary ternary H; exact mixed-height envelopes',
                  unit_cofactor='excluded', infinite_axes='exact geometric-tail cells',
                  negative_gap_meaning='This envelope does not certify positivity; no actual counterexample',
                  full_arithmetic_period_enumerated=False, summary=summary,
                  cases={name: compact_case(row) for name, row in results.items()})
    text = json.dumps(encode(output), indent=2) + '\n'
    if args.output is not None:
        args.output.write_text(text)
        print(json.dumps(encode(dict(profiles=summary, actual_original_control={
            k: v for k, v in actual.items() if k not in ('original_labels', 'uniform_old_survivor_law')})), indent=2))
    else:
        print(text, end='')


if __name__ == '__main__':
    main()
