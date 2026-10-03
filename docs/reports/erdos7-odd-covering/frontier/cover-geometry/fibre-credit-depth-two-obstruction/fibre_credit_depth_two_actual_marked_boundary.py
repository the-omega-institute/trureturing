#!/usr/bin/env python3
"""An actual marked-cylinder boundary and a positive full-core-height continuation."""
from fractions import Fraction as F
from itertools import combinations
from math import prod
from pathlib import Path
from hashlib import sha256
import argparse,json

def need(ok,message):
    if not ok:raise RuntimeError(message)

def actual_source(partial,core):
    P=(11,13,17,19,23)
    nonzero=max(1-F(r['probabilities'][0]) for r in partial['profiles'])
    need(nonzero==F(10,27),'largest partial nonzero probability')
    critical=[]
    for full in ((),(23,),(19,23)):
        mult=prod((1+F(1,p-2 if p in full else p-1) for p in P),start=F(1))
        R=F(core['deletion_upper'])*mult
        need(nonzero<R<1,'critical mass above every partial nonzero mass')
        critical.append({'full_outside_axes':list(full),'critical_retention':str(R),'critical_retention_decimal':float(R)})

    base=[(3,0),(9,4),(5,0),(15,1),(45,37),(7,0)]+[(m,0) for m in (21,35,63,105,315)]
    points=[x for x in range(315) if all(x%m!=a for m,a in base)]
    need(len(points)==102,'actual first-shape pruned315 law')
    D=[d for d in range(2,316) if 315%d==0]
    originals=base+[(p,0) for p in P]
    for p in P:
        for j,d in enumerate(D):
            root=j%(p-1)+1
            a=2+d*((root-2)*pow(d,-1,p)%p)
            need(0<=a<p*d and a%d==2%d and a%p==root,'fixed original CRT phase')
            originals.append((p*d,a))
    need(len(originals)==len({m for m,a in originals})==71,'all numerical moduli distinct')
    need(all(m>1 and m%2 for m,a in originals),'nonunit odd moduli')

    rows=[]
    for x in points:
        livecounts=[]
        for p in P:
            removed={j%(p-1)+1 for j,d in enumerate(D) if x%d==2%d}
            # Independent literal test of the CRT phases in that coarse row.
            allowed=[]
            for r in range(1,p):
                valid=True
                for m,a in originals:
                    if m%p!=0 or m==p:continue
                    d=m//p
                    if x%d==a%d and r==a%p:
                        valid=False;break
                if valid:allowed.append(r)
            need(len(allowed)==p-1-len(removed),'literal cylinder incidence agrees with union of roots')
            livecounts.append(len(allowed))
        count=prod(livecounts)
        rows.append({'x':x,'outside_live_counts':livecounts,'outside_survivor_count':count})
    raw_count=len(points)*prod(p-1 for p in P)
    survivors=sum(r['outside_survivor_count'] for r in rows)
    rho=F(survivors,raw_count)
    need(rho==F(135151,228096),'exact actual restriction mass')
    need(rho<F(critical[0]['critical_retention']),'retention-only sufficient target fails on actual family')
    need(survivors>0,'not an odd cover')
    core_weights={r['x']:F(r['outside_survivor_count'],survivors) for r in rows}
    marked=[]
    for profile in partial['profiles']:
        S=profile['S']
        chosen=[d for d in D if (3 not in S or d%9==0) and (5 not in S or d%5==0) and (7 not in S or d%7==0)]
        rawmean=sum(F(sum(x%d==2%d for d in chosen),len(points)) for x in points)
        conditioned=sum((core_weights[x]*sum(x%d==2%d for d in chosen) for x in points),F(0))
        # Maxima here are only OLD315 marked queries, not all outside-bearing queries.
        uniform_max=sum(max(sum((core_weights[x] for x in points if x%d==a),F(0)) for a in range(d)) for d in chosen)
        marked.append({'S':S,'old315_query_slots':chosen,'phase2_raw_mean':str(rawmean),'phase2_conditional_mean':str(conditioned),
                       'all_phase_old315_conditional_mean_max':str(uniform_max)})
    carrier=315*prod(P)
    out={'scope':'Actual71-class family, first canonical old45 shape, no repeated numerical moduli, global fixed CRT phases. Tests fixed-profile retention-only repair; not an odd covering or a bound on all possible sources.',
         'critical_mass_for_fixed_partial_profiles':critical,'max_partial_nonzero_probability':str(nonzero),
         'originals':[{'modulus':m,'residue':a} for m,a in originals],
         'coarse_survivor_count':len(points),'raw_source_atom_count':raw_count,'actual_survivor_count':survivors,
         'actual_retention':str(rho),'actual_retention_decimal':float(rho),'Haar_survivor_density':str(F(survivors,carrier)),
         'rows':rows,'marked_old_query_readings':marked}
    return out

def marked_queries(source):
    primes = (11, 13, 17, 19, 23)
    divisors = (1, 3, 5, 7, 9, 15, 21, 35, 45, 63, 105, 315)
    points = [row['x'] for row in source['rows']]
    originals = source['originals']
    total = source['actual_survivor_count']
    allowed = {}
    for x in points:
        allowed[x] = {}
        for p in primes:
            relevant = [a for a in originals if a['modulus'] % p == 0 and a['modulus'] != p]
            allowed[x][p] = tuple(r for r in range(1, p) if all(
                not (x % (a['modulus'] // p) == a['residue'] % (a['modulus'] // p)
                     and r == a['residue'] % p) for a in relevant))
    need(sum(prod(len(allowed[x][p]) for p in primes) for x in points) == total,
         'literal common source denominator')
    for p in primes[1:]:
        need(all(12 in allowed[x][p] for x in points), 'one universal query root')

    # A second algorithm below retains every possible intersection of root masks.
    # It does not invoke the universal-root optimization.
    full = (1 << len(points)) - 1
    root_masks = {p: {sum((r in allowed[x][p]) << i for i, x in enumerate(points))
                      for r in range(1, p)} for p in primes}
    intersection_sets = {}
    for mask in range(32):
        selected = tuple(p for i, p in enumerate(primes) if mask >> i & 1)
        intersections = {full}
        for p in selected:
            intersections = {left & right for left in intersections for right in root_masks[p]}
        intersection_sets[selected] = intersections

    maxima = []
    means = {}
    for d in divisors:
        old_masks = [sum((x % d == a) << i for i, x in enumerate(points)) for a in range(d)]
        for selected, intersections in intersection_sets.items():
            weights = [prod(len(allowed[x][p]) for p in primes if p not in selected) for x in points]
            roots = range(1, 11) if 11 in selected else (None,)
            direct = max((sum(w for x, w in zip(points, weights) if x % d == a
                              and (r is None or r in allowed[x][11])), a, r or 0)
                         for a in range(d) for r in roots)
            candidates = {a & b for a in old_masks for b in intersections}
            independent = max(sum(w for i, w in enumerate(weights) if support >> i & 1)
                              for support in candidates)
            need(direct[0] == independent, 'all root-phase intersections agree')
            means[d, selected] = F(independent, total)
            maxima.append({'core_divisor': d, 'outside_primes': list(selected),
                           'max_numerator': independent, 'old_phase': direct[1],
                           'root11': direct[2], 'root_intersection_count': len(intersections)})

    partials = []
    for size in range(1, 4):
        for selected_core in combinations((3, 5, 7), size):
            selected_divisors = [d for d in divisors if (3 not in selected_core or d % 9 == 0)
                                 and (5 not in selected_core or d % 5 == 0)
                                 and (7 not in selected_core or d % 7 == 0)]
            value = sum((v for (d, selected), v in means.items() if d in selected_divisors), F(0))
            partials.append({'S': list(selected_core), 'full_outside_partial_mean': str(value),
                             'decimal': float(value)})
    debit = sum((F(row['full_outside_partial_mean']) / prod(p - 1 for p in row['S'])
                 for row in partials), F(0))
    need(debit == F(101900963, 147044288) < 1, 'actual marked source passes core lift')
    carrier = 315 * prod(primes)
    density = F(total, carrier) * (1 - debit)
    result = {'scope': 'Exact full saturated means on one fixed71-original actual source, all32 outside '
              'cofactors. Every root intersection checked. Not a uniform arbitrary-family bound.',
              'source_survivor_count': total, 'partials': partials, 'weighted_debit': str(debit),
              'weighted_debit_decimal': float(debit), 'complete_mean': str(sum(means.values(), F(0))),
              'higher_core_extension_Haar_lower': str(density), 'cylinder_maxima': maxima,
              'checked_query_slots': len(maxima)}
    return result

DEPENDENCIES={'fibre_credit_depth_two_saturated_partial_obstruction.json': '4fa1ac005550335dd929d984d191ec0c85cf701dd6837ed985d0f65876e8a4de', 'fibre_credit_depth_two_core_height_joint_bridge.json': '385db85e5f01bb21534c4e31ed9f089d0871360193236dab1f1fbc42bb08a491'}

def calculate():
    directory=Path(__file__).resolve().parent
    for name,digest in DEPENDENCIES.items():
        need(sha256((directory/name).read_bytes()).hexdigest()==digest,'pinned actual marked dependency: '+name)
    partial=json.loads((directory/'fibre_credit_depth_two_saturated_partial_obstruction.json').read_text())['partial']
    core=json.loads((directory/'fibre_credit_depth_two_core_height_joint_bridge.json').read_text())['partial_bounds'][0]
    source=actual_source(partial,core)
    marked=marked_queries(source)
    need(marked['higher_core_extension_Haar_lower']=='5015925/118982864','same actual source full-core-height continuation')
    return {'scope':'One fixed71-class actual family has a successful marked all-core-height continuation. '
            'New high-core moduli may bear every outside subset. Not arbitrary shallow families or Lean.',
            'dependency_hashes':DEPENDENCIES,'actual_source':source,'marked_queries':marked}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args(); result=json.loads(json.dumps(calculate()))
    rendered=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output is None:
        need(json.loads(Path(__file__).resolve().with_suffix('.json').read_text())==result,
             'retained result agrees with actual marked source')
        print(rendered,end='')
    else:args.output.write_text(rendered)

if __name__=='__main__':main()
