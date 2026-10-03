#!/usr/bin/env python3
"""Exact adaptive source selection and two full-old-height continuations."""
from fractions import Fraction as Q
from pathlib import Path
from functools import lru_cache
from itertools import product, combinations
from math import prod, ceil, lcm
from hashlib import sha256
from tempfile import TemporaryDirectory
import argparse, json, subprocess


def check(ok, message):
    if not ok:
        raise RuntimeError(message)


def source_cases(directory, catalogue, weights, inherited):
    expected = {(tuple(r['b']), r['M']) for r in catalogue['exceptional_sources']}
    supplied = {(tuple(r['b']), r['uniform_group'][1]) for r in weights['rows']}
    check(expected == supplied and len(supplied) == len(weights['rows']) == 28,
          'all exceptional actual sources have exactly one fixed probability')
    lines = ['28']
    for i, row in enumerate(weights['rows']):
        u = list(map(Q, row['row_probabilities']))
        b = row['b']
        check(len(u) == len(b) == 17 and min(u) >= 0 and sum(u) == 1,
              'fixed actual old45 marginal probability')
        check(row['uniform_group'][0] == 86 and sum(6 - v for v in b) == 86,
              'actual source support has its stated uniform group')
        cell = [value / (6 - v) for value, v in zip(u, b)]
        den = lcm(*(v.denominator for v in cell))
        nums = [int(v * den) for v in cell]
        check(sum((6 - v) * n for v, n in zip(b, nums)) == den, 'native source mass')
        lines.append(' '.join(map(str, [i, den] + b + nums)))
    native = directory / 'fibre_credit_depth_two_reweighted_source_hinges.cpp'
    # Native checks denominators<=10^12; all arithmetic sums are below
    #17*6*12*10^12, strictly less than the signed64-bit maximum.
    with TemporaryDirectory(prefix='e7_reweighted_source_') as temporary:
        temp = Path(temporary)
        inputs, outputs, executable = temp / 'weights.txt', temp / 'hinges.json', temp / 'query'
        inputs.write_text('\n'.join(lines) + '\n')
        subprocess.run(['c++', '-std=c++17', '-O2', '-fsanitize=undefined',
                        '-fno-sanitize-recover=all', str(native), '-o', str(executable)],
                       check=True, capture_output=True)
        subprocess.run([str(executable), str(inputs), str(outputs)],
                       check=True, capture_output=True)
        raw = json.loads(outputs.read_text())
    check(raw['ordered_pairs'] == 22657600 and len(raw['rows']) == 28,
          'all weighted query pairs checked on every source')
    points = [x for x in range(45) if all(x % d != a for d, a in
              ((3, 0), (9, 4), (5, 0), (15, 1), (45, 37)))]
    groups = {d: [tuple(i for i, x in enumerate(points) if x % d == a)
                  for a in range(d)] for d in (3, 5, 9, 15, 45)}
    weighted = []
    for i, (row, result) in enumerate(zip(weights['rows'], raw['rows'])):
        check(result['id'] == i and row['b'] == result['b'], 'same native actual source')
        cell = [Q(v, result['denominator']) for v in result['cell_weight_numerators']]
        u = list(map(Q, row['row_probabilities']))
        check(all(w == v / (6 - b) for w, v, b in zip(cell, u, row['b'])),
              'literal source probabilities bound to their support')
        independent_mean = sum(cell) + sum(max(sum(u[i] for i in C) for C in gs)
                                           + max(sum(cell[i] for i in C) for C in gs)
                                           for gs in groups.values())
        hinges = [Q(v, result['denominator']) for v in result['hinge_numerators']] + [Q(0), Q(0)]
        check(hinges[0] - hinges[1] == 1 and hinges[1] == independent_mean,
              'complete weighted mean agrees with separate cylinder maxima')
        law = {y: hinges[y-1] - 2*hinges[y] + hinges[y+1] for y in range(1, 13)}
        check(min(law.values()) >= 0 and sum(law.values()) == 1, 'genuine weighted law')
        check(all(sum(p*max(y-t, 0) for y, p in law.items()) == hinges[t]
                  for t in range(14)), 'all weighted hinges recovered')
        weighted.append({'id': row['id'], 'M': row['uniform_group'][1], 'b': row['b'],
                         'head315_density_cap': str(315*max(cell)),
                         'nonunit_mean': str(hinges[1]), 'hinge_bounds': list(map(str, hinges[:12])),
                         'comparison_law': [{'value': y, 'probability': str(p)}
                                            for y, p in law.items() if p]})
    cases = []
    for row in catalogue['rows']:
        if (row['N'], row['M']) in ((86, 184), (86, 185)):
            continue
        cases.append(('uniform-first', f"{row['N']}/{row['M']}", Q(315, row['N']),
                      Q(row['nonunit_mean']), row['comparison_law']))
    check(len(cases) == 190, 'unchanged first-shape source groups')
    for row in weighted:
        cases.append(('weighted'+str(row['M']), str(row['id']), Q(row['head315_density_cap']),
                      Q(row['nonunit_mean']), row['comparison_law']))
    for row in inherited[1:]:
        cases.append(('other-shape', row['shape'], Q(315, row['old315_Nmin']),
                      Q(row['hinge_bounds'][1]), row['comparison_law']))
    check(len(cases) == 223, 'complete source selection')
    return cases, weighted


def gate_parameters(five, six, bridge):
    fixed = five['gate']['fixed_penalties']
    check(five['gate']['complete_exact_enclosure'] and six['complete_exact_enclosure'],
          'inherited complete scalar gates')
    check(fixed['target'] == 18000 and six['target'] == 19100, 'inherited thresholds')
    sixth = six['fixed_penalties']
    check(fixed['Y_knots'] == sixth['Y_knots'], 'same unbounded pair penalty')
    knots = fixed['Y_knots']
    slopes = [a+b for a, b in zip(knots, knots[1:])]
    g = {knots[0]: Q(slopes[0])}
    for j in range(1, len(slopes)):
        g[knots[j]] = Q(slopes[j] - slopes[j-1])
    for parameters, count, kap in ((fixed, 5, Q(1, 125)), (sixth, 6, Q(1, 5000))):
        r = parameters['capacities']
        check(len(r) == count and Q(parameters['kappa']) == kap, 'same gate capacities')
        check(max(kap*prod(r[i]-1 for i in range(count) if i not in J)
                  for J in combinations(range(count), 2)) < 640,
              'pair conjugate valid for unbounded fields')
    linear = Q(sixth['higher_support_mean_coefficient'], 5000)
    dc = {t: 15*v for t, v in g.items()}
    dc[1] += linear
    for row in sixth['unary_hinge_coefficient_numerators']:
        for t, value in zip(sixth['thresholds'], row):
            dc[t] = dc.get(t, Q(0)) + Q(value, sixth['coefficient_denominator'])
    constant = 15 + linear
    check(constant == Q(bridge['uniform_profile_constant']) and
          dc == {int(t): Q(v) for t, v in bridge['uniform_profile_hinge_coefficients'].items()},
          'aggregate six-field fees match the proved unbounded interface')
    return fixed, tuple(knots), slopes, dc, constant


@lru_cache(None)
def tail(p,n):
    if n==0:return Q(1)
    if n==1:return Q(1,p-1)
    return Q(1,(p-2)*p**(n-1))
def after(p,n):return Q(1,p-2) if n==0 else Q(p,p-1)*tail(p,n+1)
@lru_cache(None)
def survival(primes,a,t):
    if not primes:return Q(a>t)
    p=primes[0];rest=primes[1:];j=t//a
    return tail(p,j)+sum(((tail(p,n)-tail(p,n+1))*survival(rest,a*(1+n),t) for n in range(j)),Q(0))
@lru_cache(None)
def hinge(primes,a,t):
    if not primes:return Q(max(a-t,0))
    p=primes[0];rest=primes[1:];j=t//a
    finite=sum(((tail(p,n)-tail(p,n+1))*hinge(rest,a*(1+n),t) for n in range(j)),Q(0))
    mr=prod((1+Q(1,q-2) for q in rest),start=Q(1))
    return finite+a*mr*((1+j)*tail(p,j)+after(p,j))-t*tail(p,j)


def continuation(cases,fixed,knots,slopes,DC,constant):
    axes=(11,13,17,19,23);results=[]
    for deep,fresh,target,kap,r,friendly in (((19,23),6,19100,Q(1,5000),(28,30,36,40,42,46),Q(1,350000)),((17,19,23),5,18000,Q(1,125),(28,30,36,40,42),Q(1,75000))):
        z=[Q(1,p-2 if p in deep else p-1) for p in axes];factor=prod(Q(p,p-2 if p in deep else p-1) for p in axes)
        shallow=[p for p in axes if p not in deep];rows=[];rawcosts=[]
        for kind,ident,D315,c,law in cases:
            check(sum(Q(y['probability']) for y in law)==1 and min(Q(y['probability']) for y in law)>=0,'genuine core law')
            check(sum(int(y['value'])*Q(y['probability']) for y in law)==1+c,'same source mean')
            delta=c+2+sum(z)-(c+1)*prod(1+x for x in z);D=D315*factor;check(delta>0,'one actual mixed restriction')
            atoms={}
            for y in law:
                for bits in product((0,1),repeat=len(shallow)):
                    a=int(y['value'])*2**sum(bits)
                    w=Q(y['probability'])*prod((Q(1,p-1) if bit else Q(p-2,p-1) for p,bit in zip(shallow,bits)),start=Q(1))
                    atoms[a]=atoms.get(a,Q(0))+w
            def sf(t):return sum((w*survival(deep,a,t) for a,w in atoms.items()),Q(0))
            def raw(t):return sum((w*hinge(deep,a,t) for a,w in atoms.items()),Q(0))
            lo=0;hi=1
            while sf(hi)>delta:hi*=2
            while hi-lo>1:
                mid=(lo+hi)//2
                if sf(mid)>delta:lo=mid
                else:hi=mid
            cut=hi;check(sf(cut)<=delta<=sf(cut-1),'one common upper-delta law')
            mean=cut+raw(cut)/delta;caps={t:mean-t if t<=cut else raw(t)/delta for t in knots}
            if fresh==5:
                eg=1+slopes[0]*caps[1]+sum((slopes[j]-slopes[j-1])*caps[knots[j]] for j in range(1,len(slopes)))
                cost=sum(Q(v,100)*caps[t] for coeff in fixed['unary_hinge_coefficient_numerators'] for t,v in zip(fixed['thresholds'],coeff))+10*eg+Q(11794,125)*mean
            else:cost=constant+sum(v*caps[t] for t,v in DC.items())
            upper=ceil(cost);check(cost<upper<target,'strict certified cost ceiling')
            rawcosts.append(cost)
            rows.append({'kind':kind,'case':ident,'delta':str(delta),'raw_Haar_cap':str(D),'normalized_Haar_factor':str(delta/D),'quantile':cut,'cost_strict_upper':upper,'cost_display':float(cost)})
        upper=max(x['cost_strict_upper'] for x in rows);hmin=min(Q(x['normalized_Haar_factor']) for x in rows)
        density=hmin*(target-upper)/(kap*prod(r));check(density>friendly,'uniform finite-height noncoverage bound')
        worst=max(range(len(rows)),key=lambda i:rawcosts[i]);paired=min(Q(x['normalized_Haar_factor'])*(target-v)/(kap*prod(r)) for x,v in zip(rows,rawcosts))
        result={'deep':list(deep),'fresh_count':fresh,'target':target,'kappa':str(kap),'reference_capacities':list(r),'case_count':223,'global_cost_strict_upper':upper,'worst_case':rows[worst]['kind']+':'+rows[worst]['case'],'worst_cost_display':float(rawcosts[worst]),'minimum_normalized_Haar_factor':str(hmin),'conservative_margin':target-upper,'Haar_survivor_lower':str(density),'simple_strict_Haar_lower':str(friendly),'paired_Haar_lower_display':float(paired),'rows':rows}
        results.append(result)
    return results

DEPENDENCIES={'fibre_credit_depth_two_actual_source_catalogue.json': 'acfb87e349621565e594b52913b9663ab81f0fc8f82dd1c8600a4df80b7edd8e', 'fibre_credit_depth_two_reweighted_source_weights.json': '820c0aa78fe37e7343936d3108da9c94e35edf00cc63458948b2670bcf0e6ac1', 'fibre_credit_depth_two_reweighted_source_hinges.cpp': 'dd7f6b752410efd2f70b471327b6fc7b1150ed129b33b6785ed6e62445f116de', 'fibre_credit_depth_two_old23_full_height.json': 'ca998ef3ce5e1043cbd1a78a4f9cd4306b12cfb781b219729aa916f0ba016ede', 'fibre_credit_depth_two_old19_old23_five_fresh.json': 'a3253b132077d7c95e7a39a80b583f39cbc49f4444ab03a14fb96250247bfc5b', 'fibre_credit_depth_two_old23_gate.json': '8263571884835d712c0b70edce8c63d6643d24c6900a43865413352389c68871', 'fibre_credit_depth_two_old_height_hinge_bridge.json': '699dbd9dd90bba1011052121b159938fdfcfe834892077085c6494ab3a411c49'}

def calculate():
    directory=Path(__file__).resolve().parent
    for name,digest in DEPENDENCIES.items():
        check(sha256((directory/name).read_bytes()).hexdigest()==digest,'pinned adaptive source dependency: '+name)
    def load(name):return json.loads((directory/name).read_text())
    catalogue=load('fibre_credit_depth_two_actual_source_catalogue.json')
    weights=load('fibre_credit_depth_two_reweighted_source_weights.json')
    inherited=load('fibre_credit_depth_two_old23_full_height.json')['rows']
    fixed,knots,slopes,dc,constant=gate_parameters(
        load('fibre_credit_depth_two_old19_old23_five_fresh.json'),
        load('fibre_credit_depth_two_old23_gate.json'),
        load('fibre_credit_depth_two_old_height_hinge_bridge.json'))
    cases,weighted=source_cases(directory,catalogue,weights,inherited)
    results=continuation(cases,fixed,knots,slopes,dc,constant)
    check([r['global_cost_strict_upper'] for r in results]==[18974,17420], 'all source fee bounds')
    check([r['Haar_survivor_lower'] for r in results]==['144433/49258905696','11011445/809559406656'],
          'two actual full-height survivor bounds')
    return {'scope':'Two restricted noncoverage results from one selected actual source per original family. '
            'Full weighted queries and tails replayed; fixed rational weights, no LP optimality claim or Lean.',
            'dependency_hashes':DEPENDENCIES,'weighted_source_laws':weighted,'results':results,
            'source_catalogue_replayed':False,'scalar_gate_enclosures_replayed':False,
            'complete_weighted_query_enumeration_replayed':True,'old_core_caps':{'3':2,'5':1,'7':1}}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args(); result=calculate()
    rendered=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output is None:
        check(json.loads(Path(__file__).resolve().with_suffix('.json').read_text())==result,
              'retained result agrees with adaptive source continuation')
        print(rendered,end='')
    else:args.output.write_text(rendered)

if __name__=='__main__':main()
