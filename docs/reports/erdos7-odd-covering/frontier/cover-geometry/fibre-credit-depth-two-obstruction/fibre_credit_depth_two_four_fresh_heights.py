#!/usr/bin/env python3
"""Exact enclosure candidate with cubic unary, quadratic pair, and linear higher loads."""
from fractions import Fraction as F
from collections import Counter
from itertools import product
from pathlib import Path
import json
import runpy
from hashlib import sha256
from math import prod

DEPENDENCIES = {
    'fibre_credit_depth_two_uniform_shallow.py':
        '1f01fb1c704a48fddb7f0be9563635cbb4ea436ce1495d2e156fdfc3c0788de6',
    'fibre_credit_depth_two_uniform_shallow.json':
        'afc7b9a8167cf22e67885e427c865c5daa844eb3664b6ff7b684be56e3168591',
    'fibre_credit_depth_two_head_cubic.py':
        '742cc3299b597da64d4a2b1330c8875c6c68c571adccf1d154cfadff783295f1',
    'fibre_credit_depth_two_head_cubic.json':
        '04abeee82ca5c1c1b7c4f2363633211b5385c688659ab65bc9963d75be4bddec',
}


def replay_sources():
    directory = Path(__file__).resolve().parent
    for filename, expected in DEPENDENCIES.items():
        if sha256((directory / filename).read_bytes()).hexdigest() != expected:
            raise RuntimeError('pinned same-source dependency: ' + filename)
    results = []
    for suffix in ('uniform_shallow', 'head_cubic'):
        stem = 'fibre_credit_depth_two_' + suffix
        module = runpy.run_path(str(directory / (stem + '.py')))
        result = json.loads(json.dumps(module['calculate']()))
        if json.loads((directory / (stem + '.json')).read_text()) != result:
            raise RuntimeError('replayed common-source result differs: ' + stem)
        results.append(result)
    return results


def calculate():
    source, cubes = replay_sources()
    TARGET=18000
    CAPS=(28,30,36,40)
    WEIGHTS=(30,24,15,10)
    MAX_DEPTH=10
    MAX_NODES=20000000
    visits=Counter();leaves=Counter();nodes=0
    children=tuple(product((0,1),repeat=4))


    def need(ok,message):
        if not ok:raise RuntimeError(message)


    def certify(a,b,c,e,d,depth):
        nonlocal nodes
        nodes+=1;visits[depth]+=1
        # The complete Phi_(1/8) response is coordinatewise nondecreasing.
        # Use the SAME lower corner in numerator and denominator, in both regimes.
        u,v,w,z=28*d-a-1,30*d-b-1,36*d-c-1,40*d-e-1
        us,vs,ws,zs=u*u,v*v,w*w,z*z
        m=us*(vs+ws+zs)+vs*(ws+zs)+ws*zs
        n=u*v*w*z
        weighted_cubes=30*a*a*a+24*b*b*b+15*c*c*c+10*e*e*e
        if m and 16*n<=m:
            num=m*d*weighted_cubes+30*n*n
            den=30*m*d**4
        elif m:
            num=256*d*weighted_cubes+30*(32*n-m)
            den=7680*d**4
        else:
            num=weighted_cubes;den=30*d**3
        if num>=TARGET*den:
            leaves[depth]+=1
            return
        need(depth<MAX_DEPTH and nodes<MAX_NODES,
             f'bounded enclosure incomplete at {(a,b,c,e,d,depth)} lower={F(num,den)}')
        for i,j,k,l in children:
            certify(2*a+i,2*b+j,2*c+k,2*e+l,2*d,depth+1)


    for a,b,c,e in product(range(1,28),range(1,30),range(1,36),range(1,40)):
        certify(a,b,c,e,1,0)

    root_volume=27*29*35*39
    need(sum((F(n,16**depth) for depth,n in leaves.items()),F(0))==root_volume,
         'accepted cell volumes cover the complete continuous rectangle')
    refinements=nodes-sum(leaves.values())
    need(nodes==root_volume+16*refinements,'all sixteen children checked at every refinement')
    outside=min(F(w*r**3+sum(WEIGHTS)-w,30) for w,r in zip(WEIGHTS,CAPS))
    need(outside>TARGET,'one capped unary coordinate proves the full exterior bound')

    G2=max(F(row['Gamma23_upper']) for row in source['square_moment29_extension']['rows'])
    shapes=source['complete_shallow_bounds'][1]['shape_bounds']
    need([row['shape'] for row in cubes['rows']] == [row['shape'] for row in shapes],
         'cubic bounds and actual carrier use the same six shapes')
    lift3=prod(1+F(7,p-1) for p in source['complete_shallow_bounds'][1]['outside_primes'])
    G3=max(F(cubic['cubic_upper'])*lift3/F(shape['continuous_gate'])
           for cubic,shape in zip(cubes['rows'],shapes))
    need(G2 == F(2607189975,7283281), 'replayed common-source square bound')
    need(source['complete_shallow_bounds'][1]['uniform_density_lower_if_positive'] == '104726/6084351',
         'replayed common-source Haar lower')
    t=F(19)
    need(G2<t*t, 'same-source mean bound follows from its square bound')
    budget=F(79,30)*G3+6*G2+F(131,8)*t
    EW=8*(TARGET-budget)
    Haar=F(104726,6084351)*EW/(28*30*36*40)
    G3old=F(94428228722435,16149165669)
    budget_old=F(79,30)*G3old+6*G2+F(131,8)*t
    EWold=8*(TARGET-budget_old)
    Haar_old=F(104726,6084351)*EWold/(28*30*36*40)
    need(G3==F(906617738995,159166336),'new same-source raw cubic normalization')
    need(budget<TARGET and EW>0 and Haar>F(1,17000),'strict four-axis mixed-moment surplus')
    need(budget_old<TARGET and Haar_old>F(1,62000), 'inherited cubic already suffices')
    out={'scope':'Ordinary proof and exact integer certificate, not Lean. '
                 'Old d|334639305, four distinct fresh primes q1>=29,q2>=31,q3>=37,q4>=41, '
                 'arbitrary finite fresh heights and simultaneous phases. Old core heights remain restricted.',
         'target':TARGET,'dependency_hashes':DEPENDENCIES,'sources_replayed':True,'processed_nodes':nodes,'visits_by_depth':dict(visits),
         'accepted_leaves_by_depth':dict(leaves),'volume':root_volume,'complete':True,
         'pointwise_lower':'A1^3+(4/5)A2^3+(1/2)A3^3+(1/3)A4^3+Phi_(1/8)(P,D_pair)>=18000',
         'outside_rectangle_lower':str(outside),'source_square_upper':str(G2),
         'source_cubic_upper':str(G3),'source_mean_upper':str(t),
         'expected_cost_upper':str(budget),
         'mean_W_lower':str(EW),'Haar_lower':str(Haar),'simple_Haar_lower':'1/17000',
         'old_cubic_bound':str(G3old),'old_expected_cost_upper':str(budget_old),
         'old_mean_W_lower':str(EWold),'old_Haar_lower':str(Haar_old),
         'old_simple_Haar_lower':'1/62000','kappa':'1/8'}
    return out


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = json.loads(json.dumps(calculate()))
    rendered = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output is None:
        if json.loads(Path(__file__).resolve().with_suffix('.json').read_text()) != result:
            raise RuntimeError('retained result differs from the complete four-dimensional certificate')
        print(rendered, end='')
    else:
        args.output.write_text(rendered)


if __name__ == '__main__':
    main()
