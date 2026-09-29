#!/usr/bin/env python3
"""Exact actual-CRT checks of the full-query cubic variational interface."""
from fractions import Fraction as F
from itertools import product,combinations
from collections import defaultdict
from pathlib import Path
from math import ceil,prod,gcd
import json

def need(ok,message):
    if not ok:raise RuntimeError(message)

def calculate():
    K=15
    mods=(1,3,5,15)
    X=tuple(x for x in range(K) if gcd(x,K)==1)
    layouts=tuple((0,)+a for a in product(range(3),range(5),range(15)))
    loads={a:tuple(sum(x%d==r for d,r in zip(mods,a)) for x in X) for a in layouts}

    def maximum_linear(row_weights):
        phases=[];value=F(0)
        for d in mods:
            sums=[sum((row_weights[i] for i,x in enumerate(X) if x%d==a),F(0)) for a in range(d)]
            best=max(sums)
            phases.append(sums.index(best))
            value+=best
        return tuple(phases),value

    probabilities={
        'uniform':tuple(F(1,len(X)) for _ in X),
        'biased_same_support':tuple(F(1,2) if x==1 else F(1,14) for x in X),
        'weighted_same_support':tuple(F(z,36) for z in (1,2,3,4,5,6,7,8)),
        'reverse_weighted_same_support':tuple(F(z,36) for z in (8,7,6,5,4,3,2,1)),
    }
    results=[]
    checks=0
    for name,mu in probabilities.items():
        need(sum(mu)==1 and min(mu)>0,'same actual full-support carrier')
        cubes={a:sum(mu[i]*v**3 for i,v in enumerate(loads[a])) for a in layouts}
        Gamma=max(cubes.values())
        scores=[];strict=0;traps=[]
        for a in layouts:
            t=loads[a]
            b,R=maximum_linear(tuple(mu[i]*t[i]**2 for i in range(len(X))))
            score=3*R-2*cubes[a]
            need(cubes[b]>=score>=cubes[a],'globally fixed complete-query tangent ascent')
            scores.append(score)
            strict+=cubes[b]>cubes[a]
            if b==a and cubes[a]<Gamma:
                traps.append({'phases':a,'cube':str(cubes[a]),'global':str(Gamma)})
            checks+=1
        need(max(scores)==Gamma,'exact full-query variational maximum over all actual query load fields')
        strongest=F(0);strongest_subset=()
        for bits in product((0,1),repeat=len(X)):
            mass=sum((mu[i] for i,b in enumerate(bits) if b),F(0))
            if mass==0:continue
            b,R=maximum_linear(tuple(mu[i]*bits[i] for i in range(len(X))))
            lower=R**3/mass**2+1-mass
            need(lower<=cubes[b]<=Gamma,'localized row concentration with baseline outside the event')
            if lower>strongest:
                strongest=lower
                strongest_subset=tuple(X[i] for i,b in enumerate(bits) if b)
            checks+=1
        selected=(0,0,0,0)
        need(loads[selected]==(1,)*len(X),'same selected field under distinct actual laws')
        results.append({'law':name,'weights':list(map(str,mu)),'universal_cubic_max':str(Gamma),
                        'selected_query_cube':str(cubes[selected]),'strict_ascent_layouts':strict,
                        'stationary_suboptimal_examples':traps[:2],
                        'strongest_localized_lower':str(strongest),'localized_subset':strongest_subset})

    # Coherent full-dictionary test: sum of pairwise row collision kernels.
    energy=[]
    cylinder_checks=0
    for name,mu in probabilities.items():
        pair=sum((mu[i]*mu[j]*sum((1 for d in mods if (x-y)%d==0))**3
                  for i,x in enumerate(X) for j,y in enumerate(X)),F(0))
        # For squarefree15, tau(gcd)^3=(1+7[3|diff])*(1+7[5|diff]).
        weights={1:1,3:7,5:7,15:49}
        collisions=F(0)
        for d,w in weights.items():
            masses=[sum((mu[i] for i,x in enumerate(X) if x%d==a),F(0)) for a in range(d)]
            collisions+=w*sum(t*t for t in masses)
        need(pair==collisions,'coherent cubic energy equals weighted marginal collision probabilities')
        gamma=F(next(z['universal_cubic_max'] for z in results if z['law']==name))
        need(pair<=gamma,'coherent random-centre energy uses fixed global phases')
        energy.append({'law':name,'collision_energy':str(pair)})
        for m in mods:
            kernel=sum((F(w*gcd(d,m),d) for d,w in weights.items()),F(0))
            for a in range(m):
                centres=tuple(y for y in range(K) if y%m==a)
                mass=sum((mu[i] for i,x in enumerate(X) if x%m==a),F(0))
                for x in centres:
                    exact=F(sum(sum((1 for d in mods if (x-y)%d==0))**3 for y in centres),len(centres))
                    need(exact==kernel,'conditional coherent-centre kernel from literal CRT centre enumeration')
                need(1+mass*(kernel-1)<=gamma,'localized coherent cubic cap including outside unit term')
                cylinder_checks+=1

    old_primes=(5,7,11,13,17,19,23)
    divisors=tuple(3**j*prod((p for p,b in zip(old_primes,bits) if b),start=1)
                   for j in range(3) for bits in product((0,1),repeat=7))
    need(len(set(divisors))==384,'actual shallow23 complete numerical dictionary')
    G3=F(906617738995,159166336)
    atom_cap=(G3-1)/(384**3-1)
    formal_p=tuple(F(n,100000) for n in (34625,28046,15971,11494,9864))
    cardinality_needs=[ceil(p/atom_cap) for p in formal_p]
    literal_five_lower=1+(384**3-1)*max(formal_p)
    need(literal_five_lower>G3,'five source atoms cannot each be one actual old row')

    out={'scope':'Actual fixed-phase complete queries on the same CRT carrier; ordinary exact checks, not Lean. No rejection of arbitrary fine embeddings of the formal five-block model.',
         'carrier':K,'actual_source_points':X,'complete_layout_count':len(layouts),
         'checks':checks,'source_results':results,'coherent_collision_energies':energy,
         'conditional_cylinder_kernel_checks':cylinder_checks,
         'shallow23_dictionary_size':len(divisors),'G3new':str(G3),
         'necessary_actual_row_mass_cap':str(atom_cap),
         'literal_five_actual_rows_cubic_lower':str(literal_five_lower),
         'minimum_fine_row_counts_per_formal_block':cardinality_needs,
         'minimum_total_fine_rows_from_blocks':sum(cardinality_needs),
         'interpretation':'A real embedding must supply its residue-incidence table. Full-query weighted-cylinder tests, not selected scalar moments, then check it. Replicating formal atoms without giving incidence does not settle compatibility.'}
    return out


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = json.loads(json.dumps(calculate()))
    rendered = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output is None:
        need(json.loads(Path(__file__).resolve().with_suffix('.json').read_text()) == result,
             'retained result agrees with complete fixed-phase query checks')
        print(rendered, end='')
    else:
        args.output.write_text(rendered)


if __name__ == '__main__':
    main()
