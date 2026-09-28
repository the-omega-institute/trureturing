"""Literal CRT and phase enumeration for the complete tight-row odd wheel."""
from argparse import ArgumentParser
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from math import prod
from pathlib import Path
import json


def need(value,message):
    if not value:
        raise ValueError(message)


def rational(x):
    return str(x)


def coprime_crt(residues,moduli):
    total=prod(moduli)
    return sum(a*(total//d)*pow(total//d,-1,d)
               for a,d in zip(residues,moduli))%total


def actual_wheel_fixture():
    p=3;n=6
    edges={tuple(sorted((0,i))) for i in range(1,n)}
    edges.update(tuple(sorted((1+i,1+(i+1)%5))) for i in range(5))
    nonedges=[ij for ij in combinations(range(n),2) if ij not in edges]
    conflict_primes=[5,7,11,13,17]
    tags=[19,23,29,31,37,41]
    coordinates=conflict_primes+tags;B=prod(coordinates);Q=p*B
    specifications=[{tags[i]:0} for i in range(n)]
    for ell,(i,j) in zip(conflict_primes,nonedges):
        specifications[i][ell]=0
        specifications[j][ell]=1
    ms=[prod(spec) for spec in specifications]
    bs=[coprime_crt(list(spec.values()),list(spec)) for spec in specifications]
    need(len(set(ms))==n,'wheel repeats numerical cofactors')
    from math import gcd,lcm
    for i,j in combinations(range(n),2):
        compatible=(bs[i]-bs[j])%gcd(ms[i],ms[j])==0
        need(compatible==((i,j) in edges),'complete actual cofactor compatibility graph differs from wheel')
    clique_witnesses=[]
    for mask in range(1<<n):
        active=[i for i in range(n) if mask>>i&1]
        if not all(tuple(ij) in edges for ij in combinations(active,2)):
            continue
        coordinate_values={ell:0 for ell in coordinates}
        for i,tag in enumerate(tags):
            coordinate_values[tag]=int(i not in active)
        for i in active:
            coordinate_values.update(specifications[i])
        y=coprime_crt([coordinate_values[ell] for ell in coordinates],coordinates)
        actual=[i for i in range(n) if y%ms[i]==bs[i]]
        need(actual==active,'clique CRT witness has wrong full active set')
        clique_witnesses.append({'vertices':active,'cofactor':y})
    need(len(clique_witnesses)==22,'wheel clique count')
    need(max(len(w['vertices']) for w in clique_witnesses)==3,'full cofactor graph has an oversized clique')
    rows=[w for w in clique_witnesses if len(w['vertices'])==3]
    need(len(rows)==5,'full tight-row patterns are not exactly the five wheel triangles')
    point_rows=[[coprime_crt([u,w['cofactor']],[p,B]) for u in range(p)] for w in rows]
    points=[x for row in point_rows for x in row]
    ds=[p*m for m in ms]
    residues=[[coprime_crt([a,b],[p,m]) for a in range(p)] for b,m in zip(bs,ms)]
    hits=[[[int(x%d==a) for x in points] for a in options] for d,options in zip(ds,residues)]
    row_masses=[F(1,lcm(*(ms[i] for i in w['vertices']))) for w in rows]
    local=[None]*5;hist=Counter();best=None;best_count=16;best_mass=None;best_mass_witness=None
    for phases in product(range(p),repeat=n):
        counts=[sum(hits[i][phases[i]][j] for i in range(n)) for j in range(len(points))]
        row_holes=[counts[3*j:3*j+3].count(0) for j in range(5)]
        for j in range(5):
            need(sum(counts[3*j:3*j+3])==3,'actual tight row is not average one')
            if row_holes[j]==0 and local[j] is None:
                local[j]=list(phases)
        total=sum(row_holes);hist[total]+=1
        mass=sum((mu*F(h,p) for mu,h in zip(row_masses,row_holes)),F(0))
        if best_mass is None or mass<best_mass:
            best_mass=mass
            best_mass_witness={'p_phases':phases,
                'literal_residues':[residues[i][a] for i,a in enumerate(phases)],
                'holes_per_p_fibre':row_holes,
                'row_hole_masses':[rational(mu*F(h,p)) for mu,h in zip(row_masses,row_holes)],
                'total_tight_region_hole_mass':rational(mass)}
        if total<best_count:
            best_count=total
            best={'p_phases':phases,'literal_residues':[residues[i][a] for i,a in enumerate(phases)],
                  'selected_holes':[x for x,c in zip(points,counts) if c==0]}
    need(sum(hist.values())==729 and best_count==1,'full wheel phase obstruction')
    need(all(v is not None for v in local),'wheel row not independently coverable')
    need(best_mass==min(row_masses)/p,'sharp tight-region Haar lower bound')
    return {'prime':p,'period':Q,'cofactor_period':B,'cofactor_moduli':ms,'cofactor_residues':bs,
        'original_moduli':ds,'conflict_prime_nonedges':[{'prime':ell,'nonedge':list(ij)} for ell,ij in zip(conflict_primes,nonedges)],
        'unique_tag_primes':tags,'complete_cofactor_compatibility_edges':sorted(edges),
        'all_exact_active_clique_witnesses':clique_witnesses,
        'all_tight_row_active_patterns':rows,'representative_point_rows':point_rows,
        'individual_row_cover_phase_witnesses':local,'phase_assignments':729,
        'selected_hole_count_histogram':dict(sorted(hist.items())),'minimum_selected_holes':best_count,
        'attaining_assignment':best,'full_tight_conflict_maximum_clique_weight':'1',
        'tight_row_cofactor_masses':list(map(rational,row_masses)),
        'minimum_actual_tight_region_hole_mass':rational(best_mass),
        'attaining_tight_region_mass_assignment':best_mass_witness,
        'scope':'The COMPLETE cofactor compatibility graph and COMPLETE tight-row conflict graph are the odd wheel, not a selected subgraph of K6. Every tight row is independently coverable, all weighted-clique bounds pass, but no common 3-phase assignment covers every tight row. Other cofactor rows have marginals 0,1/3,2/3 and are not claimed to pass global lower bounds.'}



def main():
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    result={'result':'PASS','odd_wheel_joint_obstruction':actual_wheel_fixture(),
        'scope':'Ordinary exact control of the complete tight-row phase graph and its sharp hole mass. Other cofactor rows have marginals below one. No all-support-marginal counterexample, Lean verification, or unrestricted odd-covering resolution is claimed.'}
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8')
    print('PASS: 15 CRT pairs, 22 exact active patterns, 729 original phase assignments; sharp tight-region mass attained')


if __name__=='__main__':
    main()
