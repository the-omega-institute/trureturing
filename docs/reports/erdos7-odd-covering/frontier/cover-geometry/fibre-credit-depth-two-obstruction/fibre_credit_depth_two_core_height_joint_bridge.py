#!/usr/bin/env python3
"""Exact partial-bound and higher-fibre examples for an all-height ICX bridge."""
from fractions import Fraction as F
from itertools import product, combinations
from pathlib import Path
from math import prod, gcd
import argparse,json
from hashlib import sha256

def need(b,m):
    if not b:raise RuntimeError(m)

DEPENDENCIES={'fibre_credit_depth_two_old23_full_height.json': 'ca998ef3ce5e1043cbd1a78a4f9cd4306b12cfb781b219729aa916f0ba016ede', 'fibre_credit_depth_two_old_height_subset_source.json': '2f9e9076607397d6cc49e55dd25eb2253f16db288b65865a87773dd07dc6e25f'}

def calculate():
    directory=Path(__file__).resolve().parent
    for name,digest in DEPENDENCIES.items():
        need(sha256((directory/name).read_bytes()).hexdigest()==digest,
             'pinned common source: '+name)
    head_rows=json.loads((directory/'fibre_credit_depth_two_old23_full_height.json').read_text())['rows']
    outside=json.loads((directory/'fibre_credit_depth_two_old_height_subset_source.json').read_text())
    mods=(3,5,9,15,45)
    subsets=[tuple(c) for k in range(1,4) for c in combinations((3,5,7),k)]
    rows=[]
    for root,shape in product((1,2),('same_other_column','other_same_column','other_other_column')):
        rr,cc=((root,2) if shape=='same_other_column' else (3-root,1 if shape=='other_same_column' else 2))
        a15=next(a for a in range(15) if a%3==root and a%5==1)
        a45=next(a for a in range(45) if a%9==rr and a%5==cc)
        originals=[(3,0),(9,4),(5,0),(15,a15),(45,a45)]
        points=[x for x in range(45) if all(x%m!=a for m,a in originals)]
        groups={m:sorted({tuple(i for i,x in enumerate(points) if x%m==a) for a in range(m)}-{()}) for m in mods}
        maxcount={m:max(map(len,gs)) for m,gs in groups.items()}
        n=len(points);nmin=6*n-sum(maxcount.values())
        current_head=head_rows[len(rows)]
        need(current_head['old45_survivors']==n and current_head['old315_Nmin']==nmin,
             'same actual head shape and source minimum')
        caps={}
        stats={}
        for S in subsets:
            selected=[d for d in (1,3,5,9,15,45) if (3 not in S or d%9==0) and (5 not in S or d%5==0)]
            constant=int(1 in selected)
            querymods=[d for d in selected if d>1]
            maxsum=n*constant+sum(maxcount[m] for m in querymods)
            if 7 in S:
                cap=F(maxsum,nmin)
                layouts=1
            else:
                best=F(0);layouts=0
                for chosen in product(*(groups[m] for m in querymods)):
                    counts=[constant]*n
                    for cylinder in chosen:
                        for i in cylinder:counts[i]+=1
                    zeros=[int(v==0) for v in counts]
                    zero_credit=sum(max(sum(zeros[i] for i in c) for c in groups[m]) for m in mods)
                    need(6*n-zero_credit>0,'partial D2 denominator')
                    g=F(6*sum(counts)+maxsum,6*n-zero_credit)
                    best=max(best,g);layouts+=1
                cap=best
                need(0<=cap<=1,'all partial no7 caps must lie in [0,1] for zero-only formula')
                # Reverify full positive-cylinder D2 at the computed rational cap.
                for chosen in product(*(groups[m] for m in querymods)):
                    counts=[constant]*n
                    for cylinder in chosen:
                        for i in cylinder:counts[i]+=1
                    credit=sum(max(sum(max(cap-counts[i],0) for i in c) for c in groups[m]) for m in mods)
                    need(6*sum(counts)+maxsum+credit<=6*n*cap,'partial positive-cylinder D2')
            caps[S]=cap
            stats[','.join(map(str,S))]={'cap':str(cap),'layouts':layouts,'query45_moduli':selected,'maximum45_sum':maxsum}
        lam=sum((caps[S]*prod((F(1,p-1) for p in S),start=F(1)) for S in subsets),F(0))
        need(lam<1,'all old3/5/7 heights lift by same source')
        rows.append({'shape':f'root{root}_{shape}','n45':n,'n315_min':nmin,'partial_query_caps':stats,
                     'deletion_upper':str(lam),'deletion_upper_decimal':float(lam),'retention_lower':str(1-lam),
                     'Haar_survivor_lower':str(F(nmin,315)*(1-lam))})

    # Two actual families with identical shallow family and projected new phases.
    base=[(3,0),(9,4),(5,0),(15,1),(45,37),(7,0)]
    # Optional redundant actual classes complete every old315 numerical slot.
    base += [(m,0) for m in (21,35,63,105,315)]
    x0=2; Q0=315
    need(all(x0%m!=a for m,a in base),'chosen coarse point survives every old actual original')
    examples=[]
    for p,H,cofactors in ((3,2,(1,5,7)),(5,1,(1,3,7,9,21))):
        Q=Q0*p
        fibre=[x0+Q0*t for t in range(p)]
        mods_new=[p**(H+1)*d for d in cofactors]
        killed=[(m,x%m) for m,x in zip(mods_new,fibre)]
        coincident=[(m,x0%m) for m in mods_new]
        need(len(set(m for m,a in base+killed))==len(base+killed),'distinct numerical labels')
        need(all(a%gcd(m,Q0)==b%gcd(m,Q0) for (m,a),(_,b) in zip(killed,coincident)),'same shallow projected phases')
        countsA=[sum(x%m==a for x in fibre) for m,a in killed]
        countsB=[sum(x%m==a for x in fibre) for m,a in coincident]
        need(countsA==countsB==[1]*p,'identical individual conditional masses')
        aliveA=[x for x in fibre if all(x%m!=a for m,a in killed)]
        aliveB=[x for x in fibre if all(x%m!=a for m,a in coincident)]
        need(len(aliveA)==0 and len(aliveB)==p-1,'different actual joint fibre survival')
        globalA=sum(all(x%m!=a for m,a in base+killed) for x in range(Q))
        globalB=sum(all(x%m!=a for m,a in base+coincident) for x in range(Q))
        need(globalA>0 and globalB>0,'method example is not an odd covering')
        examples.append({'prime':p,'old_height':H,'coarse_point':x0,'carrier':Q,'new_moduli':mods_new,
                         'partition_phases':[a for m,a in killed],'coincident_phases':[a for m,a in coincident],
                         'projected_phases':[a%gcd(m,Q0) for m,a in killed],
                         'individual_conditional_masses':[str(F(1,p))]*p,'fibre_survivors_partition':0,'fibre_survivors_coincident':p-1,
                         'global_survivors_partition':globalA,'global_survivors_coincident':globalB})

    # Prime7: six available old cofactors can erase six of seven descendants
    # at each new height, leaving a single nested branch of arbitrarily small mass.
    seven=[]
    for extra in range(1,6):
        Q=315*7**extra
        new=[]
        current=x0
        for j in range(1,extra+1):
            old_mod=315*7**(j-1)
            candidates=[current+old_mod*t for t in range(7)]
            for d,x in zip((1,3,5,9,15,45),candidates[:6]):
                m=7**(j+1)*d
                new.append((m,x%m))
            current=candidates[6]
        need(len({m for m,a in base+new})==len(base+new),'seven ladder uses distinct labels')
        fibre=range(x0,Q,315)
        alive=[x for x in fibre if all(x%m!=a for m,a in new)]
        need(alive==[current],'seven ladder retains exactly one descendant')
        coincident=[(m,x0%m) for m,a in new]
        alive_coincident=[x for x in range(x0,Q,315) if all(x%m!=a for m,a in coincident)]
        need(len(alive_coincident)==6*7**(extra-1),'coincident seven family retains six of seven first descendants')
        need(all(a%gcd(m,Q0)==b%gcd(m,Q0) for (m,a),(_,b) in zip(new,coincident)),'seven pair has identical projected phases')
        need(all(8%m!=a for m,a in base+new+coincident),'seven pairs each have an explicit global survivor')
        coincident=[(m,x0%m) for m,a in new]
        alive_other=[x for x in fibre if all(x%m!=a for m,a in coincident)]
        need(len(alive_other)==6*7**(extra-1),'coincident ladder retains six sevenths')
        need(all(8%m!=a for m,a in base+new) and all(8%m!=a for m,a in base+coincident),
             'one explicit global survivor in both ladder families')
        seven.append({'extra_height':extra,'new_modulus_count':len(new),'fibre_atom_count':7**extra,
                      'surviving_atom':current,'conditional_survival':str(F(1,7**extra)),
                      'coincident_survival':str(F(6,7)),'explicit_global_survivor':8})

    output={'scope':'Ordinary exact finite checks for partial315 query caps and actual high-digit joint obstructions; no Lean.',
            'partial_bounds':rows,'all_three_height_lift_retention_min':str(min(F(r['retention_lower']) for r in rows)),
            'all_three_height_lift_Haar_min':str(min(F(r['Haar_survivor_lower']) for r in rows)),
            'base_originals':base,'coarse_projection_pair_examples':examples,'seven_nested_ladder':seven}
    # The shared raw source cannot be closed by adding these two independent
    # union majorants. A negative lower estimate is not actual zero retention.
    joint=[]
    for case in outside['subsets']:
        J=case['full_height_axes']
        mult=prod(1+F(1,p-2 if p in J else p-1) for p in (11,13,17,19,23))
        for row,cell in zip(rows,case['shapes']):
            need(row['shape']==cell['shape'],'same source shape across interfaces')
            lower=F(cell['retention'])-F(row['deletion_upper'])*mult
            need(lower<0,'separated union bounds do not certify the common intersection')
            joint.append({'full_height_axes':J,'shape':row['shape'],'separated_retention_lower':str(lower)})
    output['joint_separated_estimates']=joint
    output['dependency_hashes']=DEPENDENCIES
    output['ordinary_ICX_transport_implemented_as_arithmetic_only']=True
    return output

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result=json.loads(json.dumps(calculate()))
    rendered=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output is None:
        need(json.loads(Path(__file__).resolve().with_suffix('.json').read_text())==result,
             'retained result agrees with core-height joint bridge')
        print(rendered,end='')
    else:
        args.output.write_text(rendered)

if __name__=='__main__':main()
