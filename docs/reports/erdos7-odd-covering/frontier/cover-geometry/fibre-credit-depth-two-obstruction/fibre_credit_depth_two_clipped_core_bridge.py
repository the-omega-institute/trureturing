#!/usr/bin/env python3
"""Fixed-threshold exact consumer for three actual clipped-source scopes.
Literal Report741 hinges and Report744 partial caps refer to one canonical
old315 law. No numerical LP, optimizer or threshold-optimality premise.
"""
from fractions import Fraction as F
from math import prod
from pathlib import Path
from hashlib import sha256
import argparse,json

def check(v,m):
    if not v:raise ValueError(m)


DEPENDENCIES={'fibre_credit_depth_two_core_height_joint_bridge.json': '385db85e5f01bb21534c4e31ed9f089d0871360193236dab1f1fbc42bb08a491', 'fibre_credit_depth_two_old23_full_height.json': 'ca998ef3ce5e1043cbd1a78a4f9cd4306b12cfb781b219729aa916f0ba016ede'}

def calculate():
    directory=Path(__file__).resolve().parent
    for name,digest in DEPENDENCIES.items():
        check(sha256((directory/name).read_bytes()).hexdigest()==digest,'pinned general-clipping dependency: '+name)
    P=(11,13,17,19,23);threshold=(4,6,6,6,6)
    faces=((3,),(5,),(7,),(3,5),(3,7),(5,7),(3,5,7))
    data=(
     ('root1_same_other_column',77,'35/83 7/9 6/11 1/11 5/77 9/77 1/77','16/39','10/77'),
     ('root1_other_same_column',78,'5/12 63/82 41/78 7/78 5/78 3/26 1/78','32/79','5/39'),
     ('root1_other_other_column',78,'5/12 63/82 41/78 7/78 5/78 3/26 1/78','32/79','5/39'),
     ('root2_same_other_column',75,'35/76 21/26 37/75 7/75 1/15 3/25 1/75','2/5','2/15'),
     ('root2_other_same_column',74,'35/76 21/26 19/37 7/74 5/74 9/74 1/74','2/5','5/37'),
     ('root2_other_other_column',74,'35/76 21/26 19/37 7/74 5/74 9/74 1/74','2/5','5/37'))
    check(data[-1][1:]==data[-2][1:],'literal equal core contracts')
    inherited_core=json.loads((directory/'fibre_credit_depth_two_core_height_joint_bridge.json').read_text())['partial_bounds']
    inherited_hinges=json.loads((directory/'fibre_credit_depth_two_old23_full_height.json').read_text())['rows']
    check(len(inherited_core)==len(inherited_hinges)==len(data)==6,'same six inherited sources')
    for (shape,N,entries,h4,h6),core,hinges in zip(data,inherited_core,inherited_hinges):
        check(shape==core['shape']==hinges['shape'],'same canonical source identity')
        check(N==core['n315_min']==hinges['old315_Nmin'],'same cardinality contract')
        check(F(h4)==F(hinges['hinge_bounds'][4]) and F(h6)==F(hinges['hinge_bounds'][6]),'fourth and sixth complete-query hinges')
        for face,cap in zip(faces,map(F,entries.split())):
            key=','.join(map(str,face))
            check(cap==F(core['partial_query_caps'][key]['cap']),'same-source literal partial cap')
    expected={():('229886/596362975','69655678/70690165',2600),
              (19,23):('129274/1028859975','12926803/12991440',8000),
              (17,23):('45629/724786920','199093841/199595760',16000)}
    results=[]
    for full,(expected_density,expected_cost,friendly) in expected.items():
        flags=[int(p in full) for p in P]
        den=[p-a-b for p,a,b in zip(P,threshold,flags)]
        check(min(den)>0,'all positive clipping denominators')
        z=[F(1,p-1-b) for p,b in zip(P,flags)]
        s=[1-(a-1)*t for a,t in zip(threshold,z)]
        check(all(0<v<=1 for v in s),'actual positive clipping levels')
        query_caps=[v/t for v,t in zip(z,s)]
        check(query_caps==[F(1,d) for d in den],'normalized outside cap identity')
        pure_density=[F(p-b,p-1-b) for p,b in zip(P,flags)]
        outside_Haar=prod(D/t for D,t in zip(pure_density,s))
        check(outside_Haar==prod(F(p-b,d) for p,b,d in zip(P,flags,den)),'same raw outside domination')
        factor=prod(1+v for v in query_caps);rows=[]
        for shape,N,entries,h4,h6 in data:
            betas=list(map(F,entries.split()))
            lam=sum(v/prod(p-1 for p in S) for S,v in zip(faces,betas))
            hh=[F(h4)]+[F(h6)]*4
            losses=[h*u for h,u in zip(hh,query_caps)]
            Z0=1-sum(losses);raw_debit=lam*factor
            margin=Z0-raw_debit;D0=F(315,N)*outside_Haar
            check(margin>0 and Z0>0,'same-source actual positive remaining mass')
            rows.append({'shape':shape,'Nmin':N,'H4':h4,'H6':h6,'core_debit':str(lam),
                'source_loss_terms':list(map(str,losses)),'source_mass_lower':str(Z0),
                'raw_higher_core_debit':str(raw_debit),'total_cost':str(1-margin),
                'raw_remaining_mass':str(margin),'raw_Haar_cap':str(D0),
                'Haar_survivor_lower':str(margin/D0)})
        lower=min(F(r['Haar_survivor_lower']) for r in rows)
        cost=max(F(r['total_cost']) for r in rows)
        check(lower==F(expected_density) and cost==F(expected_cost),'fixed six-shape constants')
        check(lower>F(1,friendly),'simple positive density lower bound')
        results.append({'full_outside_primes':full,'thresholds':threshold,'denominators':den,
            'clipping_levels':list(map(str,s)),'query_multiplier':str(factor),
            'raw_outside_Haar_factor':str(outside_Haar),'rows':rows,
            'maximum_total_cost':str(cost),'uniform_Haar_survivor_lower':str(lower),
            'strict_simple_Haar_lower':f'1/{friendly}'})
    out={'scope':__doc__,'required_original_structure':'Core-shallow originals use at most one outside prime; each such axis may have all eleven nonunit core cofactors at every allowed exponent. Core-higher originals may use arbitrary outside subsets/heights within the stated carrier.',
         'results':results}
    out['dependency_hashes']=DEPENDENCIES
    return out

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args();result=json.loads(json.dumps(calculate()))
    rendered=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output is None:
        check(json.loads(Path(__file__).resolve().with_suffix('.json').read_text())==result,
              'retained result agrees with all eighteen clipped-source continuations')
        print(rendered,end='')
    else:args.output.write_text(rendered)

if __name__=='__main__':main()
