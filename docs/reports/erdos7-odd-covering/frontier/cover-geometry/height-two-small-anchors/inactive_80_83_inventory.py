#!/usr/bin/env python3
"""Necessary exact80/exact83 cut profile inventory; no actual realizability claim."""
from itertools import combinations_with_replacement,product
from collections import Counter
from pathlib import Path
import argparse,json

def require(t,m):
    if not t:raise RuntimeError(m)

def roots(n,k):
    q=n-2
    for delta in range(3):
        for z in combinations_with_replacement(range(1 if k==0 else 0,4),n-delta):
            forward=7*delta+2*sum(z)
            if forward<=20:yield {'n':n,'q':q,'delta':delta,'z':z,'Z':sum(z),'p':sum(z[:q]),'forward':forward}

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    two=[]
    for kind,n,m in (('FF',5,5),('GF',4,5)):
        for k in range(6):
            for a,b in product(roots(n,k),roots(m,k)):
                if kind=='FF' and (a['delta'],a['z'])>(b['delta'],b['z']):continue
                if a['p']+b['p']<9-k:continue
                cost=42+7*k+a['forward']+b['forward']
                if cost!=80:continue
                require(k==0,'new exact80 public pattern')
                witnesses=[i for i,r in enumerate((a,b)) if r['Z']+3*r['delta']<=9]
                require(witnesses,'exact80 clipped-cardinality witness')
                two.append({'kind':kind,'cost':cost,'k':k,'roots':[a,b],'witness_root':witnesses[0]})
    three=[];uncovered=[]
    for n in (4,5):
        for k in range(3):
            for r in roots(n,k):
                if 63+7*k+r['forward']!=83:continue
                row={'cost':83,'k':k,'root':r}
                if k==0:
                    if r['Z']+3*r['delta']<=9:row['consumer']='clipped_cardinality9'
                    elif n==5 and r['z'].count(1)>=3:row['consumer']='three_singletons'
                    elif n==5 and r['z'].count(1)>=2 and r['z'].count(2)>=2:row['consumer']='full1122'
                    elif n==4 and r['z'].count(1)>=1 and sum(v<=2 for v in r['z'])>=2:row['consumer']='gap12'
                    elif n==4 and r['z'].count(2)>=3:row['consumer']='gap222'
                    else:row['consumer']='open_profile';uncovered.append(row)
                else:
                    require(r['p']+k<=3 or (n==5 and r['z'] in ((1,1,1,1,1),(1,1,1,1,2))),'new exact83 public pattern')
                    row['consumer']='existing_small_anchor_or_public_singletons'
                three.append(row)
    expected={(4,(1,3,3,3)),(4,(2,2,3,3)),(5,(1,1,2,3,3)),(5,(1,2,2,2,3)),(5,(2,2,2,2,2))}
    require({(x['root']['n'],x['root']['z']) for x in uncovered}==expected,'five exact83 unresolved profiles')
    result={'scope':'Finite necessary normalized cut shapes only. The exact80 consumers use unchanged complete fibres. The five exact83 open shapes are not claimed realizable or impossible.','two_inactive_exact80':two,'three_inactive_exact83':three,'unresolved_exact83':uncovered,'two_exact80_count':len(two),'three_exact83_count':len(three),'unresolved_exact83_count':len(uncovered),'PASS':True}
    args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k in ('scope','two_exact80_count','three_exact83_count','unresolved_exact83_count','PASS')}));print([(x['root']['n'],x['root']['z']) for x in uncovered])

if __name__=='__main__':main()
