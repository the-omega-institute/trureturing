#!/usr/bin/env python3
"""Exact necessary token profiles and the uniform-root-cap feasibility boundary."""
from fractions import Fraction as F
from itertools import combinations_with_replacement
from pathlib import Path
import argparse,json

def require(test,msg):
    if not test:raise RuntimeError(msg)

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    rows=[]
    for n in (4,5):
      q=n-2
      for delta in range(3):
       for k in range(3):
        for z in combinations_with_replacement(range(1 if k==0 else 0,4),n-delta):
          Z=sum(z);c=63+7*(delta+k)+2*Z
          if c>82:continue
          p=sum(z[:q])
          if k==0:
            require(Z+3*delta<=9,'whole clipped root');consumer='B80.2'
          elif k==1:
            if p<=2:consumer='whole_projection_at_most3'
            else:
              require(n==5 and delta==0 and z in ((1,1,1,1,1),(1,1,1,1,2)),'four public+singleton fibres')
              consumer='B80.3'
          else:
            require(delta==0 and p<=1,'public2 cheapest whole projection')
            consumer='whole_projection_at_most3'
          rows.append(dict(n=n,delta=delta,k=k,z=z,c=c,consumer=consumer))
    tables=[]
    for M,rho in ((74,F(109,6)),(75,F(113,6)),(76,F(39,2))):
      ranges={str(t):[c for c in range(M,85) if c-(21-rho)*t<M] for t in (1,2,3)}
      feasible_total=4*rho>=M
      require(feasible_total==(M in (75,76)),'four-source-cut feasibility')
      tables.append(dict(M=M,rho=str(rho),ranges=ranges,source_capacity=str(4*rho),
        source_capacity_enough=feasible_total,conditional_bound=str(1+(373+12*rho)/M)))
    require(tables[0]['ranges']=={'1':[74,75,76],'2':list(range(74,80)),'3':list(range(74,83))},'74 partial cut range')
    require(F(37,2)>F(73,4),'uniform74 feasible and strict intervals disjoint')
    ceilings=[F(674,75),F(683,76),F(2865,319),F(4252,477),F(3572,397),F(2779,323)]
    require(max(ceilings)==F(3572,397)<9,'M75/76 final common bound')
    result=dict(scope='Necessary integer profiles and exact cap arithmetic only; source suppliers are separate ordinary proofs.',
      profiles=len(rows),capacity82_profiles=sum(r['c']==82 for r in rows),rows=rows,
      uniform_root_tests=tables,final75_76_bound='3572/397',maximum74_closed=False,PASS=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='rows'}))

if __name__=='__main__':main()
