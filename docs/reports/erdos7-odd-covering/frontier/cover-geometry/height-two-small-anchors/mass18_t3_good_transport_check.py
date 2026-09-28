#!/usr/bin/env python3
"""Exact cut-inventory and mixture checks for T3-good mass18 transport."""
import argparse
from fractions import Fraction as F
from itertools import product,combinations
from pathlib import Path
import json

def require(t,m):
    if not t:raise RuntimeError(m)

def actual_local_control():
    support={(i,j) for i in range(5) for j in range(2)}|{(i,2) for i in range(3)}
    initial={(0,0):F(2),(0,1):F(2),(0,2):F(2),
        (1,0):F(2),(1,1):F(1),(1,2):F(2),
        (2,0):F(2),(2,2):F(2),(3,0):F(1),(3,1):F(2)}
    y=(F(0),F(2),F(0),F(0),F(0),F(1),F(0))
    z=(F(1,2),F(0),F(0),F(0),F(0))
    for rows in combinations(range(5),3):
        require(len({j for i,j in support if i in rows})>=3,'actual complete T3 neighborhood')
    repair=dict(initial);repair[0,0]-=F(1,2);repair[4,0]=F(1,2)
    mixture={p:F(5,7)*initial.get(p,0)+F(2,7)*repair.get(p,0) for p in support}
    recorded=[]
    for name,flow in (('initial',initial),('repair',repair),('mixture',mixture)):
        require(set(flow)<=support and sum(flow.values())==18,'actual support and mass')
        require(all(0<=w<=2 for w in flow.values()),'entry capacities')
        rows=[sum(w for (i,j),w in flow.items() if i==r) for r in range(5)]
        cols=[sum(w for (i,j),w in flow.items() if j==c) for c in range(7)]
        require(all(r<=6 and r+zz<=7 for r,zz in zip(rows,z)),'same row caps and external vector')
        require(all(c+yy<=7 for c,yy in zip(cols,y)),'same fine caps and external vector')
        scores=[[20*rows[i]+20*cols[j]+25*flow.get((i,j),0)+5*z[i]+5*y[j]
            for j in range(7)] for i in range(5)]
        recorded.append(dict(name=name,flow=[[i,j,str(w)] for (i,j),w in sorted(flow.items())],
            rows=list(map(str,rows)),columns=list(map(str,cols)),
            scores=[[str(s) for s in row] for row in scores],maximum=str(max(map(max,scores)))))
    require(F(recorded[0]['maximum'])==F(625,2),'initial bad query is present')
    require(F(recorded[1]['maximum'])==290,'explicit repaired query values')
    require(F(recorded[2]['maximum'])==F(4285,14)<=F(2175,7),'one actual mixture bounds every cell')
    minima=[]
    for reduction in (F(0),F(1,2)):
        capacities=[]
        for rowside in range(32):
            for colside in range(128):
                c=6*sum(not(rowside>>i&1) for i in range(5))
                c+=sum(7-y[j] for j in range(7) if colside>>j&1)
                c+=sum(2-(reduction if (i,j)==(0,0) else 0)
                    for i,j in support if rowside>>i&1 and not(colside>>j&1))
                capacities.append(c)
        require(len(capacities)==4096 and min(capacities)==18,'complete local cut check')
        minima.append(dict(entry_reduction=str(reduction),minimum=str(min(capacities)),
            cut_count=len(capacities),minimum_cut_count=capacities.count(min(capacities))))
    return dict(scope='One actual T3-good local support, not a complete original blocker.',
        support=sorted(support),external_y=list(map(str,y)),external_z=list(map(str,z)),
        T3_triples=10,flows=recorded,cut_checks=minima)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    inventory=[]
    for a,b,c,Y in product(range(6),range(8),range(36),range(7)):
        if b==0 and Y:continue
        if 12*a+14*b+4*c-Y==36:inventory.append((a,b,c,Y))
    expected=[(0,0,9,0),(1,0,6,0),(2,0,3,0),(3,0,0,0),
       (0,1,6,2),(1,1,3,2),(2,1,0,2),
       (0,1,7,6),(1,1,4,6),(2,1,1,6),
       (0,2,2,0),(0,2,3,4),(1,2,0,4),(0,3,0,6)]
    require(set(inventory)==set(expected),'complete mass18 necessary inventory')
    possible=[]
    for a,b,c,Y in inventory:
        for t in range(1,c+1):
            if 2*t<=7<=2*t+2*a:possible.append((a,b,c,Y,t))
    require(set(possible)=={(1,0,6,0,3),(1,1,3,2,3),(1,1,4,6,3),(2,0,3,0,2),(2,0,3,0,3)},'bad-entry cut candidates')
    require(F(37,2)-F(1,2)==18,'half-unit reduction cut margin')
    bad=F(625,2);good=F(310);repair=F(300);bound=F(2175,7)
    require(F(5,7)*good+F(2,7)*bad==bound,'old-good mixed score')
    for b in (1,2):require(bad-F(2,7*b)*(bad-repair)<=bound,'each old-bad mixed score')
    require(F(22535,74)<bound<F(623,2),'higher-mass and target comparisons')
    require(F(561,2)+bound==F(8277,14),'mass18 coherent charge')
    require(F(8277,14)>591 and F(8277,14)>285+F(1835,6),'global maximum')
    require(1+F(8277,14)/74==F(9313,1036)==9-F(11,1036),'common-law strict margin')
    result={'scope':'Exact necessary cut inventory, bad-entry cut cases, half-unit capacity reduction budget, and convex-mixture arithmetic. The actual-support T3 proof is in the manuscript; no complete-source enumeration or Lean.','cut_inventory':sorted(inventory),'possible_bad_entry_cut_cases':sorted(possible),'fine_score_bound':str(bound),'common_law_bound':'9313/1036','strict_margin':'11/1036','PASS':True}
    result['actual_local_control']=actual_local_control()
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('cut_inventory','possible_bad_entry_cut_cases','actual_local_control')}))

if __name__=='__main__':main()
