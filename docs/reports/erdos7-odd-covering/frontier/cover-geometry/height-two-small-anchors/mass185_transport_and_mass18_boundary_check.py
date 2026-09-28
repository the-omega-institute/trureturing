#!/usr/bin/env python3
"""Exact arithmetic for half-integral mass18.5 transport and the mass18 obstruction."""
import argparse
from fractions import Fraction as F
from pathlib import Path
from itertools import product
import json

def require(t,m):
    if not t:raise RuntimeError(m)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    inventory=[]
    for a,b,c,Y in product(range(6),range(8),range(36),range(6)):
        if b==0 and Y:continue
        if 12*a+14*b+4*c-Y==37:inventory.append((a,b,c,Y))
    expected=[(0,1,6,1),(1,1,3,1),(2,1,0,1),(0,1,7,5),(1,1,4,5),(2,1,1,5),(0,2,3,3),(1,2,0,3),(0,3,0,5)]
    require(set(inventory)==set(expected),'complete necessary cut inventory')
    require(F(22965,76)<F(1835,6)<306,'scaled and two-column bounds')
    require(F(4875,16)<F(1835,6),'three-column bound')
    tight=[];other=[]
    for even,subset in product(range(0,62,2),(F(0),F(7),F(11,2),F(25,2))):
        capacity=even+subset
        if capacity==F(25,2):tight.append((even,str(subset)))
        if capacity>F(25,2):other.append(capacity)
    require(tight==[(0,'25/2')] and min(other)==13,'two-column tight-cut parity and gap')
    require(3*F(1,6)<=F(1,2),'two-column entry reduction budget')
    require(F(19)-7*F(1,16)>F(37,2),'capacity19 entry reduction')
    require(F(39,2)-15*F(1,16)>F(37,2),'larger-cut entry reduction')
    cap19=[]
    for a,b,c,Y in product(range(6),range(4),range(16),range(6)):
        if b==0 and Y:continue
        if 12*a+14*b+4*c-Y==38:cap19.append((a,b,c,Y))
    require(all(b>=1 and c<=7 for a,b,c,Y in cap19),'all capacity19 arithmetic shapes')
    E={(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(4,0),(4,1),(4,3),(4,4)}
    x={p:F(2) for p in E}
    x[4,0]=x[4,1]=F(1)
    y=[F(0),F(2),F(0),F(0),F(0),F(1),F(0)]
    z=[F(1,2),F(0),F(0),F(0),F(0)]
    rows=[sum(x.get((i,j),0) for j in range(7)) for i in range(5)]
    cols=[sum(x.get((i,j),0) for i in range(5)) for j in range(7)]
    require(sum(x.values())==18 and sum(y)==3 and sum(z)==F(1,2),'local and external totals')
    require(all(v<=2 for v in x.values()),'entry caps')
    require(all(r<=6 and r+zz<=7 for r,zz in zip(rows,z)),'internal and original child caps')
    require(all(c+yy<=7 for c,yy in zip(cols,y)),'residual fine caps')
    crossing={p for p in E if p[0]!=4}
    require(len(crossing)==6 and 6+2*len(crossing)==18,'matching local cut')
    forced={p:F(2) for p in crossing}
    residual={j:7-y[j]-sum(v for (i,k),v in forced.items() if k==j) for j in (0,1,3,4)}
    residual={j:min(F(2),v) for j,v in residual.items()}
    require(residual=={0:F(1),1:F(1),3:F(2),4:F(2)} and sum(residual.values())==6,'unique remaining row')
    scores=[[20*rows[i]+20*cols[j]+25*x.get((i,j),0)+5*z[i]+5*y[j] for j in range(7)] for i in range(5)]
    require(scores[0][0]==F(625,2) and max(map(max,scores))==F(625,2),'forced bad fine score')
    charge=3*F(37,2)+3*21+9*18+scores[0][0]
    require(charge==593>8*74,'bad coherent charge')
    require(F(1)+F(1183,148)==F(1331,148)==9-F(1,148),'conditional common-law margin')
    require(285+F(1835,6)<591,'mass18.5 coherent charge')
    require(8*F(37,2)+3*F(41,2)+4*18+310==F(1183,2),'additional column cap bound')
    result={'scope':'Arithmetic cut inventory and capacity-reduction checks plus one local unique-flow counterexample. No enumeration of complete original sources, no Lean.','mass185_cut_inventory':sorted(inventory),'capacity19_cut_shapes':cap19,'mass185_score_bound':'1835/6','mass18_support':sorted(E),'unique_mass18_flow':[{'row':i,'column':j,'mass':str(v)} for (i,j),v in sorted(x.items())],'external_z':list(map(str,z)),'external_y':list(map(str,y)),'rows':list(map(str,rows)),'columns':list(map(str,cols)),'fine_scores':[[str(v) for v in row] for row in scores],'forced_coherent_charge':str(charge),'conditional_gamma_bound':'1331/148','PASS':True}
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k in ('scope','mass185_score_bound','forced_coherent_charge','conditional_gamma_bound','PASS')}))

if __name__=='__main__':main()
