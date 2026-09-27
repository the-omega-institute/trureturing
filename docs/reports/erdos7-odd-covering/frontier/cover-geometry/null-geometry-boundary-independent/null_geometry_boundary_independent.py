#!/usr/bin/env python3
"""Exact finite geometry/selector checks; no arithmetic covering claim."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
I=(0,1,2,4,5); J=tuple(j for j in range(20) if j!=5)
R=[set((0,1,2)),set((4,5))]
C=[set(range(5)),set(range(6,10)),set(range(10,15)),set(range(15,20))]
checks=0
def ck(b):
 global checks
 checks+=1
 if not b:raise RuntimeError('failed check '+str(checks))
def swap(x,y,z):return z if x==y else y if x==z else x
def menu(weights,blocks,deep):
 live=sorted(weights)
 return [[weights], [{l:weights[l] if l in B else F(0) for l in live} for B in blocks], [{l:weights[l] if l==t else F(0) for l in live} for t in live], [{l:deep if l==t else F(0) for l in live} for t in live]]
def screens(grid,w,v,rb,cb):
 xm=menu(w,rb,F(1));ym=menu(v,cb,F(4,5))
 return [max(sum((x[l]*y[m]*grid.get((l,m),0) for l,m in product(I,J)),F(0)) for x,y in product(xm[a],ym[b])) for a,b in product(range(4),repeat=2)]
geo=[]
for a,b in product((0,1),repeat=2):
 f=lambda l:swap(l,0,3) if a else l
 g=lambda m:swap(m,0,5) if b else m
 rb=[{l for l in I if f(l)//3==r} for r in range(2)]
 cb=[{m for m in J if g(m)//5==c} for c in range(4)]
 old={(l,m) for l,m in product(I,J) if not(l in R[0] and m in C[0])}
 new={(l,m) for l,m in product(I,J) if not(l in rb[0] and m in cb[0])}
 ck(old<=new);ck(len(new)==95-(3-a)*(5-b))
 for l,m,r,c,ell in product(I,J,range(2),range(4),I):
  n=int(l in R[r])+int(m in C[c])+int(l==ell)
  corrected=n+a*(-1 if r==0 else 1)*int(l==0)+b*((-1,1,0,0)[c])*int(m==0)
  actual=int(f(l)//3==r)+int(g(m)//5==c)+int(f(l)==f(ell))
  ck(corrected==actual and 0<=actual<=3)
 er=[R[0],R[1]|{0}] if a else R
 ec=[C[0],C[1]|{0},C[2],C[3]] if b else C
 for B in R+rb:ck(any(B<=E for E in er))
 for B in C+cb:ck(any(B<=E for E in ec))
 for B,E in product(er,er):ck(B==E or not B<=E)
 for B,E in product(ec,ec):ck(B==E or not B<=E)
 geo.append(dict(swaps=[a,b],nulls=[0 if a else 3,0 if b else 5],pulled_rows=list(map(sorted,rb)),pulled_columns=list(map(sorted,cb)),actual_live_cells=len(new),conservative_cells=len(old),discarded_cells=sorted(new-old),maximal_common_row_selectors=list(map(sorted,er)),maximal_common_column_selectors=list(map(sorted,ec))))
w={l:F(1 if l==2 else 2,9) for l in I}
v={m:F(3 if m==0 else 4,75) for m in J}
tA={(0,10):1,(4,10):1};tB={(1,10):1,(4,10):1}
toldA=screens(tA,w,v,R,C);toldB=screens(tB,w,v,R,C)
tnewA=screens(tA,w,v,[{1,2},{0,4,5}],C);tnewB=screens(tB,w,v,[{1,2},{0,4,5}],C)
ck(toldA==toldB);ck(tnewA[4]==F(16,675));ck(tnewB[4]==toldA[4]==F(8,675))
v2={m:F(3 if m==10 else 4,75) for m in J}
qA={(4,0):1,(4,6):1};qB={(4,1):1,(4,6):1}
qoldA=screens(qA,w,v2,R,C);qoldB=screens(qB,w,v2,R,C)
qnewA=screens(qA,w,v2,R,[{1,2,3,4},{0,6,7,8,9},C[2],C[3]])
qnewB=screens(qB,w,v2,R,[{1,2,3,4},{0,6,7,8,9},C[2],C[3]])
ck(qoldA==qoldB);ck(qnewA[1]==F(16,675));ck(qnewB[1]==qoldA[1]==F(8,675))
both={(0,6):1,(4,0):1,(4,6):1}
newR=[{1,2},{0,4,5}];newC=[{1,2,3,4},{0,6,7,8,9},C[2],C[3]]
old=screens(both,w,v2,R,C)[5];one3=screens(both,w,v2,newR,C)[5];one5=screens(both,w,v2,R,newC)[5];joint=screens(both,w,v2,newR,newC)[5]
ck((old,one3,one5,joint)==(F(8,675),F(16,675),F(16,675),F(24,675)))
crt=[]
for residues,star in [((1,2,1),147),((4,1,1),245)]:
 x=next(x for x in range(9*25*49) if all(x%m==r for m,r in zip((9,25,49),residues)))
 ck(x%star==1)
 crt.append(dict(residues=list(residues),moduli=[9,25,49],x=x,star_modulus=star,star_residue=1))
result=dict(status='PASS',check_count=checks,new_lean_verification=False,scope='Finite selector and activation geometry only; no new complete gate or arithmetic covering counterexample.',geometries=geo,ternary_counterpair=dict(A=list(tA),B=list(tB),old_screens=list(map(str,toldA)),new_A_screens=list(map(str,tnewA)),new_B_screens=list(map(str,tnewB))),quinary_counterpair=dict(A=list(qA),B=list(qB),old_screens=list(map(str,qoldA)),new_A_screens=list(map(str,qnewA)),new_B_screens=list(map(str,qnewB))),joint_query=dict(support=list(both),old=str(old),one_ternary=str(one3),one_quinary=str(one5),both=str(joint)),activation_witnesses=crt)
p=Path(__file__).with_suffix('.json');p.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(status='PASS',check_count=checks,live_cell_counts=[x['actual_live_cells'] for x in geo],activation_witnesses=crt)))
