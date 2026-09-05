"""Exact finite checks for GoldenBase4IntervalMachine.lean.

The checker reads the actual Lean table literals. It verifies every scalar
obligation with Fraction arithmetic using 8/5 < phi < 13/8 and phi^2=phi+1.
It does not execute Lean, certify elaboration, or test infinite correctness
by enumeration. The induction that consumes these obligations is in Lean.
Usage: python check_interval_source.py path/to/GoldenBase4IntervalMachine.lean
"""
from __future__ import annotations
import ast
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import re
import sys

LO, HI = F(8,5), F(13,8)

def require(ok: bool, msg: str) -> None:
    if not ok: raise ValueError(msg)

def table(text: str, name: str):
    m = re.search(r"def " + re.escape(name) + r"\s*:[\s\S]*?:=\s*!\[([\s\S]*?)\]", text)
    require(m is not None, f"missing table {name}")
    xs=ast.literal_eval('['+m.group(1)+']')
    require(len(xs)==21, f"bad table length {name}")
    return xs

def point(pair): return F(pair[0],4), F(pair[1],4)
def sub(x,y):return x[0]-y[0],x[1]-y[1]
def image(x,d):return x[0]-x[1]-2*d, -x[0]+d
def bounds(x):
    a,b=x;u=a+b*LO;v=a+b*HI
    return min(u,v),max(u,v)
def nonnegative(x): return bounds(x)[0]>=0
def positive_on_open(x):
    lo,hi=bounds(x);return lo>=0 and hi>0

def check(path: Path):
    text=path.read_text();names=['zeroTarget','oneTarget','output','lowerPair','upperPair','strip']
    A,B,O,L,U,M=(table(text,n) for n in names)
    require(A[0]==0 and O[0]==0,'initial anchors')
    require(all(isinstance(t,int) and 0<=t<21 for t in A+B),'state domains')
    require(all(isinstance(o,int) and 0<=o<4 for o in O),'output domains')
    comparisons=0;transitions=0
    for q in range(21):
        lo,hi=point(L[q]),point(U[q]);m=M[q];o=O[q]
        require(isinstance(m,int),'integer strip')
        if q:
            require(bounds(sub(hi,lo))[0]>=0 and hi!=lo,f'cell nonempty {q}')
            require(nonnegative(sub(lo,(F(m)+F(o,4),F(0)))),f'output lower {q}')
            require(nonnegative(sub((F(m)+F(o+1,4),F(0)),hi)),f'output upper {q}')
        else:
            require(lo==hi==(0,0) and m==o==0,'singleton')
        for d in (0,1):
            if q>=14 and d==1:continue
            t=A[q] if d==0 else B[q]
            require((t<14)==(d==0),f'typed target {q} {d}')
            if q:
                require(t!=0,f'interval to singleton {q} {d}')
                require(nonnegative(sub(image(hi,d),point(L[t]))),f'image lower {q} {d}')
                require(nonnegative(sub(point(U[t]),image(lo,d))),f'image upper {q} {d}')
                comparisons+=2
            elif t==0:
                require(image(lo,d)==(0,0),'singleton loop')
            else:
                require(positive_on_open(sub(image(lo,d),point(L[t]))),'singleton image lower')
                require(positive_on_open(sub(point(U[t]),image(lo,d))),'singleton image upper')
            transitions+=1
    require(LO*LO-LO-1<0 and HI*HI-HI-1>0,'root brackets')
    return {'status':'PASS','source_sha256':hashlib.sha256(text.encode()).hexdigest(),
            'states':21,'legal_transitions':transitions,'noninitial_endpoint_inequalities':comparisons,
            'output_cells':21,'phi_bracket':['8/5','13/8'],
            'floating_point_used':False,'unreachable_cut_assumption_used':False,
            'lean_executed':False,'power_minimality_claimed':False}

if __name__=='__main__':
    require(len(sys.argv)==2,'usage: check_interval_source.py Lean_file')
    print(json.dumps(check(Path(sys.argv[1])),indent=2))
