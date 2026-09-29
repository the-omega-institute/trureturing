"""Construct one global coloring that realizes every row's maximum unary load."""
from itertools import product
from math import prod
from pathlib import Path
import json,random

C=(3,5,7,9,15,21,35,45,63,105,315)
Q=(11,13,17,19)

def need(ok,msg):
 if not ok:raise RuntimeError(msg)

def color(alpha,q):
 if q>=13:return {c:i+1 for i,c in enumerate(C)},None
 need(q==11,'declared prime menu')
 u=alpha[315]
 bad=[c for c in C[:-1] if alpha[c]!=u%c]
 duplicate=bad[0] if bad else 3
 roots={315:1,duplicate:1}
 remaining=iter(range(2,11))
 for c in C:
  if c not in roots:roots[c]=next(remaining)
 return roots,duplicate

def crt(c,a,q,b):
 return (a+c*((b-a)*pow(c,-1,q)%q))%(c*q)

def check(alpha,q):
 roots,pair=color(alpha,q)
 family=[(c*q,crt(c,alpha[c],q,roots[c])) for c in C]
 need(len({m for m,a in family})==11 and all(0<=a<m and a%c==alpha[c] for c,(m,a) in zip(C,family)),'one actual complete numerical phase list')
 n=[];r=[]
 for u in range(315):
  active=[(m,a) for m,a in family if u%(m//q)==a%(m//q)]
  n.append(len(active));r.append(len({a%q for m,a in active}-{0}))
  need(r[-1]==min(n[-1],q-1),'simultaneous actual maximum distinct-root profile')
 need([u for u in range(315) if r[u]==q-1]==[u for u in range(315) if n[u]>=q-1],'dead rows precisely match the declared count cut')
 return dict(duplicate_cofactor=pair,actual_originals=[dict(m=m,a=a) for m,a in family],maximum_n=max(n),maximum_r=max(r),dead_rows=[u for u in range(315) if r[u]==q-1])

def calculate():
    # Check the actual arithmetic in the only collision class for every anchor,
    # cofactor, and alternative head phase. This is independent of other slots.
    pair_checks=0
    for u in range(315):
     for c in C[:-1]:
      for a in range(c):
       coherent=(a==u%c)
       intersection=[x for x in range(u,315,315) if x%c==a]
       need(intersection==([u] if coherent else []),'315 cylinder is a singleton; every incompatible merged pair is disjoint')
       pair_checks+=1

    # Combinatorial root-count verification: a duplicated color subtracts exactly
    # one fromn when both duplicated events hit. In the coherent case both hitting
    # forces all remaining nine events to hit; otherwise both never hit.
    indicator_checks=0
    for a,b,others in product(range(2),range(2),product(range(2),repeat=9)):
     n=a+b+sum(others);r=int(bool(a or b))+sum(others)
     if not(a and b):need(r==min(n,10),'disjoint duplicate events have no lost distinct root')
     elif all(others):need(r==min(n,10),'one coherent eleven-active row loses precisely one root')
     indicator_checks+=1

    coherent_checks=0;random_checks=0;rng=random.Random(3151113);examples=[]
    for u in range(315):
     alpha={c:u%c for c in C}
     result=check(alpha,11)
     need(result['dead_rows']==[u],'all coherent configurations have exactly one dead11 row')
     coherent_checks+=1
     if u in (0,4,214):examples.append(dict(kind='coherent',head_phases=alpha,prime=11,**result))
    for i in range(256):
     alpha={c:rng.randrange(c) for c in C}
     for q in Q:
      result=check(alpha,q);random_checks+=1
      if i==0:examples.append(dict(kind='incoherent',head_phases=alpha,prime=q,**result))

    out=dict(passed=True,complete_anchor_cofactor_phase_checks=pair_checks,root_indicator_checks=indicator_checks,
             all_coherent_phase_layouts=coherent_checks,additional_actual_global_phase_layouts=random_checks,examples=examples,
             scope='For every global eleven-cofactor head phase inventory, the proved construction realizesr_q(u)=min(n_q(u),q-1) simultaneously at all315 head rows using one full numerical phase per original. This is a count-profile statement; it does not assert simultaneous equality of query-cylinder caps that discarded live-root indicators.')
    return out


def main():
    import argparse
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    args=parser.parse_args()
    result=json.loads(json.dumps(calculate()))
    rendered=json.dumps(result,indent=2,sort_keys=True)+"\n"
    if args.output is None:
        retained=json.loads(Path(__file__).resolve().with_suffix(".json").read_text())
        need(retained==result,"retained result agrees with exact global phase reconstruction")
        print(rendered,end="")
    else:
        args.output.write_text(rendered)


if __name__=="__main__":main()
