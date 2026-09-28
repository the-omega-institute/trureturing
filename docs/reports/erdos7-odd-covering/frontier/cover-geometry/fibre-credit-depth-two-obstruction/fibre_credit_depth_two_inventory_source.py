"""Exact actual-phase/primal consumer for one adaptively weighted common source."""
from fractions import Fraction as F
from itertools import product
from math import prod
from pathlib import Path
import hashlib,json

Q=(11,13,17,19)
R=F(566,49)

def need(ok,msg):
 if not ok:raise RuntimeError(msg)

def mul(xs):
 return prod(xs,start=F(1))

def calculate(witness_path=None):
 path=Path(witness_path) if witness_path is not None else Path(__file__).resolve().with_name('fibre_credit_depth_two_inventory_source_witnesses.json')
 raw=path.read_bytes();data=json.loads(raw);rows=[]
 pure=((3,0),(9,1),(5,0),(7,0))
 heads={'opposite_root':dict(pure+((15,11),(45,2),(21,1),(63,58),(35,3),(105,74),(315,187))),
        'same_root':dict(pure+((15,1),(45,22),(21,1),(63,16),(35,3),(105,74),(315,47)))}
 need([case['head'] for case in data['cases']]==list(heads),'two declared actual heads in order')
 for case in data['cases']:
  pairs=[(r['m'],r['a']) for r in case['originals']]
  originals=dict(pairs)
  labels={3**j*prod(q for i,q in enumerate((5,7)+Q) if D>>i&1) for j in range(3) for D in range(64)}-{1}
  need(len(originals)==len(pairs)==191 and set(originals)==labels,'actual complete191 distinct shallow labels')
  need(all(isinstance(m,int) and isinstance(a,int) and m>1 and m%2==1 and 0<=a<m for m,a in pairs),'canonical odd numerical phases')
  head={m:a for m,a in pairs if 315%m==0}
  need(head==heads[case['head']],'literal numerical phases of the declared head')
  need(len(head)==11 and all(originals[q]==0 for q in (3,5,7)+Q) and originals[9]==1,'actual pure roots')
  live=[x for x in range(315) if all(x%m!=a for m,a in head.items())]
  need(len(live)==(75 if case['head']=='opposite_root' else 85),'literal head survivors')
  t={};inventory={};forbidden={}
  for x in live:
   t[x]={};inventory[x]={};forbidden[x]={}
   for q in Q:
    events=[(m,a) for m,a in pairs if m%q==0 and 315%(m//q)==0 and m!=q]
    need(len(events)==11,'each outside axis has one eleven-label inventory')
    active=[(m,a) for m,a in events if x%(m//q)==a%(m//q)]
    roots={a%q for m,a in active}-{0}
    inventory[x][q]=len(active);forbidden[x][q]=sorted(roots)
    actual_live=q-1-len(roots)
    t[x][q]=q-1-inventory[x][q]
    need(actual_live>=max(0,t[x][q]),'actual load controls distinct live-root loss')
    # In these witnesses the global root choices realize the load bound simultaneously.
    need(actual_live==t[x][q] and t[x][q]>0,'same actual phase family realizes count profile on all rows')
  need(all(str(int(x))==x and type(v) is int for x,v in case['head_integer_weights'].items()),'literal integer head weights')
  weights={int(x):v for x,v in case['head_integer_weights'].items()}
  need(set(weights)<=set(live) and all(v>0 for v in weights.values()),'positive supported integer source weights')
  mass=sum(weights.values());p={x:F(v,mass) for x,v in weights.items()}
  need(sum(p.values(),F(0))==1,'one actual normalized head law')

  def fees(law):
   S=sum(law.values(),F(0));A=K=B=F(0);screens=[]
   for j,e,f,T in product(range(3),range(2),range(2),range(16)):
    m=3**j*5**e*7**f
    D=tuple(q for i,q in enumerate(Q) if T>>i&1)
    L=(F(5,4) if e else 1)*(F(7,6) if f else 1)*mul(F(q,q-1) for q in D)
    buckets={}
    for x,w in law.items():
     a=x%m;v=w*mul(F(1,t[x][q]) for q in D)
     buckets[a]=buckets.get(a,F(0))+v
    C=max(buckets.values(),default=F(0))
    A+=(L-1)*C
    if (m,T)!=(1,0):K+=L*C
    if len(D)>=2:B+=C
    screens.append(dict(head_modulus=m,outside_mask=T,cap=str(C),height_lift=str(L)))
   return S,A,B,K,R*(S-A-B)-K,screens

  S,A,B,K,gate,screens=fees(p)
  need(gate>0 and S==1,'strict positive common-source gate')
  D0=max(315*w*mul(F(q,t[x][q]) for q in Q) for x,w in p.items())
  density=49*gate/(616*D0)
  need(density>0,'positive actual survivor Haar lower')
  baseline={x:(F(1,4) if x%3==1 else F(1,6))/24*mul(F(t[x][q],q-1) for q in Q) for x in live}
  S0,A0,B0,K0,gate0,_=fees(baseline)
  need(gate0<0,'original fixed head weights fail this same product-source bound')
  # Explicit scaling embeds the new source in the old f<=U source class.
  scale=min(baseline[x]/p[x] for x in p)
  need(scale>0 and all(scale*p.get(x,F(0))<=baseline[x] for x in live),'one common reweighting is a permitted f<=U after scaling')
  head_inventory={str(q):{str(c):originals[c*q]%c for c in (3,5,7,9,15,21,35,45,63,105,315)} for q in Q}
  row=dict(head=case['head'],actual_original_count=191,actual_head_cells=len(live),primal_atoms=len(p),integer_mass=mass,
           fixed_head_phase_inventory=head_inventory,free_singleton_outside_root_slots=44,
           head_probability={str(x):str(w) for x,w in p.items()},all_rows_color_bound_exact=True,
           maximum_active_labels={str(q):max(inventory[x][q] for x in live) for q in Q},
           fixed_weight_mass=str(S0),fixed_weight_gate=str(gate0),fixed_weight_gate_decimal=float(gate0),
           source_mass=str(S),deep_debit=str(A),arbitrary132_multi_debit=str(B),complete_query_bound=str(K),
           gate=str(gate),gate_decimal=float(gate),source_Haar_density_cap=str(D0),Haar_density_lower=str(density),
           Haar_density_lower_decimal=float(density),common_admissible_scale=str(scale),screens=screens)
  rows.append(row)

 out=dict(passed=True,witness_sha256=hashlib.sha256(raw).hexdigest(),
          scope='Fixed actual11 head,44 singleton HEAD PROJECTIONS and4 outside pure roots. All44 singleton outside roots, every132 multi-support shallow phase and every additional deep or23/29-bearing phase may vary; whole family finite with distinct odd nonunit moduli, support in nine primes and v3<=2. For each actual root assignment, use one normalized conditional-product source with the SAME fixed head probability. Reciprocal count bounds control all its queries and its Haar density. No uniform arbitrary44-head-projection result and no exact optimizer claim.',cases=rows)
 return out


def main():
 import argparse
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--output',type=Path)
 args=parser.parse_args()
 result=json.loads(json.dumps(calculate()))
 rendered=json.dumps(result,indent=2,sort_keys=True)+'\n'
 if args.output is None:
  retained=json.loads(Path(__file__).resolve().with_suffix('.json').read_text())
  need(retained==result,'retained inventory source result agrees with exact reconstruction')
  print(rendered,end='')
 else:
  args.output.write_text(rendered)

if __name__=='__main__':main()
