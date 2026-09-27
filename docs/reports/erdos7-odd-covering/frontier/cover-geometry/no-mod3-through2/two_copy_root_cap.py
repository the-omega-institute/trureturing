#!/usr/bin/env python3
"""First-level pure-5 cylinder cap in the fixed PA comparison.
Consumes the pinned four-corner ledger; full tails enter through means.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse
import json,hashlib

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--input',type=Path,default=Path(__file__).with_name('two_copy_pure_anchor.json'))
parser.add_argument('--output',type=Path)
args=parser.parse_args()
SRC=args.input
try:
 raw=SRC.read_bytes()
except OSError as error:
 parser.error(str(error))
source_hash=hashlib.sha256(raw).hexdigest()
if source_hash!='45939ae4a727d63d0e91d836b8519eea84482f8c06cfe46eb96cb082a2f78a53':
 parser.error('input must be the pinned PA ledger')
D=json.loads(raw); sigma=F(1,125); T=F(257,51)
def req(v,msg):
 if not v:raise ValueError(msg)
def f(x):return F(*x)
def enc(x):
 if isinstance(x,F):return [x.numerator,x.denominator]
 if isinstance(x,dict):return {k:enc(v) for k,v in x.items()}
 if isinstance(x,list):return [enc(v) for v in x]
 return x

def moments(specs,t):
 mean=F(1);W=F(1);low={1:F(1)}
 for p,c,u,shift in specs:
  atoms={1:1-u-c/F(p)+shift}
  atoms.update({n:c*F(p-1,p**n)-(shift if n==2 else 0) for n in range(2,t)})
  req(min(atoms.values())>=0,'negative atom')
  mean*=1-u+c/F(p-1)-shift;W*=1-u
  new={}
  for n,m in low.items():
   for k,w in atoms.items():
    if n*k<t:new[n*k]=new.get(n*k,F(0))+m*w
  low=new
 return mean,W,low

def hinge(stats,t):
 mean,W,low=stats
 return mean-t*W+sum((t-n)*m for n,m in low.items())

def correction(rest,t):
 # C_t = integral ((2N-t)+ - (N-t)+) d(rest).
 # All t here are 2, 3, or 4; high tails are inside the full mean.
 req(t in (2,3,4),'threshold')
 mean,_,low=moments(rest,t)
 return mean-sum((min(2*n,t)-min(n,t))*m for n,m in low.items())

req(D['reference_primes']==[5,7,11,13,17,19] and D['stage_thresholds']==[2,2,4,4] and D['query_threshold']==3,'unexpected retained schedule')
corners=[]
for old in D['corners']:
 u,v=map(f,old['pure_removed_masses'])
 rest=[(7,F(1),v,F(0))];spec5=(5,F(1),u,sigma)
 mass=f(old['anchor_mass_lower']);stages=[]
 for row in old['stages']:
  q=row['prime'];t=row['threshold'];C=f(row['cap'])
  corr=correction(rest,t)
  H=f(row['hinge'])-sigma*corr
  req(H==hinge(moments([spec5]+rest,t),t),'shift and direct hinge disagree')
  req(H>=0,'negative hinge')
  loss=F(2,q-1-2*t)*H;mass-=loss
  stages.append({'prime':q,'threshold':t,'cap':C,'old_hinge':f(row['hinge']),'unit_shift_hinge_improvement':corr,'new_hinge':H,'loss':loss,'mass_lower':mass})
  rest.append((q,C,F(0),F(0)))
 corr=correction(rest,3);phi=f(old['query_hinge'])-sigma*corr
 req(phi==hinge(moments([spec5]+rest,3),3),'final shift and direct hinge disagree')
 req(mass>0 and phi>=0,'bad final budget')
 B=2+phi/mass
 corners.append({'pure_removed_masses':[u,v],'stages':stages,'mass_lower':mass,'query_hinge':phi,'query_upper':B,'density_upper':9/mass,'target_margin':T-B})
B=max(c['query_upper'] for c in corners);alpha=min(c['mass_lower'] for c in corners);Phi=corners[max(range(4),key=lambda i:corners[i]['query_upper'])]['query_hinge']
req(B<T,'candidate does not cross target')
out={'source_sha256':source_hash,'sigma':sigma,'target':T,'corners':corners,'mass_lower':alpha,'worst_corner_query_hinge':Phi,'query_upper':B,'target_margin':T-B,'density_upper':9/alpha}
content=json.dumps(enc(out),indent=2)+'\n'
if args.output is None:
 print(content,end='')
else:
 args.output.write_text(content,encoding='utf-8')
