#!/usr/bin/env python3
"""Exact full-tail constants for normalized all-3-rooted source construction."""
from fractions import Fraction as F
from itertools import product
from math import prod
from pathlib import Path
import argparse,hashlib,json
P=(3,5,7,11,13,17,19)
T={5:0,7:1,11:2,13:4,17:4,19:6}
C={3:F(2),**{p:F(p-1,p-2-T[p]) for p in P[1:]}}
checks={}
def require(name,b):
 if name in checks: raise ValueError('duplicate check')
 checks[name]=bool(b)
 if not b:raise ValueError(name)
def atom(p,k):
 return 1-C[p]/p if k==0 else C[p]*F(p-1,p**(k+1))
def product_low(ps,limit):
 table={1:F(1)}
 for p in ps:
  out={}
  for v,w in table.items():
   for n in range(1,limit//v+1):
    out[v*n]=out.get(v*n,F(0))+w*atom(p,n-1)
  table=out
 return table
def rooted_low(ps,limit):
 # Zero belongs to K3 only. Every (1+Kp) is strictly positive.
 D=product_low(ps,limit)
 return {0:atom(3,0),**{m:sum((w*atom(3,m//v) for v,w in D.items() if m%v==0),F(0)) for m in range(1,limit+1)}}
def rooted_hinge(ps,t):
 mean=C[3]/2*prod(1+C[p]/(p-1) for p in ps)
 low=rooted_low(ps,max(0,t-1))
 return mean-t+sum((t-m)*w for m,w in low.items() if m<t),mean,low
rows=[];old=[]
for q in P[1:]:
 t=T[q];H,mean,low=rooted_hinge(old,t)
 charge=H/(q-2-t)
 require('valid_cap_'+str(q),0<C[q]/q<1)
 require('kernel_coefficient_'+str(q),C[q]/(q-1)==F(1,q-2-t))
 rows.append({'prime':q,'threshold':t,'delta':F(t,q-2),'cap':C[q],'old_primes':list(old),'old_mean':mean,'rooted_hinge':H,'low_rooted_atoms':low,'charge':charge})
 old.append(q)
beta=sum((r['charge'] for r in rows),F(0));s=1-beta
low=product_low(P,10);mean=prod(1+C[p]/(p-1) for p in P)
hinges={tau:mean-1-tau+sum((1+tau-n)*w for n,w in low.items() if n<1+tau) for tau in range(11)}
B=hinges[5];R=5+B/s;target=F(565,51)
require('first_charge',rows[0]['charge']==F(1,3))
require('second_charge',rows[1]['charge']==F(1,6))
for q,num in ((11,843),(13,568),(17,521),(19,437)):
 require('rounded_charge_'+str(q),next(r['charge'] for r in rows if r['prime']==q)<F(num,10000))
require('rounded_total_charge',beta<F(7369,10000)<F(59,80))
require('positive_survivor',s>F(21,80))
require('full_query_mean',mean==F(30720,5929))
require('rounded_query_hinge',B<F(63,40))
require('common_law_query_below_eleven',R<11<target)
require('best_of_11_query_thresholds',min((tau+H/s,tau) for tau,H in hinges.items())[1]==5)
# Independent atom reconstruction from all ordered factor tuples with product<=10.
independent={n:F(0) for n in range(1,11)}
def recurse(i,value,mass):
 if i==len(P):
  independent[value]+=mass;return
 for factor in range(1,10//value+1):recurse(i+1,value*factor,mass*atom(P[i],factor-1))
recurse(0,1,F(1))
for n in low:require('low_atom_independent_'+str(n),low[n]==independent[n])
# Haar density cap of the single normalized preconditioning source.
Lambda=prod(C.values());haar=s/Lambda
reserve=1-(1+R)*F(51,616);post=haar*reserve
require('fresh_extension_positive',post>0)
result={'scope':'Distinct nonunit P-smooth original labels, all mixed labels divisible by3; arbitrary fixed residues, all finite heights. One normalized sequential law followed by one full-survivor conditioning. Ordinary proof required, no Lean.', 'primes':P,'caps':C,'rows':rows,'total_original_charge':beta,'survivor_probability_lower':s,'full_query_mean':mean,'low_product_atoms':low,'hinges':hinges,'hinge_tau5':B,'query_upper':R,'target':target,'query_gap':target-R,'preconditioning_Haar_density_cap':Lambda,'Haar_survivor_lower':haar,'fresh_23_29_relative_reserve':reserve,'fresh_23_29_Haar_lower':post,'extra_same_law_charge_budget':1-B/(target-5)-beta,'checks':checks,'passed_count':len(checks)}
def enc(x):
 if isinstance(x,F):return str(x)
 raise TypeError(type(x).__name__)
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'));args=p.parse_args();args.output.write_text(json.dumps(result,indent=2,default=enc)+'\n')
print(json.dumps({k:result[k] for k in ('total_original_charge','survivor_probability_lower','hinge_tau5','query_upper','Haar_survivor_lower','fresh_23_29_Haar_lower','extra_same_law_charge_budget','passed_count')},indent=2,default=enc))
print(hashlib.sha256(args.output.read_bytes()).hexdigest())
