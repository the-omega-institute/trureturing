#!/usr/bin/env python3
"""Actual375 source with own H descendants and full E5 support on Q."""
from pathlib import Path
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import importlib.util,json

def module(n,p):
 s=importlib.util.spec_from_file_location(n,p);require(s is not None and s.loader is not None,'Readable provider')
 m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
def require(p,m):
 if not p:raise ValueError(m)
def encode(x):
 if isinstance(x,F):return str(x)
 if isinstance(x,dict):return {str(k):encode(v)for k,v in x.items()}
 if isinstance(x,(tuple,list)):return [encode(v)for v in x]
 return x
def zero_induction(data,heavy):return data['_source'].zero_induction(data,heavy)

def build(base):
 _old=module('sharp375_actual315',base/'frontier/j_aligned_retained375_source.py')
 d=_old.build(base);d['_source']=_old;lp=d['lp'];before=d['model'];n=len(lp.rows)
 require((lp.nvars,n,len(lp.equalities))==(12941,30454,23),'Exact actual375 predecessor')
 # AE3: on H, Lambda=eta tensor Haar-zeta, with zeta=I27 tensor Haar_H.
 # zeta has mass 1/135 and quinary descendant restriction 5^{-(b-1)}.
 # At (L,H), this sharpens E=1/9 to E=2/27 only. Own ternary
 # descendants retain the original safe caps and CRT intersections.
 g=F(1,135);E=F(1,9)-5*g;require(E==F(2,27),'Literal H descendant coefficient')
 sharp=[]
 def add(label,row,bound=F(0)):
  lp.rows.append({c:a for c,a in row.items()if a});lp.rhs.append(bound)
  sharp.append({'label':label,'row':len(lp.rows)-1,'rhs':bound})
 cell=14;start=16*cell
 for label,bit,col in((25,0,404),(75,2,419)):
  add('H-own-'+str(label),{**{start+m:F(1)for m in range(16)if m>>bit&1},col:-E/25})
 for label,bit,col,den in((125,1,6505,125),(225,2,6520,25)):
  add('H-own-'+str(label),{**{876+400*(st-1)+start+m:F(1)for st,m in product(range(1,8),range(16))if st>>bit&1},col:-E/den})
 add('H-own-375',{**{6531+400*st+start+m:F(1)for st,m in product(range(8),range(16))},12940:-E/125})
 # AE2 equality in each forbidden raw cap forces its carrier to Q:
 # pure 5^b (b>=2): P,A,B,H coefficients <1/2=Q;
 # 3*5^b: wrong root<=1/6 and root1 P,A,B,H coefficients <1/3=Q.
 # E5 includes this entire forbidden family, not merely selected tests.
 pure=(F(0),F(1,6),F(7,18),F(1,2)-5*g)
 alpha=(F(0),F(0),F(2,9),F(1,3)-5*g)
 require(max(pure)<F(1,2)and max(alpha)<F(1,3)and F(1,6)<F(1,3),'Strict exclusions for every forbidden b>=2')
 for c,s in product(range(5),range(5)):
  if s!=3:add('E5-supported-Q-'+str(c)+'-'+str(s),{850+5*c+s:F(1)})
 require(len(lp.rows)==30479 and len(sharp)==25,'Five own H profiles and twenty full E5 support rows')
 lp.columns=[[]for _ in range(lp.nvars)];lp.eqcolumns=[[]for _ in range(lp.nvars)]
 for i,row in enumerate(lp.rows):
  for c,a in row.items():lp.columns[c].append((i,a))
 for i,row in enumerate(lp.equalities):
  for c,a in row.items():lp.eqcolumns[c].append((i,a))
 lp.checker=d['codec'].IntegerDualChecker(lp);lp.check_dual=lp.checker.check
 d.update(model={'variables':lp.nvars,'inequalities':len(lp.rows),'equalities':len(lp.equalities),
  'rows_sha256':sha256(json.dumps(encode([lp.rows,lp.rhs,lp.equalities,lp.erhs]),sort_keys=True,separators=(',',':')).encode()).hexdigest(),
  'actual375_predecessor':before,'appended_necessary_rows':sharp,'own_H_descendant_coefficient':E,
  'strict_forbidden_non_Q_coefficients':{'pure5':pure,'root1_alpha5':alpha,'wrong_root_alpha5':F(1,6)}})
 return d
