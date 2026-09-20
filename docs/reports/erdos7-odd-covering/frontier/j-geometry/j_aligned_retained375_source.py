#!/usr/bin/env python3
"""Complete retained375 interface for the actual aligned equality source.

Only pure head and seven-kernel functions escape the original constructor;
its saturated auxiliary geometry is deliberately not part of this interface.
"""
from fractions import Fraction as F
from pathlib import Path
from hashlib import sha256
import importlib.util,json

def module(n,p):
 s=importlib.util.spec_from_file_location(n,p);require(s is not None and s.loader is not None,'Readable original source')
 m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
def require(p,m):
 if not p:raise ValueError(m)
def encode(x):
 if isinstance(x,F):return str(x)
 if isinstance(x,dict):return {str(k):encode(v)for k,v in x.items()}
 if isinstance(x,(tuple,list)):return [encode(v)for v in x]
 return x

def build(base):
 source=module('aligned375_original288',base/'frontier/j-geometry/j_face_retained375_survival_heads.py');d=source.make_extended_model(base)
 lp,io,codec=d['lp'],d['io'],d['codec'];old_model=d['model'];oldrows=[dict(r)for r in lp.rows];oldrhs=list(lp.rhs);oldeq=[dict(r)for r in lp.equalities];olderhs=list(lp.erhs)
 require((lp.nvars,len(lp.rows),len(lp.equalities))==(12941,30454,20),'Complete established375 matrix')
 require(lp.rhs[14]==F(1,45)and lp.rows[17][875]==F(1,270)and lp.rows[22][875]==-F(1,270)and lp.erhs[4]==F(3,20),'Exact old coordinates before explicit geometry replacement')
 lp.rhs[14]=F(2,135);lp.rhs[17]=F(1,45)-F(1,405);lp.rhs[22]=F(1,45)-F(1,270)+F(1,405)
 lp.rows[17][875]=F(1,810);lp.rows[22][875]=-F(1,810);lp.erhs[4]=F(413,2700)
 for cell,mass in((14,F(2,135)),(19,F(1,45)),(24,F(1,45))):lp.equalities.append({16*cell+k:F(1)for k in range(16)});lp.erhs.append(mass)
 require([i for i,(a,b)in enumerate(zip(oldrows,lp.rows))if a!=b]==[17,22],'Only two theta coefficients change in original inequality matrix')
 require([i for i,(a,b)in enumerate(zip(oldrhs,lp.rhs))if a!=b]==[14,17,22],'Only three explicit raw-cell RHS changes')
 require(lp.equalities[:20]==oldeq and [i for i,(a,b)in enumerate(zip(olderhs,lp.erhs))if a!=b]==[4],'Original equality matrix remains;actual survivor RHS changed once')
 lp.columns=[[]for _ in range(lp.nvars)];lp.eqcolumns=[[]for _ in range(lp.nvars)]
 for i,row in enumerate(lp.rows):
  for c,v in row.items():lp.columns[c].append((i,v))
 for i,row in enumerate(lp.equalities):
  for c,v in row.items():lp.eqcolumns[c].append((i,v))
 lp.checker=codec.IntegerDualChecker(lp);lp.check_dual=lp.checker.check
 spec={'variables':12941,'inequalities':30454,'equalities':23,'rows_sha256':sha256(json.dumps(encode([lp.rows,lp.rhs,lp.equalities,lp.erhs]),sort_keys=True,separators=(',',':')).encode()).hexdigest(),
  'changed_inequality_matrix_rows':[17,22],'changed_inequality_rhs_rows':[14,17,22],'changed_original_equality_rhs_rows':[4],'added_fixed_H_equalities':[20,21,22],'old_model':old_model}
 return {'lp':lp,'io':io,'codec':codec,'model':spec,'old_model':old_model,
  'root':tuple(d['j'].ROOT),'head_load':d['reference'].head.bridge.head_load,
  'seven_increment':d['depth'].seven_increment,'old_u':d['triple'].U,'old_v':d['triple'].V,
  'actual_source':{'mass':F(1,4),'survivor_mass':F(413,2700),'theta_interval':(F(1,405),F(1,270)),'fixed_H_masses':(F(2,135),F(1,45),F(1,45))},
  'complete_zero7_tail':F(5071,405000),'complete_positive7_tail':F(13,490)-F(2,135*245)}

def zero_induction(data,heavy):
 lp=data['lp'];steps=[]
 for part in heavy['proof_data']['zero_induction_batches']:
  require(part['start']==len(steps)and part['stop']==len(steps)+len(part['rows']),'Entire original strong-zero induction')
  steps.extend(part['rows'])
 require(sha256(json.dumps(steps,sort_keys=True,separators=(',',':')).encode()).hexdigest()==heavy['proof_data']['zero_induction_sha256'],'Exact established induction identity')
 zero=set()
 for st in steps:
  require(st['kind']in('inequality','equality'),'Declared zero-induction row kind')
  rows,rhs=(lp.rows,lp.rhs)if st['kind']=='inequality'else(lp.equalities,lp.erhs);i=st['row'];sgn=st['sign']
  require(sgn in((1,)if st['kind']=='inequality'else(1,-1))and rhs[i]==0,'Same valid zero RHS on new actual model')
  neg={k for k,v in rows[i].items()if sgn*v<0};pos={k for k,v in rows[i].items()if sgn*v>0}
  require(sorted(neg)==st['negative_antecedents']and neg<=zero and sorted(pos-zero)==st['new_zero_columns'],'Every new-model zero is forced by earlier actual-zero columns')
  zero|=pos
 require(len(steps)==2645 and len(zero)==4634,'All and only original4634 zero columns survive;8307 other columns remain')
 return {'induction_rows':len(steps),'certified_zero_columns':len(zero),'remaining_columns':lp.nvars-len(zero),'zero_columns':sorted(zero)}

def objective(data,co,lay,pr,new):
 root=data['root'];kernel=data['seven_increment']
 hh=data['head_load'](lay);r,s,c63,r105,s105,r147,s245=pr;c441,r735,s735=new;obj=[F(0)]*12941
 h={v:sum(a*max(v-t,0)for t,a in co.items())for v in range(1,15)}
 g={(m,e):{v:sum(a*kernel(t,v,m,e)for t,a in co.items())for v in range(1,15)}for m in range(5)for e in range(5)}
 for i,b in enumerate(hh):
  c,slot=divmod(i,5);m=int(root[c]==r)+int(slot==s)+int(c==c63)+int(root[c]==r105 and slot==s105)
  e=int(root[c]==r147)+int(slot==s245)+int(c==c441)+int(root[c]==r735 and slot==s735);gg=g[m,e]
  for mask in range(16):
   k=16*i+mask;v=b+mask.bit_count();obj[k]=gg[v];obj[425+k]=h[v]
   for state in range(1,8):
    n=state.bit_count();obj[data['old_u']+400*(state-1)+k]=gg[v+n]-gg[v];obj[data['old_v']+400*(state-1)+k]=h[v+n]-h[v]
   for state in range(8):
    x=v+state.bit_count();obj[6531+400*state+k]=gg[x+1]-gg[x];obj[9731+400*state+k]=h[x+1]-h[x]
 require(min(obj)>=0 and all(v==0 for v in obj[12931:]),'All original physical raw/survivor objective columns retained')
 return obj,sum(co.values())*(data['complete_zero7_tail']+data['complete_positive7_tail'])

def coefficients(base,name):
 require(name in ('cost0','hinge4'),'A declared original own-load observation')
 if name=='hinge4':return {4:F(1)}
 io=module('aligned375_coefficients_io',base/'certificate_io.py')
 prior=json.loads(io.read_artifact_bytes(base/'certificates/source_norms/j-geometry/j_face_coupled_seven_heads.json'),object_pairs_hook=io._unique)
 co={int(t):F(v)for t,v in next(r for r in prior['results']if r['index']==0)['scan']['coefficients'].items()}
 require(set(co)==set(range(1,9))and min(co.values())>0 and sum(co.values())==F(403,8),'Original complete heavy0 hinge function')
 return co
