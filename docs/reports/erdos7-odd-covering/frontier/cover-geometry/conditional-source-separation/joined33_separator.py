#!/usr/bin/env python3
"""Exact33-label selected-block oracle with one common retained-measure input.
Existing392 conditional central separator + existing66 composite elimination.
No source/retention optimization. No common-center restriction.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product,combinations
from math import prod,gcd,lcm
from hashlib import sha256
import argparse,importlib.util,json,time,resource,sys
import numpy as np
P=(3,5,7,11,13,17,19);CENTRAL=(3,5,9,15,25,45,75,225);CHECKS=0

def ck(ok,label):
 global CHECKS
 CHECKS+=1
 if not ok:raise ArithmeticError(label)

def load_module(name,path):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);sys.modules[name]=m;spec.loader.exec_module(m);return m
CENTRAL_PROGRAM=Path(__file__).resolve().with_name('central_conditional_separator.py')
central_module=load_module('joined_conditional',CENTRAL_PROGRAM)

def joined_separator(points,weights,unary,pairs,denominator=1,chunk=65536):
 """Rational common-source API. Marginal consistency checked, not fabricated.
 Return an exact upper/maximum with one actual33-label attaining row.
 """
 started=time.perf_counter()
 ck(all(type(w) in (int,np.int64) for w in weights),'integer central masses without rounding')
 weights=list(map(int,weights));total=sum(weights)
 if not points and total==0:points=[(0,0)];weights=[0]
 ck(type(denominator) is int and denominator>0,'positive common denominator')
 ck(len(points)==len(weights) and all(v>=0 for v in weights),'one nonnegative central weight per atom')
 cp3=[0]*3;cp5=[0]*5;cp35=np.zeros((3,5),dtype=object)
 for (x,y),w in zip(points,weights):
  ck(0<=x<9 and 0<=y<25,'literal central225 atom')
  cp3[x%3]+=w;cp5[y%5]+=w;cp35[x%3,y%5]+=w
 ck(set(pairs)==set(combinations(range(7),2)),'all21 same-source pair projections')
 for i,p in enumerate(P):
  ck(len(unary[i])==p and all(type(v) in (int,np.int64) and v>=0 for v in unary[i]),'nonnegative root marginal')
  ck(sum(map(int,unary[i]))==total,'one source total throughout')
 for (i,j),w in pairs.items():
  ck(w.shape==(P[i],P[j]) and all(type(v) in (int,np.int64) and v>=0 for v in w.flat),'nonnegative joint pair table')
  ck(all(sum(map(int,w[a,:]))==int(unary[i][a]) for a in range(P[i])),'pair first marginal')
  ck(all(sum(map(int,w[:,b]))==int(unary[j][b]) for b in range(P[j])),'pair second marginal')
 ck(cp3==list(map(int,unary[0])) and cp5==list(map(int,unary[1])) and np.array_equal(cp35,pairs[0,1]),'central fine and root projections come with matching common marginals')
 C,central_layouts=central_module.central_conditional_table(points,weights)
 central_elapsed=time.perf_counter()-started
 bound=275*total;dtype=np.int64 if bound<2**63 else object
 C=np.array(C,dtype=dtype);E={};args={}
 for (i,j),w in pairs.items():
  if (i,j)==(0,1):continue
  p,q=P[i],P[j];edge=np.empty((p,q),dtype=dtype);arg={}
  for a,b in product(range(p),range(q)):
   best=-1;chosen=None
   for u,v in product(range(p),range(q)):
    val=(3+2*int(u==a)+2*int(v==b))*int(w[u,v])
    if val>best:best=val;chosen=(u,v)
   edge[a,b]=2*int(w[a,b])+best;arg[a,b]=chosen
  E[i,j]=edge;args[i,j]=arg
 # Safe independent-domain reduction. Compare each root's COMPLETE response
 # vector against every possible value of every neighbor, including central C.
 # If another root is pointwise no worse, replacing just this root never lowers
 # any global energy. Lexical ties prevent deleting all equal representatives.
 signatures=[];domains=[];dominance=[]
 for i,p in enumerate(P):
  rows=[]
  for a in range(p):
   sig=[3*int(unary[i][a])] if i>=2 else []
   if i==0:sig+=list(map(int,C[a,:]))
   elif i==1:sig+=list(map(int,C[:,a]))
   for (l,r),edge in E.items():
    if i==l:sig+=list(map(int,edge[a,:]))
    elif i==r:sig+=list(map(int,edge[:,a]))
   rows.append(tuple(sig))
  signatures.append(rows);live=[]
  for a in range(p):
   dominator=next((b for b in range(p) if b!=a and all(y>=x for x,y in zip(rows[a],rows[b])) and (rows[a]!=rows[b] or b<a)),None)
   if dominator is None:live.append(a)
   else:dominance.append({'prime':p,'removed':a,'dominator':dominator,'equal_response':rows[a]==rows[dominator]})
  ck(bool(live),'at least one maximal response in every finite root domain');domains.append(live)
 count=prod(map(len,domains));best=-1;bestcode=None;maximizers=0
 un=[np.array(v,dtype=dtype) for v in unary]
 domainarrays=[np.array(v,dtype=np.int64) for v in domains]
 for start in range(0,count,chunk):
  stop=min(start+chunk,count);rem=np.arange(start,stop,dtype=np.int64);coords=[None]*7
  for i in range(6,-1,-1):ids=rem%len(domains[i]);rem=rem//len(domains[i]);coords[i]=domainarrays[i][ids]
  values=C[coords[0],coords[1]].copy()
  for i in range(2,7):values+=3*un[i][coords[i]]
  for (i,j),edge in E.items():values+=edge[coords[i],coords[j]]
  local=int(values.max());where=np.flatnonzero(values==local)
  if local>best:best=local;bestcode=start+int(where[0]);maximizers=len(where)
  elif local==best:maximizers+=len(where)
 roots=[0]*7;rem=bestcode
 for i in range(6,-1,-1):rem,j=divmod(rem,len(domains[i]));roots[i]=domains[i][j]
 layout=dict(central_layouts[roots[0],roots[1]])
 for i in range(2,7):layout[P[i]]=roots[i]
 for i,j in E:
  p,q=P[i],P[j];u,v=args[i,j][roots[i],roots[j]]
  residue=u+p*(((v-u)*pow(p,-1,q))%q)
  ck(residue%p==u and residue%q==v,'literal independent composite residue');layout[p*q]=residue
 ck(len(layout)==33 and set(layout)==set(CENTRAL)|set(P[2:])|{P[i]*P[j] for i,j in E},'exact33 original numerical labels')
 # Direct reconstruction uses actual central and root joint events, never
 # products of separately averaged incidence columns.
 central_literal=0
 for (x,y),w in zip(points,weights):
  physical=x+9*(((y-x)*pow(9,-1,25))%25)
  n=sum(physical%d==layout[d] for d in CENTRAL)
  central_literal+=w*(n*n+2*n)
 ck(central_literal==int(C[roots[0],roots[1]]),'literal eight-label central row matches conditional separator')
 literal=central_literal+3*sum(int(unary[i][roots[i]]) for i in range(2,7))
 for (i,j),w in pairs.items():
  if (i,j)==(0,1):continue
  residue=layout[P[i]*P[j]];u,v=residue%P[i],residue%P[j]
  literal+=3*int(w[u,v])+2*(int(w[roots[i],roots[j]])+int(u==roots[i])*int(w[u,v])+int(v==roots[j])*int(w[u,v]))
 ck(literal==best,'one actual33-label row attains the exact upper after domain reduction')
 return {'integer_value':best,'value':str(F(best,denominator)),'value_decimal':float(F(best,denominator)),
  'layout':{str(d):v for d,v in sorted(layout.items())},'prime_roots':roots,
  'conditional_C':[[str(F(int(v),denominator)) for v in row] for row in C],
  'central_unconditional':str(F(max(map(int,C.flat)),denominator)),
  'conditional_layouts':[{'roots':[a,b],'value':str(F(int(C[a,b]),denominator)),'layout':{str(d):r for d,r in sorted(central_layouts[a,b].items())}} for a,b in product(range(3),range(5))],
  'raw_prime_tuple_count':prod(P),'reduced_domains':dict(zip(map(str,P),domains)),
  'reduced_tuple_count':count,'reduced_maximizer_count':int(maximizers),'domain_dominance':dominance,
  'integer_bound':bound,'arithmetic':'checked_int64' if dtype is np.int64 else 'arbitrary_integer',
  'central_seconds':central_elapsed,'total_seconds':time.perf_counter()-started}

def joined_fee_audit(base):
 data=json.loads((base/'remaining33_global_root_exclusion_certificate.json').read_text())
 c=F(1084133,201247200);g=1-c;Q=P[2:];C=list(map(F,data['combined512_coefficients']))
 for i,q in enumerate(Q):
  if i:C[256+(1<<i)]+=g/F(q*(q-2))
 rows=[]
 for j in range(512):
  mode,T=divmod(j,32);e3,e5=divmod(mode,4)
  W=(F(1),F(3),F(5),F(8,9))[e3]*(F(1),F(3),F(5),F(1,8))[e5]*prod(F(3,q-1)+F(5*q-3,(q-2)*(q-1)**2) for i,q in enumerate(Q) if T&(1<<i))
  if j==0:W=F(0)
  size=e3+e5+T.bit_count()
  if T==0 and e3<=2 and e5<=2 and mode!=0:selected=F((2*e3+1)*(2*e5+1))
  elif T and e3<=1 and e5<=1 and size<=2:selected=F(3**size)*prod(F(1,q-1) for i,q in enumerate(Q) if T&(1<<i))
  else:selected=F(0)
  loss=C[j]-c*W
  ck(loss>=0 and W-selected>=0 and C[j]-c*selected==loss+c*(W-selected),'unchanged loss plus all unselected query heights')
  if selected:rows.append({'screen':j,'selected_W':str(selected),'old_W':str(W),'remaining_W':str(W-selected),'unchanged_loss':str(loss),'new_C':str(C[j]-c*selected)})
 tokens=[('unary',d,3,d) for d in CENTRAL]
 for d,e in combinations(CENTRAL,2):tokens.append(('pair',(d,e),2,lcm(d,e)))
 for q in P[2:]:tokens.append(('unary',q,3,q))
 for p,q in combinations(P,2):
  if (p,q)==(3,5):continue
  tokens.append(('unary',p*q,3,p*q))
  for d,e in [(p,q),(p,p*q),(q,p*q)]:tokens.append(('pair',(d,e),2,p*q))
 ck(len(rows)==33 and len(tokens)==121 and sum(t[2] for t in tokens)==275,'33unary88pair totalweight275')
 ck(len({(t[0],str(t[1])) for t in tokens})==121,'one ownership for every selected atom')
 for row in rows:
  j=row['screen'];mode,T=divmod(j,32);e3,e5=divmod(mode,4)
  modulus=3**e3*5**e5*prod(q for i,q in enumerate(Q) if T&(1<<i))
  amount=sum(t[2] for t in tokens if t[3]==modulus)
  normal=prod(F(1,q-1) for i,q in enumerate(Q) if T&(1<<i))
  ck(amount*normal==F(row['selected_W']),'literal token lcm count and original normalization')
 return rows,tokens,C

def parse_integer(value):
 ck(type(value) is int or (type(value) is str and (value.isdigit() or (value.startswith('-') and value[1:].isdigit()))),'integer or exact decimal integer string, never floating input')
 return int(value)

def load_input(path):
 data=json.loads(path.read_text());den=parse_integer(data['denominator'])
 points=data['central']['points'];weights=list(map(parse_integer,data['central']['weights']))
 unary=[np.array(list(map(parse_integer,data['unary'][str(p)])),dtype=object) for p in P]
 pairs={(i,j):np.array([[parse_integer(v) for v in row] for row in data['pairs'][f'{P[i]},{P[j]}']],dtype=object) for i,j in combinations(range(7),2)}
 return data,points,weights,unary,pairs,den

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--input',type=Path,required=True)
 ap.add_argument('--base',type=Path,default=Path(__file__).resolve().parent.parent)
 ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
 a=ap.parse_args();started=time.perf_counter();data,points,weights,unary,pairs,den=load_input(a.input)
 if data.get('field_file') is not None:
  field_path=Path(data['field_file'])
  if not field_path.is_absolute():field_path=a.input.parent/field_path
  ck(sha256(field_path.read_bytes()).hexdigest()==data['field_sha256'],'exact input retained-field file digest')
 elif 'field_file' in data:
  ck(data.get('field')=='allone' and data.get('field_sha256') is None,'explicit unit retention has no field artifact')
 if 'source_sha256' in data:
  for name,digest in data['source_sha256'].items():ck(sha256((a.base/name).read_bytes()).hexdigest()==digest,'exact pinned common source '+name)
 result=joined_separator(points,weights,unary,pairs,den);rows,tokens,old_coeff=joined_fee_audit(a.base)
 c=F(1084133,201247200)
 result.update({'status':'PASS','checks':CHECKS,'input_sha256':sha256(a.input.read_bytes()).hexdigest(),
  'program_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'central_program_sha256':sha256(CENTRAL_PROGRAM.read_bytes()).hexdigest(),
  'source_mass':str(F(sum(weights),den)),'input_provenance':{k:data[k] for k in ('measure','field','source_sha256','field_sha256','field_definition','field_denominator','tau','dual_witness_sha256','program_sha256','producer_sha256','old_gate_scope') if k in data},'fee_audit':rows,'token_ledger':tokens,
  'scope':'Exact maximum of joined33 selected query block for ONE supplied common retained measure. No primal optimization, source switch, standalone gate claim or new Lean verification.'})
 if 'original_screen_values' in data or 'screen_values' in data:
  values=data.get('original_screen_values',data.get('screen_values'))
  screen=[F(values[j] if isinstance(values,list) else values[str(j)]) for j in range(512)]
  ck(len(values)==512 and all(v>=0 for v in screen),'complete nonnegative original screens')
  if 'original_coefficients' in data:ck(list(map(F,data['original_coefficients']))==old_coeff,'producer coefficient table equals independently reconstructed fullmode8 ledger')
  selected=sum(F(r['selected_W'])*screen[r['screen']] for r in rows)
  old_gate=(1-c)*F(sum(weights),den)-sum(coef*v for coef,v in zip(old_coeff,screen))
  if 'old_gate' in data:ck(old_gate==F(data['old_gate']),'independently recombined original gate')
  if 'selected_joined_screen_fee' in data:ck(selected==F(data['selected_joined_screen_fee']),'independently recombined selected query subledger')
  remain=old_coeff.copy()
  for r in rows:remain[r['screen']]-=c*F(r['selected_W'])
  direct=(1-c)*F(sum(weights),den)-sum(coef*v for coef,v in zip(remain,screen))-c*F(result['value'])
  difference=old_gate+c*(selected-F(result['value']))
  ck(direct==difference,'direct remaining-fee gate equals exact old-gate difference')
  result.update({'old_gate':str(old_gate),'old_gate_decimal':float(old_gate),'actual_selected_screen_fee':str(selected),
    'actual_query_saving':str(selected-F(result['value'])),'actual_gate_improvement':str(direct-old_gate),
    'actual_gate_improvement_decimal':float(direct-old_gate),'joined_gate':str(direct),'joined_gate_decimal':float(direct),
    'reaches_target':direct>=F(193,100000),'target':str(F(193,100000))})
 elif 'selected_joined_screen_fee' in data:
  selected=F(data['selected_joined_screen_fee']);result['actual_selected_screen_fee']=str(selected)
  if 'old_gate' in data:result['joined_gate']=str(F(data['old_gate'])+c*(selected-F(result['value'])))
 result['checks']=CHECKS
 result['elapsed_seconds']=time.perf_counter()-started;result['peak_rss_bytes']=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
 a.output.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items() if k not in ('fee_audit','token_ledger','conditional_C','conditional_layouts','domain_dominance')},indent=2))
if __name__=='__main__':main()
