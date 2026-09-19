#!/usr/bin/env python3
"""Complete exact retained375 cover on the actual aligned endpoint.

The companion prefix checker establishes all pruned original choices.
This checker closes every remaining leaf, using the standard library and
every original matrix column.
Writing alone imports optional numpy/scipy to propose rational dual prices.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from collections import defaultdict
from hashlib import sha256
import importlib.util,json,sys,argparse,time
sys.dont_write_bytecode=True
parser=argparse.ArgumentParser()
parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[1])
parser.add_argument('--prefix',type=Path,required=True)
parser.add_argument('--certificate',type=Path,required=True)
parser.add_argument('--warm-cover',type=Path)
mode=parser.add_mutually_exclusive_group(required=True);mode.add_argument('--write',action='store_true');mode.add_argument('--check',action='store_true')
args=parser.parse_args();B=args.base.resolve()
s=importlib.util.spec_from_file_location('aligned375_cover_provider',Path(__file__).with_name('j_aligned_retained375_source.py'));p=importlib.util.module_from_spec(s);s.loader.exec_module(p)
data=p.build(B);lp,io=data['lp'],data['io'];read=lambda f:json.loads(io.read_artifact_bytes(f),object_pairs_hook=io._unique)
prefix=read(args.prefix);heavy=read(B/'certificates/source_norms/j_face_retained375_heavy_heads.json');zero_data=p.zero_induction(data,heavy);zero=set(zero_data['zero_columns']);co={int(t):F(v)for t,v in prefix['coefficients'].items()};p.require(co==p.coefficients(B,prefix['name']),'Exact original own-load coefficients');target=F(prefix['target_scheduling_upper']);constant=sum(co.values())*(data['complete_zero7_tail']+data['complete_positive7_tail']);leaves=[]
for b in prefix['remaining_leaf_batches']:
 p.require(b['start']==len(leaves)and b['stop']==len(leaves)+len(b['rows']),'Complete new-source remaining branch ledger');leaves+=b['rows']
p.require(len(leaves)==prefix['counts']['remaining'],'Every pending leaf accounted')
p.require(prefix['schema']=='erdos7-aligned-retained375-prefix-v1'and prefix['covered_containing_choices']==3125000000 and target>0,'Complete companion source-prefix contract')
path=args.certificate
if args.write:
 import numpy as np
 from scipy.sparse import csr_matrix
 from scipy.optimize import linprog
 def matrix(rows):return csr_matrix(([float(v)for r in rows for v in r.values()],([i for i,r in enumerate(rows)for _ in r],[c for r in rows for c in r])),shape=(len(rows),lp.nvars))
 A,E=matrix(lp.rows),matrix(lp.equalities);rhs=np.array(list(map(float,lp.rhs)));erhs=np.array(list(map(float,lp.erhs)));bank={}
else:given=read(path);bank=data['codec'].decode_dual_bank(given['encoded_rational_duals'],inequality_count=30454,equality_count=23)
if args.write and args.warm_cover:
 warm=read(args.warm_cover);p.require(warm['model']==p.encode(data['model']),'Warm proposals use identical new actual matrix');bank=data['codec'].decode_dual_bank(warm['encoded_rational_duals'],inequality_count=30454,equality_count=23)
root=data['root'];kernel=data['seven_increment'];hs={v:sum(a*max(v-t,0)for t,a in co.items())for v in range(1,15)};gs={(m,e):{v:sum(a*kernel(t,v,m,e)for t,a in co.items())for v in range(1,15)}for m,e in product(range(5),repeat=2)}
params=[]
for leaf in leaves:
 hh=data['head_load'](leaf['layout']);r,s,c63,r105,s105,r147,s245=leaf['projection'];c441,r735,s735=leaf['projection441_735']
 params.append([(b,int(root[c]==r)+int(k==s)+int(c==c63)+int(root[c]==r105 and k==s105),int(root[c]==r147)+int(k==s245)+int(c==c441)+int(root[c]==r735 and k==s735))for b,(c,k)in zip(hh,product(range(5),repeat=2))])
specs=[];physical=set()
for cell in range(25):
 dd=defaultdict(list)
 def put(spec,col):physical.add(col);dd[spec].append(col)
 for mask in range(16):
  k=16*cell+mask;q=mask.bit_count();put(('X',q,0),k);put(('Y',q,0),425+k)
  for st in range(1,8):n=st.bit_count();put(('OU',q,n),876+400*(st-1)+k);put(('OV',q,n),3676+400*(st-1)+k)
  for st in range(8):n=st.bit_count();put(('NU',q,n),6531+400*st+k);put(('NV',q,n),9731+400*st+k)
 specs.append(dd)
p.require(len(physical)==12800,'All physical objective columns retained;remaining141 profile/control coefficients zero')
cache={}
def scalar(spec,param):
 key=(spec,param)
 if key not in cache:
  kind,q,n=spec;b,m,e=param;v=b+q;g=gs[m,e]
  cache[key]={'X':lambda:g[v],'Y':lambda:hs[v],'OU':lambda:g[v+n]-g[v],'OV':lambda:hs[v+n]-hs[v],'NU':lambda:g[v+n+1]-g[v+n],'NV':lambda:hs[v+n+1]-hs[v+n]}[kind]()
 return cache[key]
def objective(ids):
 obj=[F(0)]*lp.nvars
 for cell,dd in enumerate(specs):
  present=sorted({params[i][cell]for i in ids})
  for spec,cols in dd.items():
   values=[scalar(spec,q)for q in present];v=max(values);p.require(v>=0 and all(x<=v for x in values),'Every member coordinate has a nonnegative exact maximum')
   for c in cols:
    if c not in zero:obj[c]=v
 return obj
used=set();records=[];closed=set();counts=defaultdict(int);started=time.monotonic();largest=target

def evaluate(ids,level):
 global largest
 obj=objective(ids);key=sha256(json.dumps([data['model']['rows_sha256'],p.encode(obj)],separators=(',',':')).encode()).hexdigest()
 if key not in bank:
  p.require(args.write,'A stored exact dual for every original visited node')
  res=linprog(-np.array(list(map(float,obj))),A_ub=A,b_ub=rhs,A_eq=E,b_eq=erhs,bounds=(0,None),method='highs');p.require(res.success,'Fresh full375 source LP '+res.message)
  y=[max(F(0),F(round(float(-v)*10**12),10**12))for v in res.ineqlin.marginals];z=[F(round(float(-v)*10**12),10**12)for v in res.eqlin.marginals]
  for c in range(lp.nvars):
   gap=obj[c]-sum(v*y[i]for i,v in lp.columns[c])-sum(v*z[i]for i,v in lp.eqcolumns[c])
   if gap>0:
    u=lp.unit_rows[c];p.require(lp.rows[u]=={c:F(1)}and lp.rhs[u]==1,'Full original unit repair');y[u]+=gap
  value=sum(v*b for v,b in zip(y,lp.rhs))+sum(v*b for v,b in zip(z,lp.erhs));bank[key]={'nonzero_inequality_duals':{str(i):str(v)for i,v in enumerate(y)if v},'equality_duals':list(map(str,z)),'raw_objective_upper':str(value)}
 raw=lp.checker.check(obj,bank[key]);upper=raw+constant;close=upper<=target or len(ids)==1
 if close:
  p.require(ids and len(ids)==len(set(ids))and not(set(ids)&closed),'Disjoint nonempty exact source cover')
  used.add(key);records.append({'level':level,'leaf_indices':ids,'dual_key':key,'complete_upper':upper});counts[level]+=1
  closed.update(ids);largest=max(largest,upper)
 else:
  p.require(args.write,'Every stored final node closes at its exact bound')
  p.require(level<3,'All independent projection coordinates split before singleton stage')
  groups=defaultdict(list)
  for i in ids:groups[leaves[i]['projection441_735'][level]].append(i)
  p.require(len(groups)>1 or level<2,'A nonsingleton has a further independent coordinate')
  for ids2 in groups.values():evaluate(ids2,level+1)
 if len(records)%20==0:print('NEW375 COVER nodes',len(records),'closed',len(closed),'of',len(leaves),'upper',float(largest),'seconds',round(time.monotonic()-started,2),flush=True)

if args.write:
 groups=defaultdict(list)
 for i,leaf in enumerate(leaves):groups[(tuple(leaf['layout']),tuple(leaf['projection']))].append(i)
 for ids in groups.values():evaluate(ids,0)
else:
 final_nodes=[]
 for batch in given['cover_node_batches']:
  p.require(batch['start']==len(final_nodes)and batch['stop']==len(final_nodes)+len(batch['rows']),'Complete final-node batches')
  final_nodes.extend(batch['rows'])
 for node in final_nodes:
  ids=node['leaf_indices'];level=node['level']
  p.require(type(level)is int and 0<=level<=3 and ids and len(ids)==len(set(ids))and all(type(i)is int and 0<=i<len(leaves)for i in ids),'Legal final-node coordinates')
  p.require(len({(tuple(leaves[i]['layout']),tuple(leaves[i]['projection']),tuple(leaves[i]['projection441_735'][:level]))for i in ids})==1,'One original fixed projection prefix per final node')
  evaluate(ids,level)
if args.write:bank={k:bank[k]for k in sorted(used)}
p.require(closed==set(range(len(leaves)))and used==set(bank),'Every newly unresolved original leaf closed exactly once;every stored dual consumed')
out={'schema':'erdos7-aligned-retained375-final-cover-v1','model':data['model'],'prefix_sha256':sha256(io.read_artifact_bytes(args.prefix)).hexdigest(),'provider_sha256':sha256(io.read_artifact_bytes(Path(__file__).with_name('j_aligned_retained375_source.py'))).hexdigest(),
 'target_scheduling_upper':target,'name':prefix['name'],'complete_uniform_upper':largest,'complete_old_tail':data['complete_zero7_tail'],'complete_positive7_tail':data['complete_positive7_tail'],'complete_tail_constant':constant,
 'zero_induction':{k:v for k,v in zero_data.items()if k!='zero_columns'},'residual_leaf_count':len(leaves),'source_cover_counts':dict(counts),'covered_original_choices':3125000000,'cover_node_batches':[{'start':i,'stop':min(i+100,len(records)),'rows':records[i:i+100]}for i in range(0,len(records),100)],
 'distinct_duals':len(used),'rational_column_checks':12941*len(used),'encoded_rational_duals':data['codec'].encode_dual_bank(bank,inequality_count=30454,equality_count=23),
 'scope':'Complete original own-test '+prefix['name']+' bound on the actual aligned equality source. All3.125b independent containing choices lie in a new-source affine prefix or a freshly checked exact375 node. Only coefficients on the4634 proven-zero columns are discarded;all other objective coefficients are retained. Complete exponent/cofactor tails remain. No403 result or actual attainment.'}
if args.write:io.write_certificate_text(path,json.dumps(p.encode(out),indent=2)+'\n')
else:p.require(p.encode(out)==given,'Every final-domain partition,objective and exact dual regenerates')
print('PASS UNIVERSAL ALIGNED375 '+prefix['name']+' <=',largest,float(largest),'leaves',len(leaves),'nodes',len(records),'seconds',round(time.monotonic()-started,2),flush=True)
