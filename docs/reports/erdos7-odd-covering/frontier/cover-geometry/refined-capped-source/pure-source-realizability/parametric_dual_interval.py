"""Portable exact all-threshold common-centre dual certificate.

This wrapper calls the canonical 834 common-centre consumer's rebuild at
low_limit=27; it contains no old 834 matrix or source-table copy. It computes
only the h16 scaled alpha(h) / fixed beta family on 249 source columns.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse, hashlib, importlib.util, json, signal, sys

PINS={
 'core': '6984706c0d0637c31a343ab904bfc14035d2d15c4e3e7da9a933e21cb7515236',
 'certificate': '5fc31747f56b3402332e45009175cc6f363df3d0c77f098fb42c4fa6ff6335f1',
 'result834': 'd676655e1bbcad96372415df11e4d1bf32e38667a58eb920c0d4bbc913e38699',
 'engine': 'a63339503f703fbd8e6f47148c12c0e5b9fafe475f88d5c6a891c1ea38e392f7',
 'certificate16': '6eb07b5a9bf153e477bdf15da5901a19d3b90a2c3ee255236533c0611ab75202',
}
CENTRES=((3,0,1,1,1,1,1,1),(4,1,1,1,1,1,1,1),(2,0,1,1,1,1,1,1))
checks=0

def need(ok,msg):
 global checks; checks+=1
 if not ok: raise ValueError(msg)
def digest(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def encode(v):
 if isinstance(v,F): return str(v)
 if isinstance(v,dict): return {str(k):encode(x) for k,x in v.items()}
 if isinstance(v,(tuple,list)): return [encode(x) for x in v]
 return v
def load(name,path):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);sys.modules[name]=m;spec.loader.exec_module(m);return m
def write_fresh(path,obj):
 data=(json.dumps(encode(obj),indent=2,sort_keys=True)+'\n').encode()
 with Path(path).open('xb') as f:f.write(data)
def interval_data(columns):
 unit=[];pieces=[]
 for j in range(28):
  left,right=F(j),F(j+1);lb=rb=None;blocked=None
  for i,v in columns.items():
   a=v[j];s=v[j+1]-a
   if s==0:
    if a>0:blocked=i;break
   else:
    z=F(j)-a/s
    if s<0 and z>left:left,lb=z,i
    if s>0 and z<right:right,rb=z,i
  if blocked is not None or left>right:
   unit.append({'unit':j,'valid':False,'constant_positive_column':blocked,'left':left,'right':right});continue
  for h in (left,right):need(all(v[j]+(h-j)*(v[j+1]-v[j])<=0 for v in columns.values()),'all columns satisfy interval endpoints')
  unit.append({'unit':j,'valid':True,'left':left,'right':right,'left_binding_column':lb,'right_binding_column':rb})
  if pieces and left<=pieces[-1][1]:pieces[-1][1]=max(pieces[-1][1],right)
  else:pieces.append([left,right])
 return unit,[{'left':a,'right':b,'left_closed':True,'right_closed':b<28} for a,b in pieces if a<28]
def verify_h16(core,engine,cert,built):
 need(cert['schema']=='e7-arbitrary-retained-common-centre-h16-dual-v1','h16 schema')
 need(cert['source_pins']==core.PINS and cert['threshold']==16 and cert['tail_coefficient']=='0','h16 fixed source and threshold')
 centres=(CENTRES[0],CENTRES[2]);need(cert['centres']==encode(centres),'h16 exact common centres')
 rows=list(built['cap_rows'])
 for c in centres:
  b=[engine.hinge(law,16) for law in built['centre_laws'][c]]
  terms=[(i,b[i]-12*m) for i,m in enumerate(built['masses'])]
  terms += [(i,12*loss) for i,loss in built['losses'].items()]+[(633,F(1))]
  rows.append({'label':['centre_gate',*c],'terms':core.sparse(terms),'rhs':'0'})
 matrix={'centres':centres,'variables':built['matrix']['variables'],'inequalities':rows,'equality':built['matrix']['equality']}
 need(core.semantic_hash(matrix)==cert['semantic_matrix_sha256'],'h16 complete matrix semantic identity')
 dual=cert['upper_certificate'];need(dual['kind']=='dual','h16 dual kind')
 y=core.sparse_vector(dual['inequality_multipliers'],len(rows));lam=F(dual['mass_multiplier'])
 need(y[9902:]==[F(1,2),F(1,2)],'h16 half A/C mixture')
 col=[F(0)]*634;budgets={i:F(0) for i in range(249,633)}
 for r,w in enumerate(y):
  if not w:continue
  for i,v in rows[r]['terms']:col[i]+=w*v
  if r<9902:budgets[next(i for i,_ in rows[r]['terms'] if i>=249)]+=w
 for i,m in enumerate(built['masses']):col[i]+=lam*m
 need(col[633]==1 and all(v>=0 for v in col[:633]),'h16 every exact dual column')
 need(all(cost<=12*built['losses'][i] for i,cost in budgets.items()),'h16 every scalable cap budget')
 need(-F(46,1000)<lam<-F(45,1000)<-F(1,25),'h16 exact negative interval')
 return rows,dual
def family(engine,built,rows,dual,anchor):
 cap={i:F(0) for i in range(249)}
 for r,value in dual['inequality_multipliers']:
  if r>=9902:continue
  for i,v in rows[r]['terms']:
   if i<249:cap[i]+=F(value)*v
 need(all(v>=0 for v in cap.values()),'nonnegative cap source contributions')
 columns={i:[] for i in range(249)}
 for h in range(29):
  scale=F(28-h,28-anchor)
  for i,m in enumerate(built['masses']):
   b=sum((engine.hinge(built['centre_laws'][c][i],h)/2 for c in (CENTRES[0],CENTRES[2])),F(0))
   columns[i].append(F(28-h)-(scale*cap[i]+b)/m)
 endpoints=[]
 for h in range(29):
  value=max(v[h] for v in columns.values());arg=min(i for i,v in columns.items() if v[h]==value)
  endpoints.append({'h':h,'lambda':value,'witness_column':arg,'witness_cell':built['allowed'][arg],'ties':sum(v[h]==value for v in columns.values()),'display':float(value)})
 need(endpoints[anchor]['lambda']==F(dual['mass_multiplier']),'exact anchor dual control')
 unit,valid=interval_data(columns);best=max(range(29),key=lambda h:(endpoints[h]['lambda'],-h))
 return {'anchor':anchor,'scale_denominator':28-anchor,'baseline':endpoints[anchor],'integer_endpoints':endpoints,'maximum_closed_domain':endpoints[best],
         'supremum_half_open_domain':endpoints[best]['lambda'],'selected_maximum_attained_before28':best<28,
         'all_h_nonpositive':all(v['lambda']<=0 for v in endpoints),'strict_on_closed_domain':all(v['lambda']<0 for v in endpoints),
         'valid_unit_intervals':unit,'valid_half_open_domain_intervals':valid},columns
def main():
 ap=argparse.ArgumentParser()
 for n in ('core','candidate','result832','certificate','certificate16','result834','legacy-engine','centre-engine'):ap.add_argument('--'+n,required=True,type=Path)
 ap.add_argument('--result',required=True,type=Path);ap.add_argument('--transient',type=Path);ap.add_argument('--write-result',action='store_true');ap.add_argument('--timeout',type=int,default=300)
 a=ap.parse_args();start=__import__('time').perf_counter()
 paths={'core':a.core,'certificate':a.certificate,'certificate16':a.certificate16,'result834':a.result834,'engine':a.centre_engine}
 for n,p in paths.items():need(digest(p)==PINS[n],'immutable '+n)
 signal.signal(signal.SIGALRM,lambda s,f:(_ for _ in ()).throw(TimeoutError('timeout')));signal.alarm(a.timeout)
 core=load('e7_834_core',a.core)
 # Enforce the core's declared pins before importing further code or parsing source inputs.
 for key,path in {'candidate':a.candidate,'result832':a.result832,'centre_engine':a.centre_engine,'legacy_engine':a.legacy_engine}.items():
  need(digest(path)==core.PINS[key],'canonical834 source '+key)
 cert=core.read_json(a.certificate);res834=core.read_json(a.result834)
 need(cert['schema']=='e7-arbitrary-retained-common-centre-certificate-v1','certificate schema')
 need(res834['schema']=='e7-arbitrary-retained-common-centre-result-v1','834 result schema')
 need(res834['semantic_matrix_sha256']==cert['semantic_matrix_sha256'],'certificate/result semantic matrix')
 legacy=load('e7_834_legacy',a.legacy_engine);engine=load('e7_834_engine',a.centre_engine)
 built=core.rebuild(legacy,engine,core.read_json(a.candidate),core.read_json(a.result832),low_limit=27)
 need(built['semantic_matrix_sha256']==cert['semantic_matrix_sha256'],'canonical 834 low27 rebuild identity')
 verified=core.encode(core.verify(cert,built))
 expected834=dict(res834)
 expected834.pop('certificate_sha256');expected834.pop('consumer_sha256')
 need(verified==expected834,'canonical834 complete certificate and existing result')
 rows=built['matrix']['inequalities'];need(len(rows)==9905,'9905 canonical rows')
 masses=built['masses'];need(len(masses)==249,'249 source columns')
 rows16,dual16=verify_h16(core,engine,core.read_json(a.certificate16),built)
 if not a.write_result: need(a.result.exists(),'saved result required for comparison')
 else: need(not a.result.exists(),'fresh result path required for write')
 print('BOUND canonical core and exact h16 dual; computing 249x29 scaled dual columns',flush=True)
 f16,c16=family(engine,built,rows16,dual16,16)
 margin=F(2,401397328829)
 need(f16['maximum_closed_domain']['lambda']==-margin,'exact uniform certificate upper bound')
 need(f16['strict_on_closed_domain'] and f16['all_h_nonpositive'],'strict certificate throughout the closed interval')
 slacks=[]
 for row in f16['integer_endpoints']:
  slack=-margin-F(28-row['h'],400)-row['lambda']
  need(slack>=0,'fixed 1/400 proportional gap at each endpoint');slacks.append(slack)
 out={'schema':'e7-835-all-threshold-portable-result-v1','status':'pass','scope':'Canonical834 rebuild low_limit27; same C/phase31/249 K8 columns/zero tail/mass-one necessary raw-hinge master; h16 cap-dual scaled by (28-h)/12 and beta A=C=1/2.',
 'bindings':{**PINS,'consumer':digest(Path(__file__))},'family':f16,'uniform_margin':margin,
 'proportional_margin':{'slope':F(1,400),'intercept':margin,'endpoint_comparisons':29,'minimum_endpoint_slack':min(slacks),'zero_slack_endpoints':[j for j,v in enumerate(slacks) if v==0]},
 'statement':'For every nonnegative table u on the fixed 249 cells and every real h in [0,28], (H_A(h;u)+H_C(h;u))/2 >= (28-h)(L(u)+M(u)/400)+(2/401397328829)M(u).',
 'proof':'Cap feasibility scales by nonnegative (28-h)/12. Every cell hinge and lambda column is affine on each unit interval. Their maximum, also after adding (28-h)/400, is convex on each unit interval. The 29 exact endpoint comparisons prove the uniform and proportional bounds on the whole closed interval.',
 'limitations':['The maximum is of this fixed dual certificate family, not an asserted primal optimum.', 'No other source, phase, selected head or actual-survivor comparison is excluded.', 'No unrestricted Erdos7 or Lean claim.'],
 'optimizer_called':False,'full_960_centre_tensor_called':False}
 if a.transient:write_fresh(a.transient,{'h16_columns':c16})
 if a.write_result:write_fresh(a.result,out)
 else:need(core.read_json(a.result)==encode(out),'deterministic replay comparison')
 signal.alarm(0);print(json.dumps(encode({'status':'pass','decision':'all-h','uniform_margin':margin,'maximum':f16['maximum_closed_domain'],'checks':checks,'elapsed_seconds':__import__('time').perf_counter()-start}),indent=2))
if __name__=='__main__':main()
