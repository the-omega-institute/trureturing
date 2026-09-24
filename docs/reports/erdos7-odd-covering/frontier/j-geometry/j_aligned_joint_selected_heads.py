#!/usr/bin/env python3
"""Complete independently labelled heads at the actual aligned J endpoint.

The checker uses the standard library only. Every new joint-source dual is
replayed exactly, including all original label choices and complete tails.
"""
from types import SimpleNamespace,MethodType
import argparse
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from hashlib import sha256
import importlib.util,json,sys
sys.dont_write_bytecode=True

def require(p,m):
 if not p:raise ValueError(m)
def module(n,p):
 s=importlib.util.spec_from_file_location(n,p);require(s is not None and s.loader is not None,'Readable original provider')
 m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
def encode(x):
 if isinstance(x,F):return str(x)
 if isinstance(x,dict):return {str(k):encode(v)for k,v in x.items()}
 if isinstance(x,(tuple,list)):return [encode(v)for v in x]
 return x

def build_source(base,namespace='aligned_source_provider'):
 io=module(namespace+'_reader',base/'certificate_io.py')
 j=module(namespace+'_bridge',base/'frontier/j-geometry/j_face_coupled_seven_heads.py')
 pre,_,desc,density=j.source_tables(F(1,135));g=F(1,135);lo,hi=F(1,405),F(1,270)
 def tables(theta):
  theta=F(theta);require(lo<=theta<=hi,'Actual remaining b1 late-source interval after fixing original405 cell')
  raw=[[j.ETA[c]*pre[c][s]for s in range(5)]for c in range(5)]
  raw[2][4]-=g;raw[3][2]-=theta;raw[4][2]-=F(1,270)-theta
  return pre,raw,desc,density
 j.source_tables=tables;j.LO=lo;j.HI=hi;j.Z2=F(43,700)-8*g/35;j.Z4=F(1,28)-2*g/35
 complete_positive=F(3,20)-2*g/5;pure7=F(1,4)/5
 payments=[F(1,8)*F(6,35),(F(1,10)-g)*F(6,35),F(1,12)*F(6,35),(F(1,15)-g)*F(6,35)]
 require(complete_positive-pure7-sum(payments[:2])==j.Z2>0,'Full positive7 tail after21/35,including all omitted7 depths')
 require(complete_positive-pure7-sum(payments)==j.Z4>0,'Full positive7 tail after21/35/63/105,including all omitted7 depths')
 endpoints=[]
 for theta in(lo,hi):
  p,raw,e,w=tables(theta);flat=[x for row in raw for x in row]
  require([sum(flat[:5]),sum(flat[5:10]),sum(flat[10:])]==[F(1,24),F(1,12),F(1,8)+F(1,120)],'Exact source group cap sums')
  require(min(flat[i]for i in j.SUPPORT)>=F(1,120)and{i for i in range(10,25)if flat[i]>0}==set(j.SUPPORT),'Exact eight-support closed capacity LP on all theta')
  endpoints.append({'theta':theta,'raw_upper':raw})
 require(F(1,20)/9+F(1,18)/20==F(1,120),'All beta/deep-late source tails retained in common raw budget')
 head=j.SaturatedJCoupledSevenHead(base)
 return {'io':io,'j':j,'head':head,'actual_source_mass':F(1,4),'actual_survivor_mass':F(413,2700),
  'g':g,'lo':lo,'hi':hi,'complete_positive7':complete_positive,'positive7_head_payments':payments,'source_affine_endpoints':endpoints,
  'source_sha256':{p:sha256(io.read_artifact_bytes(base/p)).hexdigest()for p in('frontier/j-geometry/j_face_coupled_seven_heads.py','frontier/endpoint-bounds/k_face_common_seven_hinges.py')},
  'scope':'Actual aligned equality source. Rawtable literal135 hole;normalized profiles omit that hole safely. All old-zero7 tail caps and complete deletion marginals from312. No numerical saturated source bound reused.'}


def strengthen(data):
 j,head=data['j'],data['head'];require=j.require
 support=(13,17,18,22,23);fixed=(14,19,24)
 require(j.SUPPORT==(13,14,17,18,19,22,23,24),'Strengthen only the original aligned relaxation once')
 for theta in(j.LO,j.HI):
  cap=[v for row in j.source_tables(theta)[1]for v in row]
  require(min(cap[i]for i in support)>=F(1,120),'BQ alone can absorb all omitted beta/deep-late source mass')
  require([cap[i]for i in fixed]==[F(2,135),F(1,45),F(1,45)],'Literal135 hole and exact H source masses')
 j.SUPPORT=support
 def lp_bound(coefficients,capacities,budgets):
  require(len(coefficients)==len(capacities)==25 and len(budgets)==3,'Whole scaled capacity LP')
  require(min(coefficients)>=0 and min(capacities)>=0,'Nonnegative head and caps')
  total=0;records=[]
  for indices,budget in zip((tuple(range(5)),tuple(range(5,10))),budgets[:2]):
   require(sum(capacities[i]for i in indices)==budget,'Actual root0 caps force every rectangle mass')
   value=sum(coefficients[i]*capacities[i]for i in indices)
   records.append({'value':value,'fixed_allocation':[capacities[i]for i in indices]});total+=value
  fixed_value=sum(coefficients[i]*capacities[i]for i in fixed)
  remaining=budgets[2]-sum(capacities[i]for i in fixed)
  available=sum(capacities[i]for i in support)
  loss=available-remaining
  require(0<=loss<=min(capacities[i]for i in support),'Every minimum BQ cap can absorb full source omission')
  least=min(support,key=lambda i:(coefficients[i],i));gamma=coefficients[least]
  allocation={i:capacities[i]-(loss if i==least else 0)for i in support}
  alpha={i:max(0,coefficients[i]-gamma)for i in support}
  primal=sum(coefficients[i]*allocation[i]for i in support)
  dual=gamma*remaining+sum(alpha[i]*capacities[i]for i in support)
  require(sum(allocation.values())==remaining and min(allocation.values())>=0,'BQ primal source masses fit all caps and exact budget')
  require(all(gamma+alpha[i]>=coefficients[i]for i in support)and min(alpha.values())>=0,'All BQ exact weak-dual inequalities')
  require(primal==dual==sum(coefficients[i]*capacities[i]for i in support)-loss*gamma,'Matching BQ primal/dual objective with fixed H')
  value=fixed_value+dual;records.append({'value':value,'fixed_H_value':fixed_value,'gamma':gamma,'alpha':alpha,'allocation':allocation});total+=value
  return total,records
 head.bridge.lp_bound=lp_bound
 data.update(fixed_H_support=fixed,source_omission_support=support,fixed_H_raw_masses=[F(2,135),F(1,45),F(1,45)])
 return data

def build_joint(base,data):
 j,head,io=data['j'],data['head'],data['io'];require=j.require
 rawmod=module('aligned_joint_raw',base/'frontier/source-budgets/joint_selected_source_comparison.py')
 ret=module('aligned_joint_retained',base/'frontier/retained-transport/retained_deletion_heavy_comparison.py')
 joint=module('aligned_joint_scan',base/'frontier/j-geometry/j_face_joint_selected_heads.py')
 p,a,e,w=j.source_tables(j.LO)
 class Bridge:
  ROOT=j.ROOT
  GROUPS=[list(range(5)),list(range(5,10)),list(range(10,25))]
  GROUP_MASSES=[F(1,24),F(1,12),F(1,8)]
  @staticmethod
  def source_tables(_):return p,a,w,e
 raw=rawmod.RawSelectedLP(Bridge())
 lp=SimpleNamespace(nvars=876,rows=[dict(r)for r in raw.rows],rhs=list(raw.rhs),equalities=[dict(r)for r in raw.equalities],erhs=[F(1)]*4,lambda_groups=raw.lambda_groups)
 lp.rows[17][875]=j.HI-j.LO;lp.rows[22][875]=-(j.HI-j.LO)
 def add(row,rhs):lp.rows.append(row);lp.rhs.append(rhs);return len(lp.rows)-1
 lp.theta_upper=add({875:F(1)},F(1));lp.y_link=[]
 flatw=[v for r in w for v in r]
 for cell in range(25):
  for mask in range(16):
   k=16*cell+mask;lp.y_link.append(add({425+k:F(1),k:-flatw[cell]},F(0)))
 lp.equalities +=[{425+k:F(1)for k in range(400)},{k:F(1)for k in range(400)}];lp.erhs +=[F(413,2700),F(1,4)]
 for bit,cap in enumerate((F(13,750),F(11,540),F(1,75),F(11,1620))):
  add({425+16*cell+mask:F(1)for cell in range(25)for mask in range(16)if mask>>bit&1},cap)
 lp.e3_zero={}
 for cell in range(25):
  row={825+cell:F(1),850+cell:F(1)}
  for mask in range(16):row[16*cell+mask]=-flatw[cell];row[425+16*cell+mask]=F(1)
  add(row,F(0))
  if cell//5>=2:lp.e3_zero[825+cell]=add({825+cell:F(1)},F(0))
 for s in range(5):lp.equalities.append({825+s:F(1),830+s:F(1)});lp.erhs.append(j.QSLOTS[s]/90)
 for c in range(5):lp.equalities.append({850+5*c+s:F(1)for s in range(5)});lp.erhs.append(j.ETA[c]*(1+int(c>=2))/100)
 # E5 contains only b>=2; its product projections remain exact under312.
 # E3 is supported on root0; the original135 hole lies entirely in root1.
 for bit,div in ((1,3),(3,9)):
  for c in range(1,5):
   row={lp.lambda_groups[bit][c]:j.ETA[c]*(1+int(c>=2))/(100*div)}
   for slot in range(5):
    cell=5*c+slot
    for mask in range(16):
     if mask>>bit&1:row[16*cell+mask]=-flatw[cell];row[425+16*cell+mask]=F(1)
   add(row,F(0))
 for bit in (0,2):
  row={lp.lambda_groups[bit][slot]:F(1,2250)for slot in (1,2,4)}
  for cell in range(25):
   for mask in range(16):
    if mask>>bit&1:row[16*cell+mask]=-flatw[cell];row[425+16*cell+mask]=F(1)
  add(row,F(0))
 marked_rows=list(range(len(lp.rows)-10,len(lp.rows)))
 require(len(lp.equalities)==16,'Original complete projected deletion marginal order retained')
 # The hole is actual I27 x H, mass1/135. AE3 fixes every other H point.
 # Only raw masses are fixed here; no source hole is smeared into the p table.
 for cell,cap in zip((14,19,24),(F(2,135),F(1,45),F(1,45))):
  require(a[cell//5][cell%5]==cap,'Literal aligned H cell cap')
  lp.equalities.append({16*cell+mask:F(1)for mask in range(16)});lp.erhs.append(cap)
 lp.columns=[[]for _ in range(lp.nvars)];lp.eqcolumns=[[]for _ in range(lp.nvars)]
 for i,r in enumerate(lp.rows):
  for k,v in r.items():lp.columns[k].append((i,v))
 for i,r in enumerate(lp.equalities):
  for k,v in r.items():lp.eqcolumns[k].append((i,v))
 lp.check_dual=MethodType(ret.RetainedDeletionLP.check_dual,lp)
 require(len(lp.rows)==587 and len(lp.equalities)==19 and len(lp.columns)==876,'Complete aligned876-column,587-inequality,19-equality model')
 require(lp.rows[17][875]==F(1,810)and lp.rows[22][875]==-F(1,810),'Original405 forces exact common aligned theta interval')
 require(all(0<=k<876 and isinstance(v,F)for row in lp.rows+lp.equalities for k,v in row.items()),'All source coefficients exact')
 lp.raw_specification=raw.specification()
 body=encode([lp.rows,lp.rhs,lp.equalities,lp.erhs])
 specification={'variables':876,'inequalities':587,'equalities':19,'rows_sha256':sha256(json.dumps(body,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
  'actual_source_mass':F(1,4),'actual_survivor_mass':F(413,2700),'complete_mean_upper':F(293,450),'late_split_interval':[j.LO,j.HI],
  'raw_model':lp.raw_specification,'selected_moduli':[25,27,75,81],'selected_survivor_caps':[F(13,750),F(11,540),F(1,75),F(11,1620)],
  'fixed_H_raw_masses':[F(2,135),F(1,45),F(1,45)],'marked_residual_rows':marked_rows,
  'deep3_slot_marginals':[q/90 for q in j.QSLOTS],'deep5_cell_marginals':[eta*(1+int(c>=2))/100 for c,eta in enumerate(j.ETA)],
  'scope':'Actual completed aligned312 endpoint. The selected-profile table deliberately ignores the literal135 hole when taking an upper. E3 lives in root0; E5 uses only b>=2, so all ten marked deletion rows retain their exact old coefficients. No saturated-source numerical bound or dual is reused.'}
 problem=joint.JointSelectedJHead.__new__(joint.JointSelectedJHead)
 problem.j=j;problem.head=head;problem.lp=lp;problem.specification=encode(specification)
 problem.bank={};problem.proposer=None;problem.used=set();problem.verified={}
 return {'problem':problem,'lp':lp,'specification':specification,'joint':joint}

CERTIFICATE='certificates/source_norms/j-geometry/j_aligned_joint_selected_heads.json'
ORIGINAL='certificates/source_norms/j-geometry/j_face_heavy_positive175189_complete_moment_cost_comparison.json'
SOURCES=('certificate_io.py','frontier/j-geometry/j_face_coupled_seven_heads.py','frontier/endpoint-bounds/k_face_common_seven_hinges.py',
 'frontier/source-budgets/joint_selected_source_comparison.py','frontier/retained-transport/retained_deletion_heavy_comparison.py','frontier/j-geometry/j_face_joint_selected_heads.py',
 ORIGINAL,'profile-notes/257-320/312-an-aligned-j-source-has-a-complete-own-test-and-residual-deletion-interface.md',
 'certificates/source_norms/j-geometry/j_aligned_own_test_interface.json',
 'profile-notes/257-320/311-imperfect-j-source-alignment-forces-a-sharp-sector-surplus.md')
TARGETS=('AP11-0','AP11-1','AP11-2','hinge4','cost0')

def original_coefficients(basis):
 low=list(map(F,basis['low_load_values']));poly=list(map(F,basis['tail_polynomial']))
 require(len(low)==8 and len(poly)==3 and low[0]==poly[2]==0,'Original centered affine-tail function')
 slopes=[F(0)]+[b-a for a,b in zip(low,low[1:])]+[poly[1]]
 a={t:slopes[t]-slopes[t-1]for t in range(1,9)if slopes[t]!=slopes[t-1]}
 require(min(a.values())>0,'Exact original positive hinge combination')
 require([sum(v*max(n-t,0)for t,v in a.items())for n in range(1,9)]==low,'All original low integer loads')
 require([-sum(t*v for t,v in a.items()),sum(a.values()),F(0)]==poly,'Original infinite affine continuation')
 return a

def actual_nonempty_embedding(data,lp):
 """The311 completed example with legal source-null selected test events."""
 j=data['j'];raw=[list(row)for row in j.source_tables(j.HI)[1]]
 raw[3][3]-=F(1,360);raw[4][3]-=F(1,180)
 e3=[[F(0)]*5 for _ in range(5)];e5=[[F(0)]*5 for _ in range(5)]
 for s in range(5):e3[0][s]=j.QSLOTS[s]/90
 for c in range(5):e5[c][3]=j.ETA[c]*(1+int(c>=2))/100
 other=[[F(0)]*5 for _ in range(5)]
 other[1][4]=F(1,225);other[1][3]=F(1,900);other[3][4]=F(1,450);other[3][3]=F(1,1800)
 w=j.source_tables(j.HI)[3]
 y=[[w[c][s]*raw[c][s]-e3[c][s]-e5[c][s]-other[c][s]for s in range(5)]for c in range(5)]
 require(sum(map(sum,raw))==F(1,4)and sum(map(sum,y))==F(413,2700),'Complete actual source and survivor masses')
 x=[F(0)]*876
 for c,s in product(range(5),repeat=2):
  i=5*c+s;x[16*i]=raw[c][s];x[425+16*i]=y[c][s];x[825+i]=e3[c][s];x[850+i]=e5[c][s]
 for group in lp.lambda_groups:x[group[0]]=F(1)
 x[875]=F(1)
 require(min(x)>=0,'Nonnegative actual source embedding')
 slacks=[rhs-sum(v*x[k]for k,v in row.items())for row,rhs in zip(lp.rows,lp.rhs)]
 residuals=[rhs-sum(v*x[k]for k,v in row.items())for row,rhs in zip(lp.equalities,lp.erhs)]
 require(min(slacks)>=0 and set(residuals)=={F(0)},'Every one of587 inequalities and19 equalities holds at the actual limiting-family witness')
 return {'raw':raw,'survivor':y,'deep3_deletion':e3,'deep5_deletion':e5,'other_deletion':other,
  'nonnegative_coordinates':876,'inequalities_checked':len(slacks),'equalities_checked':len(residuals),
  'minimum_inequality_slack':min(slacks),'scope':'One actual311 limiting source with legally null selected events. This is not a realization theorem for arbitrary LP points.'}

def consumer_account(original,rows):
 basis={r['name']:F(r['upper'])for r in original['basis']}
 targets={r['name']:{k:F(v)for k,v in r['coefficients'].items()}for r in original['proof_data']}
 require(len(basis)==34 and len(targets)==59 and len(original['cost_weights'])==52,'Original complete299 consumer inventory')
 get=lambda t,k:targets[t].get(k,F(0))
 alpha=F(original['count_law']['remaining_hinge1_coefficient']);beta=F(original['count_law']['whole_constant_coefficient'])
 require((alpha,beta)==(F(1,7986),F(1,87846)),'Full original count-law tail remains separate')
 E,G={},{}
 for k in basis:
  unit=F(k=='mass');tail=alpha*get('mean',k)+(beta-alpha)*unit
  E[k]=unit-get('hinge4',k)/6-(sum(get('AP11-'+str(i),k)for i in range(4))+tail)/7
  N=F(original['signed_mass_coefficient'])*unit+F(original['complete_square_weight'])*get('square',k)+sum(F(v)*get('cost-'+str(i),k)for i,v in enumerate(original['cost_weights']))
  G[k]=(403-F(original['offset']))*E[k]-N
 value=lambda co,bo:sum(co[k]*bo[k]for k in bo)
 require(value(E,basis)==F(original['comparison_upper']['denominator'])and value(G,basis)==F(original['comparison_upper']['target403_numerator_margin']),'Exact original complete consumer recovered')
 require(all(E[k]<=0 and G[k]<=0 for k in basis if k!='mass'),'Original upper observations enter monotonically')
 adjusted=dict(basis,mass=F(413,2700),mean=F(293,450));eb,gb=value(E,adjusted),value(G,adjusted)
 active={k for k in basis if(E[k]or G[k])and k not in('mass','mean')}
 require(len(active)==16,'Sixteen original source observations need their own aligned bounds')
 paid=[]
 for row in rows:
  name=row['name'];gap=max(row['complete_upper']-basis[name],F(0))
  paid.append({'name':name,'reference_upper':basis[name],'complete_actual_upper':row['complete_upper'],
   'nonnegative_gap':gap,'denominator_price':-E[name],'signed403_price':-G[name],
   'denominator_cost':-E[name]*gap,'signed403_cost':-G[name]*gap})
 firstfour=[r for r in paid if r['name']!='cost0']
 return {'original_observations':16,'proved_observations':len(paid),'remaining_observations':sorted(active-{r['name']for r in paid}),
  'conditional_initial_denominator':eb,'conditional_initial_signed403_margin':gb,
  'proved_source_costs':paid,'conditional_margin_after_AP_and_H4':gb-sum(r['signed403_cost']for r in firstfour),
  'conditional_denominator_after_all_five':eb-sum(r['denominator_cost']for r in paid),
  'conditional_margin_after_all_five':gb-sum(r['signed403_cost']for r in paid),
  'whole_count_tail_coefficients':[alpha,beta],
  'scope':'Exact accounting of fixed299 recipes with actual312 mass/mean and the five new source bounds. Eleven other aligned source bounds are still unproved here. A negative remaining margin rules out closing this accounting from these upper values alone; it is not a lower bound on an actual family and does not rule out stronger observations or new recipes.'}

def calculate(base,given):
 data=strengthen(build_source(base,'canonical_aligned313'));io=data['io']
 read=lambda p:json.loads(io.read_artifact_bytes(p),object_pairs_hook=io._unique)
 pins={path:sha256(io.read_artifact_bytes(base/path)).hexdigest()for path in SOURCES}
 original=read(base/ORIGINAL);bases={r['name']:r for r in original['basis']}
 new=build_joint(base,data);problem=new['problem'];lp=new['lp'];problem.bank=given['rational_duals']
 seeds=given['seeds'];require(set(seeds)==set(TARGETS),'Exactly five original target seed schedules')
 witness=actual_nonempty_embedding(data,lp);rows=[]
 for name in TARGETS:
  a=original_coefficients(bases[name]);seed=seeds[name];layout=tuple(seed['layout']);projection=tuple(seed['projection21_35_63_105'])
  require(len(layout)==7 and all(0<=v<limit for v,limit in zip(layout,(2,5,5,2,5,5,5)))and len(projection)==5 and all(0<=v<limit for v,limit in zip(projection,(2,5,5,2,5))),'Valid independent original containing choices used only to schedule pruning')
  source={'index':name,'scan':{'coefficients':a,'maximizing_witness':{'layout':layout,**dict(zip(('seven21_root','seven35_slot','seven63_cell','seven105_root','seven105_slot'),projection))}}}
  scan=problem.scan(source);upper=scan['complete_hinge_upper']
  rows.append({'name':name,'original_low_load_values':bases[name]['low_load_values'],'original_tail_polynomial':bases[name]['tail_polynomial'],
   'scan':scan,'complete_upper':upper})
  print('Complete aligned '+name+' <= '+str(upper)+' = '+str(float(upper)),flush=True)
 require(problem.used==set(problem.bank),'Every stored new-source dual is consumed and every required dual is present')
 return encode({'schema':'erdos7-aligned-joint-selected-heads-v1','source_sha256':pins,
  'domain':'Actual completed aligned312 endpoint qJ=1,rho=2/675,original45 and135 in one root1 cell; uniform limiting statement for actual finite sources approaching this endpoint.',
  'actual_source_mass':F(1,4),'actual_survivor_mass':F(413,2700),'complete_mean_upper':F(293,450),
  'model':new['specification'],'actual_nonempty_embedding':witness,'seeds':seeds,'results':rows,
  'rational_duals':{k:problem.bank[k]for k in sorted(problem.used)},'distinct_dual_count':len(problem.used),
  'rational_dual_columns_checked':876*len(problem.used),'total_containing_choices':6250000*len(rows),
  'fixed299_consumer_account':consumer_account(original,rows),
  'scope':'Five complete independently labelled original source bounds,all selected and omitted exponent/cofactor tails. No common optimizer or actual attainment of relaxed maxima. No explicit finite-source radius,positive403 comparison,unrestricted Erdos7 resolution,or Lean verification.'})

def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2]);parser.add_argument('--certificate',type=Path)
 mode=parser.add_mutually_exclusive_group();mode.add_argument('--write',action='store_true');mode.add_argument('--check',action='store_true')
 args=parser.parse_args();base=args.base.resolve();path=args.certificate or base/CERTIFICATE
 io=module('aligned313_canonical_input',base/'certificate_io.py')
 given=json.loads(io.read_artifact_bytes(path),object_pairs_hook=io._unique)
 result=calculate(base,given)
 if args.write:io.write_certificate_text(path,json.dumps(result,indent=2)+'\n');print('WROTE '+str(path),flush=True)
 else:require(result==given,'Every exact complete-source field reconstructed');print('PASS complete aligned313 source and five heads',flush=True)
if __name__=='__main__':main()
