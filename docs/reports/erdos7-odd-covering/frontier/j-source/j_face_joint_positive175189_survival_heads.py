#!/usr/bin/env python3
"""Complete actual J H4 with joint fresh positive-seven labels175 and189."""
from pathlib import Path
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from types import SimpleNamespace
from math import lcm
import argparse,importlib.util,json,sys
sys.dont_write_bytecode=True
CERTIFICATE='certificates/source_norms/j-source/j_face_joint_positive175189_survival_heads.json'
MODEL='4da5961945a50079d14a49fc0017409abeba79624086971f2c0747d63e8e494d'
U,L,N=12941,32141,32151
PINS={'frontier/j-source/j_face_retained375_survival_heads.py': '4229d9cc7248987ae1ff5fd04f674af37b2f7b3c3820e9101428bab3cec493dc', 'certificates/source_norms/j-source/j_face_retained375_survival_heads.json': '1aa84f59e967f07b290343f0f6ded7ac4df7041068a15d372f88c6ffb7e501ce', 'profile-notes/j-source/288-retaining375-strengthens-the-complete-j-survival-hinge.md': '69147427bcfdf28e74263a611345c6142c6185ab600f2bafd3a8eb5840c0f3b7'}

def require(ok,message):
 if not ok:raise ValueError(message)

def module(name,path):
 spec=importlib.util.spec_from_file_location(name,path)
 require(spec is not None and spec.loader is not None,'Loadable unchanged source')
 result=importlib.util.module_from_spec(spec);spec.loader.exec_module(result);return result

def encode(value):
 if isinstance(value,F):return str(value)
 if isinstance(value,dict):return {str(k):encode(v)for k,v in value.items()}
 if isinstance(value,(list,tuple)):return [encode(v)for v in value]
 return value

def batches(rows,size):return [rows[i:i+size]for i in range(0,len(rows),size)]

def ui(state,k,bit,joint):return U+6400*(joint-1)+3200*bit+400*state+k

def make_problem(B):
 load=lambda name:module("joint175189_"+name.replace("/","_"),B/(name+".py"))
 base=load('frontier/j-source/j_face_retained375_survival_heads');data=base.make_extended_model(B);old=data['lp']
 j,triple,depth,codec,io=(data[k]for k in('j','triple','depth','codec','io'))
 published=json.loads(io.read_artifact_bytes(B/base.CERTIFICATE));require(data['model']==published['model'],'All original375 source constraints')
 lp=SimpleNamespace(nvars=N,rows=[dict(r)for r in old.rows],rhs=list(old.rhs),equalities=[dict(r)for r in old.equalities],erhs=list(old.erhs),unit_rows=list(old.unit_rows))
 def add(r,rhs=F(0)):
  lp.rows.append({k:F(v)for k,v in r.items()if v});lp.rhs.append(F(rhs))
 def original(state,k):
  if state:return {triple.U+400*(state-1)+k:F(1)}
  return {k:F(1),**{triple.U+400*(st-1)+k:F(-1)for st in range(1,8)}}
 def atom(state,k,bit):
  col=6531+400*state+k
  if bit:return {col:F(1)}
  return {**original(state,k),col:F(-1)}
 for bit,state,k in product(range(2),range(8),range(400)):
  row={ui(state,k,bit,joint):F(1)for joint in range(1,4)}
  for c,v in atom(state,k,bit).items():row[c]=-v
  add(row)
 pre,absolute,desc,w=j.source_tables(j.LO);labels=(25,27,75,81,135,125,225,375);crt=[]
 for which,cofactor,cap in [(0,25,F(1,50)),(1,27,F(1,36))]:
  lp.equalities.append({L+5*which+s:F(1)for s in range(5)});lp.erhs.append(F(1))
  states=[joint for joint in range(1,4)if joint>>which&1]
  for cell in range(25):
   c,s=divmod(cell,5);row={ui(state,16*cell+mask,bit,joint):F(1)for joint,bit,state,mask in product(states,range(2),range(8),range(16))}
   row[L+5*which+(s if which==0 else c)]=-desc[c][s]/25 if which==0 else -pre[c][s]/27
   add(row)
  add({ui(state,k,bit,joint):F(1)for joint,bit,state,k in product(states,range(2),range(8),range(400))},cap)
  for idx,d in enumerate(labels):
   row={}
   for joint,bit,state,k in product(states,range(2),range(8),range(400)):
    mask=k%16;occupied=(mask>>idx&1)if idx<4 else((state>>(idx-4)&1)if idx<7 else bit)
    if occupied:row[ui(state,k,bit,joint)]=F(1)
   bound=F(1,lcm(cofactor,d));add(row,bound);crt.append({'cofactor':cofactor,'old_label':d,'lcm':lcm(cofactor,d),'raw_upper':bound})
 add({ui(state,k,bit,3):F(1)for bit,state,k in product(range(2),range(8),range(400))},F(1,675))
 for c in range(U,N):lp.unit_rows.append(len(lp.rows));add({c:F(1)},F(1))
 require(lp.rows[:len(old.rows)]==old.rows and lp.rhs[:len(old.rhs)]==old.rhs and lp.equalities[:20]==old.equalities and lp.erhs[:20]==old.erhs,
         'Every original row,bound,equality and unit-repair row remains unchanged')
 require(N==32151 and len(lp.rows)==56133 and len(lp.equalities)==22 and len(lp.unit_rows)==N,'Exactly the complete joint raw-only model dimensions')
 lp.columns=[[]for _ in range(N)];lp.eqcolumns=[[]for _ in range(N)]
 for i,row in enumerate(lp.rows):
  for c,v in row.items():lp.columns[c].append((i,v))
 for i,row in enumerate(lp.equalities):
  for c,v in row.items():lp.eqcolumns[c].append((i,v))
 lp.checker=codec.IntegerDualChecker(lp);lp.check_dual=lp.checker.check
 modelhash=sha256(json.dumps(encode([lp.rows,lp.rhs,lp.equalities,lp.erhs]),sort_keys=True,separators=(',',':')).encode()).hexdigest()
 require(modelhash==MODEL,'The entire joint raw-atom matrix has the declared exact rational identity')
 difference={}
 for v,m,e,size in product(range(1,15),range(5),range(5),range(1,3)):
  diff=depth.seven_increment(4,v,m+size,e)-depth.seven_increment(4,v,m,e)
  require(0<=diff<=size*F(6,35)and(v<4 or diff==size*F(6,35)),'Exact full raw cap increment for every original count')
  difference[v,m,e,size]=diff
 def objective(lay,pr,new):
  obj,const=base.complete_objective(data,lay,pr,new);obj+=[F(0)]*(N-len(obj))
  H=data['reference'].head.bridge.head_load(lay);r,s,c63,r105,s105,r147,s245=pr;c441,r735,s735=new
  for i,b in enumerate(H):
   c,slot=divmod(i,5);m=int(j.ROOT[c]==r)+int(slot==s)+int(c==c63)+int(j.ROOT[c]==r105 and slot==s105)
   e=int(j.ROOT[c]==r147)+int(slot==s245)+int(c==c441)+int(j.ROOT[c]==r735 and slot==s735)
   for joint,bit,state,mask in product(range(1,4),range(2),range(8),range(16)):
    v=b+mask.bit_count()+state.bit_count()+bit;obj[ui(state,16*i+mask,bit,joint)]=difference[v,m,e,joint.bit_count()]
  require(const==F(5071,405000)+F(13,490),'Original complete375 tail before only the two fresh-label deductions')
  const-=F(3,875)+F(1,210)
  require(const==F(5071,405000)+F(337,18375)and min(obj)>=0 and len(obj)==N,'Every leaf has the complete unchanged tail and nonnegative full objective')
  return obj,const
 return {'lp':lp,'base':base,'data':data,'io':io,'codec':codec,'published':published,'objective':objective,'raw_CRT_caps':crt,
         'model':{'variables':N,'inequalities':len(lp.rows),'equalities':len(lp.equalities),'rows_sha256':modelhash}}


def branch_key(row):return tuple(tuple(row[k])for k in('layout','projection','projection441_735'))

def calculate(B,bank):
 problem=make_problem(B);lp,io,codec,published=(problem[k]for k in('lp','io','codec','published'))
 require(PINS,'Exact published original-source pins')
 pins=dict(published['source_sha256'])
 for path,pin in PINS.items():
  require(path not in pins or pins[path]==pin,'Consistent direct mathematical source '+path);pins[path]=pin
 for path,pin in pins.items():require(sha256(io.read_artifact_bytes(B/path)).hexdigest()==pin,'Pinned mathematical source '+path)
 oldpath='certificates/source_norms/j-source/j_face_second_cofactor_survival_heads.json'
 old=json.loads(io.read_artifact_bytes(B/oldpath));oldbank=codec.decode_dual_bank(old['encoded_rational_duals'],inequality_count=6354,equality_count=18)
 objective=problem['objective'];key_for=lambda obj:sha256(json.dumps([MODEL,encode(obj)],separators=(',',':')).encode()).hexdigest()
 used=set();verified={}
 def evaluate(identity):
  obj,const=objective(*identity);key=key_for(obj);require(key in bank,'A complete exact joint dual for every original unresolved branch')
  if key not in verified:verified[key]=lp.checker.check(obj,bank[key])
  used.add(key);return verified[key]+const,key,const
 seed=published['seed'];fixed,seedkey,constant=evaluate(branch_key(seed));previous=F(published['complete_AP13_upper'])
 require(0<fixed<previous<F(old['complete_AP13_upper']),'The original controller gives a strict fixed scheduling benchmark')
 original_ledger=problem['base'].complete_old_pruning(B,oldbank,fixed)
 require(F(original_ledger['old_complete280_H4_upper'])==F(old['complete_AP13_upper']),'The same original complete280 source fallback')
 old375bank=codec.decode_dual_bank(published['encoded_rational_duals'],inequality_count=30454,equality_count=20)
 records={branch_key(row):row for row in published['residual_leaf_results']}
 require(len(records)==len(published['residual_leaf_results']),'Original375 branch identities are unique')
 if branch_key(seed)not in records:
  records[branch_key(seed)]={**seed,'dual_key':published['seed_dual_key'],'complete375_upper':published['fixed_pruning_benchmark'],
                            'complete_tail_constant':published['complete_tail_constant']}
 leaves=original_ledger['remaining_eight_projection_leaves'];remaining=[];bounded=[];reused=[];oldchecks=0;reuse_digest=sha256()
 for index,leaf in enumerate(leaves):
  identity=branch_key(leaf);available=min(F(leaf['strongest_available_old_upper']),previous);record=records.get(identity);own=None;oldkey=None
  if record is not None:
   obj,const=problem['base'].complete_objective(problem['data'],*identity)
   oldkey=sha256(json.dumps([problem['data']['model']['rows_sha256'],encode(obj)],separators=(',',':')).encode()).hexdigest()
   require(oldkey==record['dual_key']and oldkey in old375bank and const==F(record['complete_tail_constant']),
           'Only an exact own-branch original375 objective and complete tail may reuse that dual')
   own=problem['data']['lp'].checker.check(obj,old375bank[oldkey])+const;oldchecks+=12941
   require(own==F(record['complete375_upper']),'Every reused original375 dual is checked on its own complete objective')
   available=min(available,own)
   reused.append({'leaf_index':index,'layout':identity[0],'projection':identity[1],'projection441_735':identity[2],
                  'dual_key':oldkey,'complete375_upper':own,'complete_tail_constant':const})
  row={**leaf,'original_prefix_leaf_index':index,'published_complete375_uniform_upper':previous,
       'checked375_branch_upper':own,'checked375_dual_key':oldkey,'strongest_available_upper':available}
  if available<=fixed:bounded.append(row);kind='bounded375'
  else:remaining.append(row);kind='remaining'
  reuse_digest.update(repr((kind,identity,str(available),oldkey)).encode())
 c=original_ledger['counts'];two=c['two_old_bounded']+c['two_enhanced_bounded'];four=c['four_old_bounded']+c['four_enhanced_bounded']
 six=c['six_old_bounded']+c['six_enhanced_bounded']+c['six_known_dual_bounded']
 require(c['layouts']==12500 and c['two_seen']==125000 and c['four_seen']==50*(c['two_seen']-two)
         and c['six_seen']==10*(c['four_seen']-four)and c['seven_seen']==5*(c['six_seen']-six)
         and c['eight_seen']==10*(c['seven_seen']-c['seven_bounded']),
         'Every complete independent original two/four/six/seven/eight prefix identity')
 prefix_count=25000*two+500*four+50*six+10*c['seven_bounded']+c['eight_bounded']+c['seed_bounded']
 require(prefix_count+len(leaves)==original_ledger['covered_containing_choices']==3125000000
         and len(leaves)==c['lp_remaining']==len(bounded)+len(remaining)
         and len({branch_key(r)for r in leaves})==len(leaves)
         and all(F(v)<=fixed for v in original_ledger['maximum_pruned_bounds'].values()),
         'Complete original domain,no missing or duplicate leaf,and every bounded prefix at the same threshold')
 results=[]
 for i,leaf in enumerate(remaining):
  identity=branch_key(leaf);upper,key,const=evaluate(identity);ownold=F(leaf['strongest_available_upper'])
  require(const==constant==F(5071,405000)+F(337,18375),'Exactly the same complete tails on every residual')
  results.append({'leaf_index':i,'layout':identity[0],'projection':identity[1],'projection441_735':identity[2],
                  'complete_joint_upper':upper,'previous_available_upper':ownold,'adopted_upper':min(upper,ownold),
                  'complete_tail_constant':const,'dual_key':key})
 upper=max([fixed]+[r['adopted_upper']for r in results])
 require(0<upper<previous and used==set(bank)and prefix_count+len(bounded)+len(results)==3125000000,
         'Every original choice has a complete bound,every rational dual is consumed,and the final full upper strictly improves')
 for path,pin in original_ledger['source_sha256'].items():
  require(path not in pins or pins[path]==pin,'Consistent complete prefix source closure '+path);pins[path]=pin
 for path,pin in pins.items():require(sha256(io.read_artifact_bytes(B/path)).hexdigest()==pin,'Stable final original source '+path)
 encoded=codec.encode_dual_bank({k:bank[k]for k in sorted(bank)},inequality_count=56133,equality_count=22)
 require(codec.decode_dual_bank(encoded,inequality_count=56133,equality_count=22)==bank,'Existing lossless complete rational dual codec')
 ledger={k:v for k,v in original_ledger.items()if k not in('remaining_eight_projection_leaves','existing256_duals_rechecked')}
 ledger['remaining_eight_projection_leaf_batches']=batches(leaves,100)
 ledger['existing256_dual_key_batches']=batches(original_ledger['existing256_duals_rechecked'],512)
 return encode({'schema':'erdos7-j-face-joint-positive175189-survival-heads-v1','source_sha256':pins,
  'geometry':published['geometry'],'source_mass':F(1,4),'survivor_mass':F(3,20),'name':'hinge4','threshold':4,
  'model':problem['model'],'original288_model':problem['data']['model'],
  'retained_old_labels':published['retained_old_labels'],'previous_retained_positive7_labels':published['retained_positive7_labels'],
  'new_positive7_labels':[175,189],'fresh_old_cofactors':[25,27],'independent_profile_dimensions':[5,5],
  'raw_CRT_caps':problem['raw_CRT_caps'],'joint_raw_cap':F(1,675),'assigned_removed_tail_caps':[F(3,875),F(1,210)],
  'complete_old_tail':F(5071,405000),'complete_positive7_tail':F(337,18375),'complete_tail_constant':constant,
  'original_controller':seed,'seed_dual_key':seedkey,'fixed_pruning_benchmark':fixed,'prefix_ledger':ledger,
  'prefix_bounded_original_choices':prefix_count,'original375_reuse':{'branch_reuse_count':len(reused),
   'bounded_leaf_count':len(bounded),'rational_column_checks':oldchecks,'branch_batches':batches(reused,100),
   'bounded_leaf_batches':batches(bounded,100),'remaining_leaf_batches':batches(remaining,100),'all_branch_decisions_sha256':reuse_digest.hexdigest()},
  'residual_leaf_count':len(results),'residual_leaf_batches':batches(results,100),'total_containing_choices':3125000000,
  'complete_AP13_upper':upper,'previous_complete_AP13_upper':previous,'improvement_over_previous':previous-upper,
  'encoded_rational_duals':encoded,'distinct_dual_count':len(bank),'rational_column_checks':N*len(verified),
  'scope':'Complete original H4/AP13 on both entire actual saturated J faces. The unchanged375 source is refined only on raw atoms by the two independent parent events for175 and189; each original branch LP contains both full independent five-coordinate profiles. Every3.125 billion original independent containing choice lies in an inherited complete prefix,an individually checked original375 branch,or an exactly checked joint-source residual. Every original source row,survivor/raw measure,common late interval,exponent/cofactor tail and original projection remains. Only assigned caps3/875 and1/210 are removed once,leaving old tail5071/405000 and positive-seven tail337/18375. The final upper is max(fixed seed,all own-leaf minima). No actual attainment,complete52-cost comparison,off-face/global extension,Lean verification,or unrestricted Erdos7 conclusion.'})

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
 g=p.add_mutually_exclusive_group();g.add_argument('--write',action='store_true');g.add_argument('--check',action='store_true')
 p.add_argument('--proposal',type=Path);args=p.parse_args()
 require((args.proposal is not None)==args.write,'Only the writer consumes an explicit complete proposal')
 io=module('joint175189_reader',args.base/'certificate_io.py');codec=module('joint175189_codec',args.base/'frontier/transport/retained135_heavy_comparison.py')
 candidate=json.loads(io.read_artifact_bytes(args.proposal if args.write else args.base/CERTIFICATE))
 bank=codec.decode_dual_bank(candidate['encoded_rational_duals'],inequality_count=56133,equality_count=22)
 result=calculate(args.base,bank)
 if args.write:io.write_certificate_text(args.base/CERTIFICATE,json.dumps(result,indent=2)+'\n')
 else:require(result==candidate,'Every complete original-domain joint-source field recomputes')
 print('PASS complete joint175189 H4;3125000000 choices;'+str(result['residual_leaf_count'])+' residuals;upper '+str(float(F(result['complete_AP13_upper']))),flush=True)

if __name__=='__main__':
 try:main()
 except(ValueError,ArithmeticError,OSError,KeyError,TypeError,json.JSONDecodeError)as e:
  print('FAIL: '+str(e),file=sys.stderr);raise SystemExit(1)
