#!/usr/bin/env python3
"""Complete J Phi5 with an exact seven-retained head and selected-seven slope."""
from pathlib import Path
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from types import MethodType
import argparse,importlib.util,json,sys
sys.dont_write_bytecode=True
CERTIFICATE='certificates/source_norms/j-source/j_face_exact_seven_retained_factorial_head.json'
PINS={'frontier/j-source/j_face_triple_pair_factorial_heads.py': '08ef924528e9331c85033df20a1731e74c2a8191436375a490ecca3ac89a629e', 'certificates/source_norms/j-source/j_face_triple_pair_factorial_heads.json': 'cec974fc637ee57304f1b612c2a58a311ef677eb5a227279bf145279967cf5d1', 'profile-notes/j-source/282-seven-retained-old-labels-strengthen-the-complete-j-moments.md': '1f11dc95e3c705a5932b63db86503af0bcbbfb8b9597abd0e58d75081d1b5d39', 'frontier/j-source/j_face_exact_retained_factorial_head.py': '9b0771ef3004955019241135e79740f07771369a7da1052d20b122c1797b0799', 'certificates/source_norms/j-source/j_face_exact_retained_factorial_head.json': '1738b1fe9276a0b3014bc783fdf210804c3f3c108a19af27497fa94aee494f90', 'profile-notes/j-source/284-exact-retained-head-and-slope-sharpen-the-complete-j-factorial.md': 'bdc09c5f1ceb7b9f92640c3f45b191b45b8fec9812267b5b327609b9ddbcdc3e'}

def require(ok,message):
 if not ok:raise ValueError(message)

def module(name,path):
 s=importlib.util.spec_from_file_location(name,path)
 require(s is not None and s.loader is not None,'Loadable original mathematical source')
 m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m

def encode(value):
 if isinstance(value,F):return str(value)
 if isinstance(value,dict):return {str(k):encode(v)for k,v in value.items()}
 if isinstance(value,(list,tuple)):return [encode(v)for v in value]
 return value

def inputs(base):
 source=module('exact_seven_source282',base/'frontier/j-source/j_face_triple_pair_factorial_heads.py')
 exact=module('exact_seven_source284',base/'frontier/j-source/j_face_exact_retained_factorial_head.py')
 data=source.inputs(base);io=data['io'];read=lambda p:json.loads(io.read_artifact_bytes(base/p),object_pairs_hook=data['core'].unique)
 full7,prior=read(source.CERTIFICATE),read(exact.CERTIFICATE);pins=dict(data['pins'])
 for path,pin in {**full7['source_sha256'],**prior['source_sha256'],**PINS}.items():
  require(path not in pins or pins[path]==pin,'Consistent complete source closure '+path);pins[path]=pin
 for path,pin in pins.items():require(sha256(io.read_artifact_bytes(base/path)).hexdigest()==pin,'Pinned original mathematical input '+path)
 require(full7['geometry']==prior['geometry']and F(full7['survivor_mass'])==F(prior['survivor_mass'])==F(3,20)
         and full7['conditional_positive7']==prior['conditional_positive7']==encode(data['conditional'].record),
         'Both entire actual J faces, one survivor measure and complete conditional PZZ')
 data.update(source282=source,exact=exact,full7=full7,prior=prior,pins=pins)
 return data

def correction_table(exact):
 rows=[]
 for b in range(1,7):
  for r in range(8):
   gap,slope=exact.head_gap(b,r),exact.slope_gap(b,r)
   require(gap>=0 and slope==min(r,max(4-b,0))>=0 and exact.head_gap(b,r+1)-gap==slope,
           'Exact seven-retained head gap and its nonnegative discrete derivative')
   require(gap==F(r*(r-1),2)-F(max(r-max(4-b,0),0)*max(r-max(4-b,0)-1,0),2),
           'Closed exact head correction for all original head and retained counts')
   rows.append({'head':b,'retained_count':r,'exact_factorial':exact.phi(b+r),'old_head_gap':gap,'selected_seven_slope_gap':slope})
 require(len(rows)==48,'All six original head counts and eight retained counts')
 return rows

def make_problem(base,data,bank):
 source,exact,triple,j=(data[k]for k in('source282','exact','triple','j'))
 problem=source.make_problem(base,data,5,data['source'].pure_factorial_expansion(),bank)
 original=problem.objective
 require(problem.specification==data['full7']['model']and problem.lp.nvars==6531
         and len(problem.lp.rows)==11211 and len(problem.lp.equalities)==19,
         'Every original seven-retained model row and independent profile remains')
 def objective(self,co,layout,projection):
  require(co=={}and self.k==5 and self.fc==1 and self.atone==0,'Only the original complete pure Phi5 function')
  obj,constant=original(co,layout,projection);r,s,c63,r105,s105,r147,s245=projection
  for i,b in enumerate(self.head.bridge.head_load(layout)):
   c,slot=divmod(i,5)
   first=int(j.ROOT[c]==r)+int(slot==s)+int(c==c63)+int(j.ROOT[c]==r105 and slot==s105)
   second=int(j.ROOT[c]==r147)+int(slot==s245);weight=F(1,5)+F(6,35)*first+F(6,245)*second
   for mask in range(16):
    cell=16*i+mask;q=mask.bit_count()
    obj[425+cell]-=exact.head_gap(b,q);obj[cell]-=weight*exact.slope_gap(b,q)
    require(obj[425+cell]==exact.phi(b+q)and obj[cell]==weight*max(b+q-4,0),
            'Y exact survivor head and X exact selected-seven raw slope')
    for state in range(1,8):
     n=state.bit_count()
     obj[triple.V+400*(state-1)+cell]-=exact.head_gap(b,q+n)-exact.head_gap(b,q)
     obj[triple.U+400*(state-1)+cell]-=weight*(exact.slope_gap(b,q+n)-exact.slope_gap(b,q))
     require(obj[triple.V+400*(state-1)+cell]==exact.phi(b+q+n)-exact.phi(b+q)
             and obj[triple.U+400*(state-1)+cell]==weight*(max(b+q+n-4,0)-max(b+q-4,0)),
             'Exact marked-state increments on their own survivor and raw measures')
  require(len(obj)==6531 and isinstance(constant,F)and all(isinstance(v,F)for v in obj)
          and all(v>=0 for i,v in enumerate(obj)if i!=875),
          'Only the unchanged common-theta secant may be signed')
  return obj,constant
 problem.objective=MethodType(objective,problem);problem.original_objective=original
 return problem

def calculate(base,bank):
 data=inputs(base);table=correction_table(data['exact']);problem=make_problem(base,data,bank)
 prior=F(data['prior']['complete_factorial_upper']);oldbank=problem.codec.decode_dual_bank(data['full7']['encoded_rational_duals'],inequality_count=11211,equality_count=19)
 branches=data['prior']['seed_rows']['branches'];oldseeds=next(r for r in data['full7']['seed_rows']if r['name']=='factorial5')['branches']
 require(len(branches)==60 and [(r['layout'],r['projection'])for r in branches]==[(r['layout'],r['projection'])for r in oldseeds],
         'The same sixty original independent seed branches')
 key_for=lambda obj:sha256(json.dumps(encode(obj),separators=(',',':')).encode()).hexdigest()
 verified={};used=set()
 def checked(obj,key):
  require(key in bank,'Every supplied branch has an exact rational dual')
  if key not in verified:verified[key]=problem.lp.checker.check(obj,bank[key])
  used.add(key);return verified[key]
 seeds=[];seed_keys=set()
 for row in branches:
  layout,projection=tuple(row['layout']),tuple(row['projection']);obj,const=problem.objective({},layout,projection);key=key_for(obj)
  upper=checked(obj,key)+const;seed_keys.add(key)
  seeds.append({'layout':layout,'projection':projection,'upper':upper,'key':key,'constant':const})
 fixed=max(r['upper']for r in seeds)
 require(len(seed_keys)==60 and 0<fixed<prior,'Fixed threshold from exactly the sixty original seeds')
 counts={k:0 for k in('layouts','layout_bounded','projection_seen','conditional_bounded','new_dual_bounded','old_dual_bounded','remaining')}
 maxima={k:F(-1)for k in('layout','conditional','new_dual','old_dual')};leaves=[];known={};digest=sha256();oldchecks=0;dominance=0
 projections=tuple(product(range(2),range(5),range(5),range(2),range(5),range(2),range(5)))
 cond={p:tuple(data['conditional'].endpoints(p))for p in projections}
 for layout in data['j'].layouts():
  counts['layouts']+=1;parts=problem.parts(layout);oldline=tuple(p[0]+problem.pair_tail for p in parts)
  if max(oldline)<=fixed:
   counts['layout_bounded']+=1;maxima['layout']=max(maxima['layout'],max(oldline));digest.update(repr(('layout',layout,oldline)).encode());continue
  for projection in projections:
   counts['projection_seen']+=1
   line=tuple(p[0]+problem.pair_tail-F(89,240)+z for p,z in zip(parts,cond[projection]));upper=min(max(line),prior)
   if max(line)<=fixed:
    counts['conditional_bounded']+=1;maxima['conditional']=max(maxima['conditional'],max(line));digest.update(repr(('conditional',layout,projection,line)).encode());continue
   obj,const=problem.objective({},layout,projection);key=key_for(obj);bound=None;kind=None;bankkey=None
   # Freeze pruning to the sixty seed keys; residual duals cannot alter the partition.
   if key in seed_keys:
    bound=checked(obj,key)+const;kind='new_dual';bankkey=key
   else:
    original,original_const=problem.original_objective({},layout,projection)
    require(original_const==const and all(a<=b for a,b in zip(obj,original)),'Componentwise exact correction on the same nonnegative variables')
    dominance+=len(obj)
    oldkey=sha256(json.dumps([problem.specification['rows_sha256'],encode(original)],separators=(',',':')).encode()).hexdigest()
    if oldkey in oldbank:
     bound=problem.lp.checker.check(obj,oldbank[oldkey])+const;oldchecks+=len(obj);kind='old_dual';bankkey=oldkey
   if bound is not None:
    upper=min(upper,bound);known[key]={'bank':kind,'bank_key':bankkey,'upper':bound,'constant':const}
   if upper<=fixed:
    require(kind is not None,'A complete bound below the prior uniform bound uses a checked dual')
    counts[kind+'_bounded']+=1;maxima[kind]=max(maxima[kind],upper);digest.update(repr((kind,layout,projection,key,str(upper))).encode())
   else:
    counts['remaining']+=1
    leaves.append({'layout':layout,'projection':projection,'strongest_available_upper':upper,'affine_endpoints':line,'objective_key':key,'constant':const})
    digest.update(repr(('remaining',layout,projection,key,str(upper))).encode())
 require(counts['layouts']==12500 and counts['projection_seen']==5000*(12500-counts['layout_bounded'])
         and counts['projection_seen']==sum(counts[k]for k in('conditional_bounded','new_dual_bounded','old_dual_bounded','remaining'))
         and 5000*counts['layout_bounded']+counts['projection_seen']==62500000,
         'Exact complete partition of all62500000 original independent containing choices')
 require(all(v<=fixed for v in maxima.values())and len(leaves)==counts['remaining'],'Every bounded region and residual leaf is accounted for')
 results=[]
 for leaf in leaves:
  layout,projection=leaf['layout'],leaf['projection'];obj,const=problem.objective({},layout,projection);key=key_for(obj)
  require(key==leaf['objective_key']and const==leaf['constant'],'Every residual is the unchanged original full-function objective')
  upper=checked(obj,key)+const;old=leaf['strongest_available_upper']
  results.append({'layout':layout,'projection':projection,'complete_exact7_upper':upper,'previous_available_upper':old,
                  'adopted_upper':min(upper,old),'constant':const,'dual_key':key})
 upper=max([fixed]+[r['adopted_upper']for r in results])
 require(0<upper<prior and used==set(bank),'Strict complete improvement and every supplied exact dual consumed')
 encoded=problem.codec.encode_dual_bank(bank,inequality_count=11211,equality_count=19)
 require(problem.codec.decode_dual_bank(encoded,inequality_count=11211,equality_count=19)==bank,'Existing lossless exact rational dual codec')
 batch=lambda rows:[rows[i:i+100]for i in range(0,len(rows),100)]
 return encode({'schema':'erdos7-j-face-exact-seven-retained-factorial-head-v1','source_sha256':data['pins'],
  'geometry':data['prior']['geometry'],'source_mass':F(1,4),'survivor_mass':F(3,20),'model':problem.specification,
  'name':'factorial5','factorial_threshold':5,'expansion':data['source'].pure_factorial_expansion(),
  'retained_old_labels':data['source282'].RETAINED,'correction_table':table,
  'pair_partitions':data['triple_payments'],'conditional_positive7':data['conditional'].record,'seed_rows':seeds,
  'fixed_pruning_benchmark':fixed,'prefix_ledger':{'counts':counts,'maxima':maxima,'covered_containing_choices':62500000,
   'leaf_batches':batch(leaves),'used_dual_check_batches':batch([{'objective_key':key,**v}for key,v in known.items()]),
   'all_branch_decisions_sha256':digest.hexdigest(),'seed_dual_count':len(seed_keys),'original_dual_column_checks':oldchecks,
   'componentwise_objective_checks':dominance},'residual_leaf_batches':batch(results),'residual_leaf_count':len(results),
  'total_containing_choices':62500000,'complete_factorial_upper':upper,'previous_complete_factorial_upper':prior,
  'improvement_over_previous':prior-upper,'encoded_rational_duals':encoded,'distinct_dual_count':len(bank),
  'rational_column_checks':6531*len(verified),
  'scope':'Complete pure Phi5 on both entire actual saturated J faces, all62500000 independent original choices and all exponent tails. The seven original zero-seven labels25,27,75,81,135,125,225 are counted exactly on the unchanged6531-variable model. The exact nonnegative selected-positive-seven slope is bounded directly on the raw measure. Every original unselected old/positive-seven cross, complementary POO/POZ/PZZ pair tail, independent profile and common-theta secant remains. Pruning uses only the original sixty seed duals; every remaining leaf receives an exact6531-column certificate. No actual-source attainment, off-face/global joining, complete52-cost comparison, Lean verification or unrestricted Erdos7 conclusion.'})

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
 g=p.add_mutually_exclusive_group();g.add_argument('--write',action='store_true');g.add_argument('--check',action='store_true')
 p.add_argument('--proposal',type=Path);args=p.parse_args()
 require((args.proposal is not None)==args.write,'Only a writer takes an explicit completed proposal')
 io=module('exact_seven_io',args.base/'certificate_io.py');core=module('exact_seven_json',args.base/'frontier/j-source/j_face_joint_selected_heads.py')
 candidate=json.loads(io.read_artifact_bytes(args.proposal if args.write else args.base/CERTIFICATE),object_pairs_hook=core.unique)
 codec=module('exact_seven_codec',args.base/'frontier/transport/retained135_heavy_comparison.py')
 bank=codec.decode_dual_bank(candidate['encoded_rational_duals'],inequality_count=11211,equality_count=19)
 result=calculate(args.base,bank)
 if args.write:io.write_certificate_text(args.base/CERTIFICATE,json.dumps(result,indent=2)+'\n')
 else:require(result==candidate,'Every complete exact-seven certificate field recomputes')
 print('PASS exact seven-retained Phi5;62500000 choices;'+str(result['distinct_dual_count'])+' exact6531-column duals.',flush=True)

if __name__=='__main__':
 try:main()
 except(ValueError,ArithmeticError,OSError,KeyError,TypeError,json.JSONDecodeError)as e:
  print('FAIL: '+str(e),file=sys.stderr);raise SystemExit(1)
