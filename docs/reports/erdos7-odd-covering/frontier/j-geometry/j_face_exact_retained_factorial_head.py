#!/usr/bin/env python3
"""Complete J Phi5 bound using its exact retained head and selected-seven slope."""
from pathlib import Path
from fractions import Fraction as F
from hashlib import sha256
from types import MethodType
import argparse,importlib.util,json,sys
sys.dont_write_bytecode=True
CERTIFICATE='certificates/source_norms/j-geometry/j_face_exact_retained_factorial_head.json'
PINS={
 'frontier/j-geometry/j_face_joint_pair_factorial_heads.py':'28853a42f7b5d38004bad74245b8b1d46d4ad2764bc8be054d3d483df7cbb0eb',
 'certificates/source_norms/j-geometry/j_face_joint_pair_factorial_heads.json':'95a3eee9db33fb73c79160982df25c12a66e9f7a213b22c43c9def8b1949ad09',
 'profile-notes/257-320/276-actual-retained-tail-pairs-strengthen-original-j-costs-and-square.md':'397f1db9f44157a345c31826f96920ea8776db620cbeb62bbbfd671dd3eab652'}

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

def phi(n):return F(max(n-5,0)*max(n-4,0),2)
def head_gap(b,r):return phi(b)+max(b-4,0)*r+F(r*(r-1),2)-phi(b+r)
def slope_gap(b,r):return F(max(b-4,0)+r-max(b+r-4,0))

def correction_table():
 rows=[]
 for b in range(1,7):
  a=max(4-b,0)
  for r in range(7):
   gap,slope=head_gap(b,r),slope_gap(b,r)
   require(gap>=0 and slope==min(r,a)>=0
           and head_gap(b,r+1)-gap==slope,
           'Exact retained-only gap, capped slope deficit and discrete derivative')
   if b>=4:require(gap==slope==0,'Already quadratic head has no correction')
   else:require(gap==F(r*(r-1),2)-F(max(r-a,0)*max(r-a-1,0),2),
                'Exact below-threshold head correction')
   rows.append({'head':b,'retained_count':r,'exact_factorial':phi(b+r),
                'old_head_gap':gap,'selected_seven_slope_gap':slope})
 require(len(rows)==42,'All six original head counts and seven possible retained counts')
 return rows

def inputs(base):
 source=module('exact_retained_source276',base/'frontier/j-geometry/j_face_joint_pair_factorial_heads.py')
 data=source.inputs(base);io=data['io']
 old=json.loads(io.read_artifact_bytes(base/source.CERTIFICATE),object_pairs_hook=data['core'].unique)
 pins=dict(data['pins'])
 for path,pin in {**old['source_sha256'],**PINS}.items():
  require(path not in pins or pins[path]==pin,'Consistent complete source closure '+path);pins[path]=pin
 for path,pin in pins.items():require(sha256(io.read_artifact_bytes(base/path)).hexdigest()==pin,'Pinned original mathematical input '+path)
 require(old['geometry']==data['source274']['geometry'] and F(old['survivor_mass'])==F(3,20)
         and old['pair_partitions']==encode(data['payments'])
         and old['conditional_positive7']==encode(data['conditional'].record),
         'The same entire actual source, retained-pair payments and complete conditional PZZ')
 data.update(source=source,old=old,pins=pins)
 return data

def make_problem(base,data,bank,proposer=None):
 source=data['source']
 problem=source.make_problem(base,*(data[k]for k in('j','core','pair','depth','second','moment','shift','generalized','prior244','prior251')),
                            F(4879,7200),5,data['conditional'],data['payments'],bank=bank,proposer=proposer)
 problem.fc=F(1);problem.atone=F(0);original=problem.objective
 require(problem.specification==data['old']['model'],'All original3306 variables and source constraints remain')
 def objective(self,co,layout,projection):
  require(co=={} and self.k==5 and self.fc==1 and self.atone==0,'Exactly the pure Phi5 function')
  obj,constant=original(co,layout,projection)
  r,s,c63,r105,s105,r147,s245=projection
  for i,b in enumerate(self.head.bridge.head_load(layout)):
   c,slot=divmod(i,5)
   first=int(data['j'].ROOT[c]==r)+int(slot==s)+int(c==c63)+int(data['j'].ROOT[c]==r105 and slot==s105)
   second=int(data['j'].ROOT[c]==r147)+int(slot==s245)
   weight=F(1,5)+F(6,35)*first+F(6,245)*second
   for mask in range(16):
    cell=16*i+mask;q=mask.bit_count()
    obj[425+cell]-=head_gap(b,q);obj[cell]-=slope_gap(b,q)*weight
    for state,n in enumerate((1,1,2)):
     obj[data['pair'].V+400*state+cell]-=head_gap(b,q+n)-head_gap(b,q)
     obj[data['pair'].U+400*state+cell]-=(slope_gap(b,q+n)-slope_gap(b,q))*weight
    require(obj[425+cell]==phi(b+q) and obj[cell]==max(b+q-4,0)*weight,
            'Y carries the exact retained head and X its exact selected-seven slope')
    for state,n in enumerate((1,1,2)):
     require(obj[data['pair'].V+400*state+cell]==phi(b+q+n)-phi(b+q)
             and obj[data['pair'].U+400*state+cell]==(max(b+q+n-4,0)-max(b+q-4,0))*weight,
             'Each marked-state increment is exact on its own survivor/raw measure')
  require(len(obj)==3306 and all(isinstance(v,F)for v in obj)
          and all(v>=0 for col,v in enumerate(obj)if col!=875),
          'All state coefficients remain nonnegative, apart from the unchanged late secant')
  return obj,constant
 problem.objective=MethodType(objective,problem)
 return problem

def calculate(base,bank,seed):
 data=inputs(base);table=correction_table()
 require(seed['index']==-3 and seed['threshold']==5
         and seed==next(r for r in data['old']['seed_rows']if r['index']==-3),
         'The same sixty independent original Phi5 seed branches, with no optimality assumption')
 problem=make_problem(base,data,bank)
 scan=data['source'].pure_factorial_scan(problem,data['conditional'],seed['branches'])
 upper=scan['complete_cost_upper'];prior=next(F(r['adopted_upper'])for r in data['old']['results']if r['name']=='factorial5')
 require(0<upper<prior and scan['covered_containing_choices']==62500000,
         'A strict whole-domain improvement for the same full Phi5 function')
 kept={key:bank[key]for key in sorted(problem.used)}
 encoded=problem.codec.encode_dual_bank(kept,inequality_count=6354,equality_count=18)
 require(problem.codec.decode_dual_bank(encoded,inequality_count=6354,equality_count=18)==kept,
         'Only the existing exact rational dual codec is used')
 return encode({'schema':'erdos7-j-face-exact-retained-factorial-head-v1','source_sha256':data['pins'],
  'geometry':data['old']['geometry'],'source_mass':F(1,4),'survivor_mass':F(3,20),'model':problem.specification,
  'name':'factorial5','factorial_threshold':5,'expansion':data['source'].pure_factorial_expansion(),
  'correction_table':table,'cross_partitions':data['old']['cross_partitions'],'pair_partitions':data['payments'],
  'conditional_positive7':data['conditional'].record,'seed_rows':seed,'scan':scan,
  'complete_factorial_upper':upper,'previous_complete_factorial_upper':prior,'improvement_over_previous':prior-upper,
  'encoded_rational_duals':encoded,'distinct_dual_count':len(kept),'rational_column_checks':3306*len(kept),
  'scope':'Complete pure Phi5 on both entire actual saturated J faces, all62500000 independent original choices and all exponent tails. The six retained zero-seven labels are counted exactly before the remaining-tail inequality. Only their known survivor head gap and selected-positive-seven raw slope gap are removed. The same3306-variable constraints, all complete unselected old/positive-seven crosses and pair tails, common-theta secant and original valid full-function affine pruning remain. No actual-source attainment, off-face extension, complete52-cost comparison, Lean verification or unrestricted Erdos7 conclusion.'})

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
 g=p.add_mutually_exclusive_group();g.add_argument('--write',action='store_true');g.add_argument('--check',action='store_true')
 p.add_argument('--proposal',type=Path);args=p.parse_args()
 require((args.proposal is not None)==args.write,'Only a writer takes an explicit completed proposal')
 io=module('exact_retained_io',args.base/'certificate_io.py');core=module('exact_retained_json',args.base/'frontier/j-geometry/j_face_joint_selected_heads.py')
 candidate=json.loads(io.read_artifact_bytes(args.proposal if args.write else args.base/CERTIFICATE),object_pairs_hook=core.unique)
 codec=module('exact_retained_codec',args.base/'frontier/retained-transport/retained135_heavy_comparison.py')
 bank=codec.decode_dual_bank(candidate['encoded_rational_duals'],inequality_count=6354,equality_count=18)
 seed=candidate['results'][0]['seed_rows']if args.write else candidate['seed_rows']
 result=calculate(args.base,bank,seed)
 if args.write:io.write_certificate_text(args.base/CERTIFICATE,json.dumps(result,indent=2)+'\n')
 else:require(result==candidate,'Every complete exact-head certificate field recomputes')
 print('PASS exact retained Phi5;62500000 choices;'+str(result['distinct_dual_count'])+' exact3306-column duals.',flush=True)

if __name__=='__main__':
 try:main()
 except(ValueError,ArithmeticError,OSError,KeyError,TypeError,json.JSONDecodeError)as e:
  print('FAIL: '+str(e),file=sys.stderr);raise SystemExit(1)
