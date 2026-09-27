#!/usr/bin/env python3
"""Retain independent original135/125 tests in complete actual J heads."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import lcm
from types import SimpleNamespace
import importlib.util
import json
from pathlib import Path
import sys
from time import perf_counter

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j-geometry/j_face_retained135125_heads.json'
PINS = {'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b', 'frontier/j-geometry/j_face_joint_selected_heads.py': '77c34ea38b4f11aabe721d401dddb1f70d992f991094bd29393f9f0aa4be921b', 'certificates/source_norms/j-geometry/j_face_joint_selected_heads.json': '67c0c79696a723ebdee9e8745c111c1da678f2916582498d61a5befecf45b0bf', 'frontier/retained-transport/retained135_heavy_comparison.py': '93ad67489e6ce429f45bd8888cfd8f6e5ac91b0bc3d4fbeebfedef9f7d4b84ac', 'profile-notes/129-192/130-the-whole-j-face-forces-source-anti-alignment.md': 'c9c11d0250836f7abc67eed901716f867b7a916a9797afcaa14b3f70584e33a8', 'profile-notes/193-256/219-one-late-source-split-controls-complete-saturated-j-heads.md': 'd0f78950c8ca3040b2a90c5b5d470655cd53e68f39b54d531f793915490ff73d', 'profile-notes/193-256/244-three-complete-j-heads-share-raw-survivor-and-marked-deletion.md': '56f83856783c4e3c68ac919a6bed36a0d00e41f19d1d78f3d83b3cc950c66118', 'profile-notes/193-256/225-two-original-tests-share-the-complete-retained-bridge.md': '27d5e9c311b5f1a949d35d5eab4d3dd5ec7f22febf6703bf12a728daf957b686'}
CAP135, CAP125 = F(1,135), F(13,3750)
U,V,L135,L125 = 876,2076,3276,3301


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name,path):
    spec = importlib.util.spec_from_file_location(name,path)
    require(spec is not None and spec.loader is not None,'Loadable existing mathematical provider')
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def encode(value):
    if isinstance(value,F): return str(value)
    if isinstance(value,dict): return {str(k):encode(v) for k,v in value.items()}
    if isinstance(value,(list,tuple)): return [encode(v) for v in value]
    return value


def make_lp(base, j, original):
 old = original
 exact = module("j_pair_exact_dual", base/"frontier/retained-transport/retained135_heavy_comparison.py")
 lp=SimpleNamespace(nvars=3306,rows=[dict(r)for r in old.rows],rhs=list(old.rhs),equalities=[dict(r)for r in old.equalities],erhs=list(old.erhs));p,a,e,w=j.source_tables(j.LO);flatw=[v for row in w for v in row]
 def add(row,b=F(0)):lp.rows.append(row);lp.rhs.append(b)
 for cols in(range(L135,L125),range(L125,3306)):lp.equalities.append({i:F(1)for i in cols});lp.erhs.append(F(1))
 for i in range(25):
  cc,ss=divmod(i,5)
  add({L135+i:-p[cc][ss]/27,**{U+400*st+16*i+m:F(1)for st in(0,2)for m in range(16)}})
  add({L125+ss:-e[cc][ss]/125,**{U+400*st+16*i+m:F(1)for st in(1,2)for m in range(16)}})
  for m in range(16):
   k=16*i+m;add({k:F(-1),**{U+400*st+k:F(1)for st in range(3)}});add({425+k:F(-1),**{V+400*st+k:F(1)for st in range(3)}})
   complement={425+k:F(1),k:-flatw[i]}
   for st in range(3):
    uk,vk=U+400*st+k,V+400*st+k;add({vk:F(1),uk:-flatw[i]});complement[vk]=F(-1);complement[uk]=flatw[i]
   add(complement)
 for states,cap in(((0,2),CAP135),((1,2),CAP125)):add({V+400*st+k:F(1)for st in states for k in range(400)},cap)
 for label,states in((135,(0,2)),(125,(1,2))):
  for bit,oldlabel in enumerate((25,27,75,81)):add({U+400*st+16*i+m:F(1)for st in states for i,m in product(range(25),range(16))if m>>bit&1},F(1,lcm(label,oldlabel)))
 add({U+800+k:F(1)for k in range(400)},F(1,3375))
 lp.unit_rows=[]
 for k in range(lp.nvars):lp.unit_rows.append(len(lp.rows));add({k:F(1)},F(1))
 lp.columns=[[]for _ in range(lp.nvars)];lp.eqcolumns=[[]for _ in range(lp.nvars)]
 for i,row in enumerate(lp.rows):
  for k,a in row.items():lp.columns[k].append((i,a))
 for i,row in enumerate(lp.equalities):
  for k,a in row.items():lp.eqcolumns[k].append((i,a))
 lp.checker=exact.IntegerDualChecker(lp)
 require(len(lp.rows)==6354 and len(lp.equalities)==18, "The complete minimal3306-variable retained-pair model")
 return lp


def objective(core,j,head,co,lay,proj):
 obj,const=core.objective(j,head,co,lay,proj);obj=list(obj)+[F(0)]*(3306-876);BB=head.bridge.head_load(lay);r,s,cc,rr,ss=proj
 extra=[int(j.ROOT[a]==r)+int(b==s)+int(a==cc)+int(j.ROOT[a]==rr and b==ss)for a,b in product(range(5),repeat=2)]
 for i,b in enumerate(BB):
  for m,st in product(range(16),range(3)):
   n=2 if st==2 else 1;v=b+m.bit_count();obj[U+400*st+16*i+m]=sum(a*(head.bridge.seven_increment(t,v+n,extra[i])-head.bridge.seven_increment(t,v,extra[i]))for t,a in co.items()if t>=2);obj[V+400*st+16*i+m]=sum(a*(max(v+n-t,0)-max(v-t,0))for t,a in co.items()if t>=2)
 const-=sum(a*(CAP135+CAP125)for t,a in co.items()if t>=2)
 require(min(obj)>=0 and const==sum(a*((j.REMAINDERS[0]if t==1 else (j.REMAINDERS[4]-CAP135-CAP125))+j.Z4)for t,a in co.items()),'Whole unchanged base plus exact two-indicator increments and assigned tails')
 return obj,const

def specification(lp, base_spec, j):
    return encode({'variables':3306,'base244_model':base_spec,
        'marked_states':['135-only','125-only','both'],'implicit_complement':'neither',
        'marked_raw_variables':1200,'marked_survivor_variables':1200,
        'projection135_variables':25,'projection125_variables':5,
        'survivor_caps':{'135':CAP135,'125':CAP125},
        'raw_intersection_caps':{str(label):{str(old):F(1,lcm(label,old)) for old in (25,27,75,81)} for label in (135,125)},
        'joint_raw_cap':F(1,3375),'complete_retained_tail':j.REMAINDERS[4]-CAP135-CAP125,
        'unit_repair_rows':3306,'inequalities':len(lp.rows),'equalities':len(lp.equalities),
        'rows_sha256':sha256(json.dumps(encode([lp.rows,lp.rhs,lp.equalities,lp.erhs]),
                                        sort_keys=True,separators=(',',':')).encode()).hexdigest()})


class RetainedJPairHead:
    def __init__(self,base,j,core,prior,bank=None,proposer=None):
        self.j,self.core=j,core
        self.previous=core.JointSelectedJHead(base,j,bank=prior['rational_duals'])
        self.head=self.previous.head
        require(self.previous.specification==prior['model'],'The unchanged244 actual-source model')
        self.lp=make_lp(base,j,self.previous.lp)
        self.specification=specification(self.lp,self.previous.specification,j)
        self.bank={} if bank is None else bank
        self.proposer=proposer
        self.used,self.verified,self.prior_used=set(),{},set()

    def prior_upper(self,coefficients,layout,projection):
        obj,constant=self.core.objective(self.j,self.head,coefficients,layout,projection)
        key=sha256(json.dumps([self.previous.specification['rows_sha256'],encode(obj)],
                             separators=(',',':')).encode()).hexdigest()
        if key not in self.previous.bank:
            return None,None
        value,checked_key,checked_constant=self.previous.dual_upper(coefficients,layout,projection)
        require(key==checked_key and constant==checked_constant,'Only identical244 whole-objective duals are reused')
        self.prior_used.add(key)
        return value,key

    def dual_upper(self,coefficients,layout,projection):
        obj,constant=objective(self.core,self.j,self.head,coefficients,layout,projection)
        require(len(obj)==3306 and min(obj)>=0 and all(v==0 for v in obj[400:425]+obj[825:876]+obj[3276:]),
                'All marked-state objective terms and every zero auxiliary column are retained')
        key=sha256(json.dumps([self.specification['rows_sha256'],encode(obj)],separators=(',',':')).encode()).hexdigest()
        if key not in self.verified:
            if key not in self.bank:
                require(self.proposer is not None,'Missing exact retained-pair dual '+key)
                self.bank[key]=self.proposer(self.lp,obj)
            self.verified[key]=self.lp.checker.check(obj,self.bank[key])
        self.used.add(key)
        return self.verified[key]+constant,key,constant

    def scan(self, row):
        j, head = self.j, self.head
        coefficients = {int(t):F(v) for t,v in row['scan']['coefficients'].items()}
        prepared = head.prepare(coefficients)
        scale = prepared['factor']/j.TOTAL
        independent_checks = head.check_compiler(prepared)
        original = row['scan']['maximizing_witness']
        seed_layout = tuple(original['layout'])
        seed_projection = tuple(original[k] for k in
            ('seven21_root','seven35_slot','seven63_cell','seven105_root','seven105_slot'))
        digest = sha256()
        counts = {'two_projection_branches':0, 'two_bounded':0,
                  'four_projection_branches':0, 'four_bounded':0,
                  'joint_dual_branches':0, 'prior244_bounded':0, 'strict_affine_crossings':0}
        used_before = set(self.used)
        start = perf_counter()

        def old_bounds(layout, projection):
            B = head.bridge.head_load(layout)
            correction = head.correction(prepared, B)
            r,s,c,rr,ss = projection
            extra = tuple(int(j.ROOT[a]==r)+int(b==s) for a,b in product(range(5),repeat=2))
            first = tuple(v+int(a==c)+int(j.ROOT[a]==rr and b==ss)
                          for v,(a,b) in zip(extra,product(range(5),repeat=2)))
            two = head.objective(prepared,B,extra,correction,False)
            four = head.objective(prepared,B,first,correction,True)
            value,x,crossed = j.max_min_affines(two,four)
            return scale*value,x,crossed,two,four

        seed_old,x,crossed,two,four = old_bounds(seed_layout,seed_projection)
        seed_joint,key,constant = self.dual_upper(coefficients,seed_layout,seed_projection)
        best = min(seed_old,seed_joint)
        witness = {'layout':seed_layout,'projection21_35_63_105':seed_projection,
                   'old_complete_upper':seed_old,'old_maximizing_late_coordinate':x,
                   'joint_complete_upper':seed_joint,'adopted_complete_upper':best,'dual_key':key,
                   'complete_tail_constant':constant}
        seed_record = dict(witness)
        require(best>=0,'Nonnegative complete seed bound')
        max_pruned_two = max_pruned_four = F(-1)
        for il,layout in enumerate(j.layouts()):
            B = head.bridge.head_load(layout)
            correction = head.correction(prepared,B)
            for r,s,extra in head.extras:
                two = head.objective(prepared,B,extra,correction,False)
                counts['two_projection_branches'] += 1
                two_upper = scale*max(two)
                if two_upper<=best:
                    counts['two_bounded'] += 1
                    max_pruned_two = max(max_pruned_two,two_upper)
                    digest.update(repr(('two',layout,r,s,two)).encode())
                    continue
                for c,rr,ss,added in head.added:
                    first = tuple(a+b for a,b in zip(extra,added))
                    four = head.objective(prepared,B,first,correction,True)
                    value,x,crossed = j.max_min_affines(two,four)
                    old_upper = scale*value
                    counts['four_projection_branches'] += 1
                    counts['strict_affine_crossings'] += int(crossed)
                    if old_upper<=best:
                        counts['four_bounded'] += 1
                        max_pruned_four = max(max_pruned_four,old_upper)
                        digest.update(repr(('four',layout,r,s,c,rr,ss,two,four)).encode())
                        continue
                    projection = (r,s,c,rr,ss)
                    previous,prior_key = self.prior_upper(coefficients,layout,projection)
                    if previous is not None and previous<=best:
                        counts['prior244_bounded'] += 1
                        digest.update(repr(('prior244',layout,projection,prior_key,str(previous))).encode())
                        continue
                    joint,key,constant = self.dual_upper(coefficients,layout,projection)
                    adopted = min(old_upper,joint)
                    counts['joint_dual_branches'] += 1
                    digest.update(repr(('joint',layout,projection,two,four,key,str(joint))).encode())
                    if adopted>best:
                        best = adopted
                        witness = {'layout':layout,'projection21_35_63_105':projection,
                                   'old_complete_upper':old_upper,'old_maximizing_late_coordinate':x,
                                   'joint_complete_upper':joint,'adopted_complete_upper':adopted,
                                   'dual_key':key,'complete_tail_constant':constant}
            if il%2500==0:
                print('J retained pair '+str(row['index'])+': layouts='+str(il)+', LP branches='
                      +str(counts['joint_dual_branches'])+', seconds='+str(round(perf_counter()-start,2)),flush=True)
        require(counts['two_projection_branches']==125000
                and counts['four_projection_branches']==50*(125000-counts['two_bounded'])
                and counts['joint_dual_branches']+counts['four_bounded']+counts['prior244_bounded']==counts['four_projection_branches']
                and 50*counts['two_bounded']+counts['four_projection_branches']==6250000
                and max_pruned_two<=best and max_pruned_four<=best,
                'All6250000 containing choices are included by full evaluation or valid uniform pruning')
        old,x,crossed,two,four = old_bounds(witness['layout'],witness['projection21_35_63_105'])
        raw,key,constant = self.dual_upper(coefficients,witness['layout'],witness['projection21_35_63_105'])
        require(old==witness['old_complete_upper'] and raw==witness['joint_complete_upper']
                and key==witness['dual_key'] and min(old,raw)==best,
                'The maximizing certificate branch reconstructs exactly; no primal attainment is claimed')
        r,s,c,rr,ss = witness['projection21_35_63_105']
        for theta in (j.LO,j.HI,j.LO+(j.HI-j.LO)*x):
            old_pair = [head.rational_objective(coefficients,witness['layout'],p,theta)
                        for p in ((r,s,None,None,None),(r,s,c,rr,ss))]
            t = (theta-j.LO)/(j.HI-j.LO)
            require(old_pair==[scale*(v[0]+(v[1]-v[0])*t) for v in (two,four)],
                    'Independent unscaled maximizing-branch bounds at both endpoints and exact common crossing')
            independent_checks += 2
        return {'coefficients':coefficients,'complete_hinge_upper':best,
                'counts':counts,'covered_containing_choices':6250000,
                'seed':seed_record,'maximizing_certificate_branch':witness,
                'complete_tail_constant':constant,'independent_affine_checks':independent_checks,
                'maximum_two_pruned':max_pruned_two,'maximum_four_pruned':max_pruned_four,
                'new_distinct_duals':len(self.used-used_before),
                'all_branch_decisions_sha256':digest.hexdigest()}


def calculate(base,bank=None,proposer=None):
    require(PINS,'Final exact source pins')
    io=module('j_pair_io',base/'certificate_io.py')
    core=module('j_pair_core244',base/'frontier/j-geometry/j_face_joint_selected_heads.py')
    read=lambda name:json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', name+'.json')),object_pairs_hook=core.unique)
    prior,original=read('j_face_joint_selected_heads'),read('j_face_coupled_seven_heads')
    pins=dict(PINS)
    for source in(prior,original):
        for path,pin in source['source_sha256'].items():
            require(path not in pins or pins[path]==pin,'Consistent saturated J source closure '+path)
            pins[path]=pin
    for path,pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest()==pin,'Pinned mathematical input '+path)
    require(prior['geometry']==original['geometry'] and F(prior['source_mass'])==F(1,4)
            and F(prior['survivor_mass'])==F(3,20) and F(prior['complete_mean_upper'])==F(16,25),
            'The same two actual saturated J faces and complete original measures')
    j=module('j_pair_source',base/'frontier/j-geometry/j_face_coupled_seven_heads.py')
    require(CAP135==F(1,135) and CAP125==F(13,30)*F(1,125)
            and j.REMAINDERS[4]-CAP135-CAP125>0,'J-specific complete mixed135 and pure-five125 tail summands')
    problem=RetainedJPairHead(base,j,core,prior,bank,proposer)
    require([str(r['index']) for r in original['results']]==['AP13','0','16']
            and [str(r['index']) for r in prior['results']]==['AP13','0','16'],
            'The three independently labelled original targets')
    rows=[]
    for src,prev in zip(original['results'],prior['results']):
        require(src['scan']['coefficients']==prev['scan']['coefficients']
                and src['at_one']==prev['at_one'],'Same original all-load function')
        scan=problem.scan(src)
        at_one=F(src['at_one']);whole=at_one*F(3,20)+scan['complete_hinge_upper']
        old_upper=F(prev['adopted_upper']);mean=at_one*F(3,20)+sum(scan['coefficients'].values())*F(49,100)
        adopted=min(whole,old_upper,mean)
        require(0<adopted<=old_upper,'Every target retains its preceding complete source theorem')
        rows.append({'index':src['index'],'at_one':at_one,'scan':scan,'complete_head_upper':whole,
                     'previous_adopted_upper':old_upper,'complete_mean_only_upper':mean,
                     'adopted_upper':adopted,'improvement_over_previous':old_upper-adopted})
        print('Complete J retained pair '+str(src['index'])+' <= '+str(float(adopted))
              +'; distinct pair duals='+str(scan['new_distinct_duals']),flush=True)
        if proposer is not None:
            print('Complete maximizing certificate branch '+str(src['index'])+': '
                  +json.dumps(encode(scan['maximizing_certificate_branch']),sort_keys=True),flush=True)
    require(problem.used==set(problem.bank) and any(r['improvement_over_previous']>0 for r in rows),
            'All exact pair duals used and at least one complete original target strictly improved')
    codec=module('j_pair_dual_codec',base/'frontier/retained-transport/retained135_heavy_comparison.py')
    retained={key:problem.bank[key] for key in sorted(problem.used)}
    encoded_bank=codec.encode_dual_bank(retained,inequality_count=6354,equality_count=18)
    require(codec.decode_dual_bank(encoded_bank,inequality_count=6354,equality_count=18)==retained,
            'Lossless exact rational recovery of every complete3306-column dual')
    return encode({'schema':'erdos7-j-face-retained135125-heads-v1','source_sha256':pins,
        'geometry':prior['geometry'],'source_mass':F(1,4),'survivor_mass':F(3,20),'complete_mean_upper':F(16,25),
        'model':problem.specification,'results':rows,
        'encoded_rational_duals':encoded_bank,
        'distinct_dual_count':len(problem.used),'rational_column_checks':3306*len(problem.used),
        'previous244_duals_used':sorted(problem.prior_used),
        'total_containing_choices':sum(r['scan']['covered_containing_choices'] for r in rows),
        'total_independent_affine_checks':sum(r['scan']['independent_affine_checks'] for r in rows),
        'scope':'Three complete original AP13/heavy0/heavy16 comparisons on both saturated actual J faces. The3306-variable containing model retains244 raw/survivor/deletion constraints and one late parameter, independent135/125 profiles, all four joint membership states, every original residue and the complete exponent tails. The125 survivor cap is13/3750 from the J pure-five theorem, not the K cap. Each target covers6250000 containing choices and all3306 rational dual columns. No optional additional deletion rows, Kforced27 rule, actual optimizer attainment, off-face extension, complete52-cost/global comparison, Lean verification or unrestricted Erdos7 result is asserted.'})


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    io=module('j_pair_read',args.base/'certificate_io.py')
    core=module('j_pair_json',args.base/'frontier/j-geometry/j_face_joint_selected_heads.py')
    stored=json.loads(io.read_artifact_bytes(args.base/CERTIFICATE),object_pairs_hook=core.unique)
    codec=module('j_pair_read_dual_codec',args.base/'frontier/retained-transport/retained135_heavy_comparison.py')
    bank=codec.decode_dual_bank(stored['encoded_rational_duals'],inequality_count=6354,equality_count=18)
    result=calculate(args.base,bank=bank)
    require(result==stored,'Every complete retained J135/125 certificate field recomputes exactly')
    print('PASS:3 complete retained J heads,18750000 containing choices,'+str(result['distinct_dual_count'])
          +' exact3306-column duals and complete exponent tails.',flush=True)


if __name__=='__main__':
    try:main()
    except(ValueError,ArithmeticError,OSError,KeyError,TypeError,json.JSONDecodeError)as error:
        print('FAIL: '+str(error),file=sys.stderr)
        raise SystemExit(1)
