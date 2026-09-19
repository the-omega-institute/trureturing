#!/usr/bin/env python3
"""One actual J source controls original quadratic costs through shifted factorials."""
import argparse
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from itertools import product
from pathlib import Path
from time import perf_counter
import importlib.util
import json
import sys
sys.dont_write_bytecode=True
CERTIFICATE='certificates/source_norms/j-geometry/j_face_shifted_factorial_quadratic_heads.json'
PINS={'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2', 'frontier/j-geometry/j_face_second_depth_retained_heads.py': '31fbe7158a9dba427a0cd69a5d41b2d7abb2f57dbc81c7e33a4f0ee1adf44c38', 'certificates/source_norms/j-geometry/j_face_second_depth_retained_heads.json': 'f5fb76fc464c2b8a6e641d7c85651c87c1007039a0e3c9ab655e2532a7bb2c4d', 'profile-notes/193-256/256-a-second-seven-depth-sharpens-the-complete-retained-j-heads.md': '8b51d3dbd5328bfe55cad1909a7321deb9fe7f9f0be08230240ae4fede5d91be', 'frontier/j-geometry/j_face_raw_prime_path_pairs.py': '661566e5fe17a22f8a5287c738ef0c57d03bcf7261c9aa39d8cedbcd03052748', 'certificates/source_norms/j-geometry/j_face_raw_prime_path_pairs.json': '83ee30fbf79feb0170bc58e4a73ddf7b24e7229828b7037ffe9db253f3c01597', 'profile-notes/257-320/265-complete-raw-prime-paths-improve-the-positive-seven-pair-block.md': '4bc30949a4134cae5f390754167d9360e9a0264d091abe5b6d41a09d51451077', 'frontier/j-geometry/j_face_triple_raw_path_complete_moment_cost_comparison.py': '3bc6fc7348fc83064c6acc261c516a45284c9bf7b3d2ab8f0f392ab8338557c2', 'certificates/source_norms/j-geometry/j_face_triple_raw_path_complete_moment_cost_comparison.json': '7f2d9e2ee630bd467cc6e52e94c0da82649db8d62aef869035072d0537577be6', 'frontier/moments-survival/whole_quadratic_same_head.py': 'ba2de9c8850b1936ebac15ab9e4cc546a052de6139289343e0de5d2dec560938'}
INDICES=(41,47,48)


def require(ok,message):
    if not ok:raise ValueError(message)


def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    require(spec is not None and spec.loader is not None,'Loadable exact mathematical input')
    value=importlib.util.module_from_spec(spec);spec.loader.exec_module(value);return value


def encode(value):
    if isinstance(value,F):return str(value)
    if isinstance(value,dict):return {str(k):encode(v) for k,v in value.items()}
    if isinstance(value,(tuple,list)):return [encode(v) for v in value]
    return value


def max_min_affines(lines):
    candidates={F(0),F(1)}
    for i,a in enumerate(lines):
        for b in lines[:i]:
            denominator=a[0]-b[0]-a[1]+b[1]
            if denominator:
                x=F(a[0]-b[0],denominator)
                if 0<x<1:candidates.add(x)
    values={x:min(a+(b-a)*x for a,b in lines) for x in candidates}
    at=max(sorted(candidates),key=lambda x:values[x])
    return values[at],at,len(candidates)-2


def make_problem(base,j,core,pair,depth,second,moment,prior244,prior251,
                 complete_pair_tail,bank=None,proposer=None):
    """Reusable original-cost scanner: same3306 source, exactPhi4 head and cross."""
    class QuadraticDepth(second.SecondDepthJHead):
     def __init__(self,*args,**kwargs):
      super().__init__(*args,**kwargs);self.mom=moment.JMomentHead(self.j);self.pair_tail=complete_pair_tail;self.k=4;self.fc=F(0);self.atone=F(0)
     @lru_cache(None)
     def parts(self,layout):
      bb=self.head.bridge.head_load(layout);phi=tuple(F(max(b-self.k,0)*max(b-self.k+1,0),2)for b in bb);h=tuple(F(max(b-self.k+1,0))for b in bb)
      oldcross=self.mom.old_tail(tuple(w*v for w,v in zip(self.mom.w,h)));rows=[]
      for theta in(self.j.LO,self.j.HI):
       head=self.mom.lp(tuple(w*v for w,v in zip(self.mom.w,phi)),theta)-sum(self.j.deletion_correction(phi))
       cross=oldcross+self.mom.raw_row(h,theta)/5
       require(head>=0 and cross>=0,'Nonnegative same-layout shifted-factorial head and complete crosses')
       rows.append((head+cross,cross))
      return tuple(rows)
     def affine(self,prepared,BB,extra,correction,expanded,layout):
      raw=self.head.objective(prepared,BB,extra,correction,expanded)
      return tuple(v+(self.fc*(p[0]+self.pair_tail)+self.atone*F(3,20))/self.scale for v,p in zip(raw,self.parts(layout)))
     def objective(self,co,layout,projection):
      obj,const=super().objective(co,layout,projection);BB=self.head.bridge.head_load(layout)
      for cell,b in enumerate(BB):
       phi=F(max(b-self.k,0)*max(b-self.k+1,0),2)
       for mask in range(16):obj[425+16*cell+mask]+=self.fc*phi
      c0,c1=(p[1]for p in self.parts(layout));obj[875]+=self.fc*(c1-c0)
      const+=self.fc*(c0+self.pair_tail)+self.atone*F(3,20)
      require(all(v>=0 for k,v in enumerate(obj)if k!=875),'Only common-theta secant may have negative price')
      return obj,const
     def prior_upper(self,co,layout,projection):return None,None
     def rational_six(self,co,layout,projection,theta):
      val=super().rational_six(co,layout,projection,theta);x=(theta-self.j.LO)/(self.j.HI-self.j.LO);p0,p1=self.parts(layout)
      return val+self.fc*(p0[0]+(p1[0]-p0[0])*x+self.pair_tail)+self.atone*F(3,20)
     def scan(self,row):
         j,head=self.j,self.head;co={int(t):F(a) for t,a in row['scan']['coefficients'].items()}
         old=head.prepare(co);six=self.prepare_six(old);scale=old['factor']/j.TOTAL;self.scale=scale
         independent=head.check_compiler(old);start=perf_counter();digest=sha256();used_before=set(self.used)
         counts={k:0 for k in ('two_projection_branches','two_bounded','four_projection_branches','four_bounded','prior251_bounded','six_projection_branches','six_affine_bounded','joint_dual_branches','strict_pair_crossings')}
         def affines(layout,projection):
             B=head.bridge.head_load(layout);correction=head.correction(old,B)
             r,s,c,rr,ss=projection[:5]
             extra=tuple(int(j.ROOT[a]==r)+int(b==s) for a,b in product(range(5),repeat=2))
             first=tuple(v+int(a==c)+int(j.ROOT[a]==rr and b==ss) for v,(a,b) in zip(extra,product(range(5),repeat=2)))
             two=self.affine(old,B,extra,correction,False,layout);four=self.affine(old,B,first,correction,True,layout)
             if len(projection)==5:return two,four
             r147,s245=projection[5:]
             second=tuple(int(j.ROOT[a]==r147)+int(b==s245) for a,b in product(range(5),repeat=2))
             return two,four,self.affine(six,B,tuple(zip(first,second)),correction,True,layout)
         source=row['scan']['maximizing_certificate_branch'];seed_layout=tuple(source['layout']);seed_projection=tuple(source['projection21_35_63_105'])
         best=F(-1);witness=None
         for r,s in product(range(2),range(5)):
             projection=seed_projection+(r,s);lines=affines(seed_layout,projection)
             value,x,_=max_min_affines(lines);joint,key,const=self.dual_upper(co,seed_layout,projection)
             previous,prior_key=self.prior_upper(co,seed_layout,seed_projection)
             adopted=min(scale*value,joint,*(() if previous is None else (previous,)))
             if adopted>best:
                 best=adopted;witness={'layout':seed_layout,'projection21_35_63_105_147_245':projection,'affine_complete_upper':scale*value,
                     'affine_maximizing_late_coordinate':x,'joint_complete_upper':joint,'previous251_complete_upper':previous,
                     'adopted_complete_upper':adopted,'dual_key':key,'previous251_dual_key':prior_key,'complete_tail_constant':const}
         seed_record=dict(witness)
         for layout in ((0,1,2,0,2,1,2),(1,3,2,1,2,3,2)):
             for projection in ((0,1,2,1,3,0,4),(1,4,4,1,2,1,1)):
                 lines=affines(layout,projection)
                 for theta,x in ((j.LO,F(0)),(j.HI,F(1))):
                     require(self.rational_six(co,layout,projection,theta)==scale*(lines[2][0]+(lines[2][1]-lines[2][0])*x),
                             'Independent unscaled full six-projection affine compiler')
                     independent+=1
         maxima={k:F(-1) for k in ('two','four','prior251','six')}
         for il,layout in enumerate(j.layouts()):
             B=head.bridge.head_load(layout);correction=head.correction(old,B)
             for r,s,extra in head.extras:
                 two=self.affine(old,B,extra,correction,False,layout);counts['two_projection_branches']+=1
                 upper=scale*max(two)
                 if upper<=best:
                     counts['two_bounded']+=1;maxima['two']=max(maxima['two'],upper)
                     digest.update(repr(('two',layout,r,s,two)).encode());continue
                 for c,rr,ss,added in head.added:
                     first=tuple(a+b for a,b in zip(extra,added));four=self.affine(old,B,first,correction,True,layout)
                     value,x,_=j.max_min_affines(two,four);upper=scale*value;counts['four_projection_branches']+=1
                     if upper<=best:
                         counts['four_bounded']+=1;maxima['four']=max(maxima['four'],upper)
                         digest.update(repr(('four',layout,r,s,c,rr,ss,two,four)).encode());continue
                     projection=(r,s,c,rr,ss);previous,prior_key=self.prior_upper(co,layout,projection)
                     if previous is not None and previous<=best:
                         counts['prior251_bounded']+=1;maxima['prior251']=max(maxima['prior251'],previous)
                         digest.update(repr(('prior251',layout,projection,prior_key,str(previous))).encode());continue
                     for r147,s245,second in head.extras:
                         extended=projection+(r147,s245);line=self.affine(six,B,tuple(zip(first,second)),correction,True,layout)
                         value,x,crossings=max_min_affines((two,four,line));upper=scale*value
                         counts['six_projection_branches']+=1;counts['strict_pair_crossings']+=crossings
                         if upper<=best:
                             counts['six_affine_bounded']+=1;maxima['six']=max(maxima['six'],upper)
                             digest.update(repr(('six-affine',layout,extended,two,four,line)).encode());continue
                         joint,key,const=self.dual_upper(co,layout,extended)
                         adopted=min(upper,joint,*(() if previous is None else (previous,)))
                         counts['joint_dual_branches']+=1
                         digest.update(repr(('joint',layout,extended,two,four,line,key,str(joint),prior_key)).encode())
                         if adopted>best:
                             best=adopted;witness={'layout':layout,'projection21_35_63_105_147_245':extended,'affine_complete_upper':upper,
                                 'affine_maximizing_late_coordinate':x,'joint_complete_upper':joint,'previous251_complete_upper':previous,
                                 'adopted_complete_upper':adopted,'dual_key':key,'previous251_dual_key':prior_key,'complete_tail_constant':const}
             if il%2500==0:print('J shifted factorial '+str(row['index'])+': layouts='+str(il)+', LP branches='+str(counts['joint_dual_branches'])+', seconds='+str(round(perf_counter()-start,2)),flush=True)
         require(counts['two_projection_branches']==125000
                 and counts['four_projection_branches']==50*(125000-counts['two_bounded'])
                 and counts['six_projection_branches']==10*(counts['four_projection_branches']-counts['four_bounded']-counts['prior251_bounded'])
                 and counts['joint_dual_branches']+counts['six_affine_bounded']==counts['six_projection_branches']
                 and 500*counts['two_bounded']+10*(counts['four_bounded']+counts['prior251_bounded'])+counts['six_projection_branches']==62500000
                 and max(maxima.values())<=best,'Every62500000 original containing choice is explicitly covered')
         layout=witness['layout'];projection=witness['projection21_35_63_105_147_245'];lines=affines(layout,projection)
         value,x,_=max_min_affines(lines);joint,key,const=self.dual_upper(co,layout,projection)
         previous,prior_key=self.prior_upper(co,layout,projection[:5])
         require(scale*value==witness['affine_complete_upper'] and x==witness['affine_maximizing_late_coordinate']
                 and joint==witness['joint_complete_upper'] and key==witness['dual_key'] and previous==witness['previous251_complete_upper']
                 and min(scale*value,joint,*(() if previous is None else (previous,)))==best,'Exact complete maximizing certificate branch; no actual attainment claim')
         for x in (F(0),F(1),witness['affine_maximizing_late_coordinate']):
             theta=j.LO+(j.HI-j.LO)*x
             require(self.rational_six(co,layout,projection,theta)==scale*(lines[2][0]+(lines[2][1]-lines[2][0])*x),
                     'Independent maximizing-branch six-projection endpoints and common crossing')
             independent+=1
         return {'coefficients':co,'complete_cost_upper':best,'counts':counts,'covered_containing_choices':62500000,
                 'seed':seed_record,'maximizing_certificate_branch':witness,'complete_tail_constant':const,
                 'independent_affine_checks':independent,'maximum_pruned':maxima,'new_distinct_duals':len(self.used-used_before),
                 'all_branch_decisions_sha256':digest.hexdigest()}

    return QuadraticDepth(base,j,core,pair,depth,prior244,prior251,bank=bank,proposer=proposer)


def shifted_expansion(source,quad,tag,threshold=4):
    require(threshold==4,'The retained threshold isPhi4')
    original=quad.quadratic_expansion(source,tag)
    old={int(t):F(v) for t,v in original['hinge_coefficients'].items()}
    fc,atone=F(original['factorial_tail_coefficient']),F(original['at_one'])
    last=max(max(old),threshold)
    coefficients={t:old.get(t,F(0))+fc*(int(t>=5)-int(t>=threshold)) for t in range(1,last+1)}
    coefficients={t:v for t,v in coefficients.items() if v}
    require(fc>0 and atone>=0 and coefficients and all(1<=t<=8 and v>0 for t,v in coefficients.items()),
            'Only unchanged original costs with a nonnegative shifted hinge expansion enter')
    phi=lambda n:F(max(n-threshold,0)*max(n-threshold+1,0),2)
    expand=lambda n:atone+sum(a*max(n-t,0) for t,a in coefficients.items())+fc*phi(n)
    entrance=max(last,threshold,original['polynomial_tail']['entrance'])
    values={n:source.zero5_cost(tag,n) for n in range(1,entrance+2)}
    require(all(expand(n)==v for n,v in values.items()),'Every finite transition of the unchanged original cost')
    leading=F(original['polynomial_tail']['leading']);constant=F(original['polynomial_tail']['constant'])
    require(fc/2==leading and sum(coefficients.values())+fc*F(1-2*threshold,2)==0
            and atone-sum(t*a for t,a in coefficients.items())+fc*F(threshold*(threshold-1),2)==constant,
            'All three coefficients of the entire infinite polynomial continuation agree')
    require(old.get(4,F(0))-fc==coefficients.get(4,F(0))
            and all(old.get(t,F(0))==coefficients.get(t,F(0)) for t in range(1,last+1) if t!=4),
            'The exact identityPhi4=Phi5+H4 changes only the threshold4 hinge coefficient')
    return {'factorial_threshold':threshold,'at_one':atone,'hinge_coefficients':coefficients,
            'factorial_coefficient':fc,'original_phi5_expansion':original,
            'polynomial_tail':{'leading':leading,'linear':F(0),'constant':constant,'entrance':entrance},
            'finite_transition_values':values}


def check_factorial_split():
    """Finite head cases plus exact all-tail coefficient/monotonicity argument."""
    records=[]
    for b in range(1,7):
        d=b-4;phi=F(max(d,0)*max(d+1,0),2);h=max(b-3,0)
        if b>=3:
            require(phi==F(d*(d+1),2) and h==d+1,'For every nonnegative tail the two quadratics are identical')
            records.append({'head':b,'case':'exact-quadratic','constant':phi,'tail_linear':F(2*d+1,2),'tail_quadratic':F(1,2)})
        else:
            require(d+1<=0 and phi==h==0,'The positive-part argument is at most the nonnegative tail; binomial is increasing on integers')
            records.append({'head':b,'case':'monotone-binomial','head_phi':phi,'head_cross':h,'argument_shift':d+1})
    return records


def calculate(base,bank,seed_rows):
    require(PINS,'Exact source pins')
    io=module('shifted_io',base/'certificate_io.py');core=module('shifted_core244',base/'frontier/j-geometry/j_face_joint_selected_heads.py')
    read=lambda name:json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', name+'.json')),object_pairs_hook=core.unique)
    prior244,prior251,source256,source265,comparison=(read(name) for name in ('j_face_joint_selected_heads','j_face_retained135125_heads',
        'j_face_second_depth_retained_heads','j_face_raw_prime_path_pairs','j_face_triple_raw_path_complete_moment_cost_comparison'))
    pins=dict(PINS)
    for source in(prior244,prior251,source256,source265,comparison):
        for path,pin in source['source_sha256'].items():
            require(path not in pins or pins[path]==pin,'Consistent mathematical source '+path);pins[path]=pin
    for path,pin in pins.items():require(sha256(io.read_artifact_bytes(base/path)).hexdigest()==pin,'Pinned actual mathematical input '+path)
    require(all(source['geometry']==source256['geometry'] and F(source['survivor_mass'])==F(3,20) for source in(prior244,prior251,source265,comparison)),
            'Every source inequality concerns the same two whole actual saturated J faces')
    j=module('shifted_source',base/'frontier/j-geometry/j_face_coupled_seven_heads.py');pair=module('shifted_pair',base/'frontier/j-geometry/j_face_retained135125_heads.py')
    depth=module('shifted_depth_formula',base/'frontier/comparison-bounds/second_depth_seven_comparison.py');second=module('shifted_scanner',base/'frontier/j-geometry/j_face_second_depth_retained_heads.py')
    moment=module('shifted_moments',base/'frontier/j-geometry/j_face_shared_square_factorial.py');quad=module('shifted_expansion',base/'frontier/moments-survival/whole_quadratic_same_head.py')
    inventory=module('shifted_inventory',base/'frontier/source-budgets/source_barrier_saturation.py');engine=inventory.Experiment(base)
    require(all(path in pins and pins[path]==pin for path,pin in engine.pins.items()),'Original52-cost identity inventory is pinned')
    tags=[row['tag'] for row in engine.specs+engine.quadratic_specs]+[('s',F(81,n*n)) for n in range(1,7)]
    require(len(tags)==52 and [int(row['index']) for row in seed_rows]==list(INDICES),'Exactly three specified original cost indices and arbitrary full-search seeds')
    pair_tail=F(source265['complete_tail_distinct_pairs'])
    require(pair_tail==F(4879,7200) and pair_tail==F(source265['complete_ordered_tail_square'])/2
            -(F(53,600)+F(3,20))/2,'The complete omitted distinct-pair tail retains all off-head labels and no duplicate diagonal')
    problem=make_problem(base,j,core,pair,depth,second,moment,prior244,prior251,pair_tail,bank=bank)
    require(problem.specification==source256['model'],'Entire unchanged3306-variable actual-source model')
    split=check_factorial_split();components=[];component_digest=sha256()
    for layout in j.layouts():
        parts=problem.parts(layout);row={'layout':layout,'shifted_factorial_head_and_cross_endpoints':parts}
        component_digest.update(json.dumps(encode(row),separators=(',',':')).encode());components.append(parts)
    require(len(components)==12500,'All original shifted factorial head/cross components before any pruning')
    previous={int(row['name'][5:]):F(row['upper']) for row in comparison['results'] if row['name'].startswith('cost-')}
    rows=[]
    for index,seed in zip(INDICES,seed_rows):
        expansion=shifted_expansion(engine.source,quad,tags[index]);problem.fc=expansion['factorial_coefficient'];problem.atone=expansion['at_one']
        co=expansion['hinge_coefficients'];row={'index':index,'scan':{'coefficients':encode(co),'maximizing_certificate_branch':seed['branch']}}
        result=problem.scan(row);complete=result['complete_cost_upper'];adopted=min(complete,previous[index])
        require(complete>0 and adopted<previous[index],'Every specified original cost improves its preceding complete comparison bound')
        rows.append({'index':index,'tag':tags[index],'expansion':expansion,'scan':result,'complete_cost_upper':complete,
                     'previous_adopted_upper':previous[index],'adopted_upper':adopted,'improvement_over_previous':previous[index]-adopted})
        print('Complete shifted factorial J cost'+str(index)+' <= '+str(float(adopted)),flush=True)
    require(problem.used<=set(bank) and not problem.prior_used,'Every required exact full-cost dual supplied; no hinge-only251 bound reused')
    kept={key:bank[key] for key in sorted(problem.used)};encoded=problem.codec.encode_dual_bank(kept,inequality_count=6354,equality_count=18)
    require(problem.codec.decode_dual_bank(encoded,inequality_count=6354,equality_count=18)==kept,'Lossless complete exact full-cost dual bank')
    return encode({'schema':'erdos7-j-face-shifted-factorial-quadratic-heads-v1','source_sha256':pins,'geometry':source256['geometry'],
        'source_mass':F(1,4),'survivor_mass':F(3,20),'model':problem.specification,'original_cost_indices':INDICES,
        'factorial_threshold':4,'complete_pair_tail':pair_tail,'complete_positive7_tail':second.Z6,
        'factorial_split_all_head_cases':split,'original_factorial_head_count':len(components),'factorial_endpoint_record_count':2*len(components),
        'all_factorial_head_cross_components_sha256':component_digest.hexdigest(),'seed_rows':seed_rows,'results':rows,
        'encoded_rational_duals':encoded,'distinct_dual_count':len(kept),'rational_column_checks':3306*len(kept),
        'total_containing_choices':sum(row['scan']['covered_containing_choices'] for row in rows),
        'total_independent_affine_checks':sum(row['scan']['independent_affine_checks'] for row in rows),
        'scope':'Three unchanged original costs41/47/48 on both entire actual saturated J faces. ExactPhi4 expansions retain the entire polynomial continuation; the same original six-head feeds the positive hinges, actual survivor factorial head and common-late-coordinate cross secant. Each target retains all62500000 original containing choices, every135/125 membership state, every147/245 projection and complete265 omitted pair tails. Only the normalized common-theta objective may be signed; all dual columns are checked. No hinge-only bound is used for full-cost pruning. No simultaneous source attainment, off-face extension, full52-cost/global comparison, Lean verification or unrestricted Erdos7 resolution.'})


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    parser.add_argument('--write',action='store_true');parser.add_argument('--check',action='store_true');parser.add_argument('--proposal',type=Path);args=parser.parse_args()
    io=module('shifted_reader',args.base/'certificate_io.py');core=module('shifted_json',args.base/'frontier/j-geometry/j_face_joint_selected_heads.py')
    if args.write:
        require(args.proposal is not None,'A complete exact proposed dual bank and explicit seeds')
        proposed=json.loads(io.read_artifact_bytes(args.proposal),object_pairs_hook=core.unique)
        bank=proposed['bank'];seeds=proposed['seed_rows']
    else:
        proposed=json.loads(io.read_artifact_bytes(args.base/CERTIFICATE),object_pairs_hook=core.unique)
        codec=module('shifted_codec',args.base/'frontier/retained-transport/retained135_heavy_comparison.py')
        bank=codec.decode_dual_bank(proposed['encoded_rational_duals'],inequality_count=6354,equality_count=18);seeds=proposed['seed_rows']
    result=calculate(args.base,bank,seeds)
    if args.write:io.write_certificate_text(args.base/CERTIFICATE,json.dumps(result,indent=2)+'\n')
    else:require(result==proposed,'Every complete shifted-factorial original-cost certificate field recomputes exactly')
    print('PASS three original quadratic costs;187500000 containing choices;'+str(result['distinct_dual_count'])+' exact3306-column duals; full polynomial and exponent tails.',flush=True)


if __name__=='__main__':
    try:main()
    except(ValueError,ArithmeticError,OSError,KeyError,TypeError,json.JSONDecodeError)as error:
        print('FAIL: '+str(error),file=sys.stderr);raise SystemExit(1)
