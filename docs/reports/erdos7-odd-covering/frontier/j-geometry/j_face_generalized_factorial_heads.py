#!/usr/bin/env python3
"""Original J costs with generalized factorial thresholds and actual joint crosses."""
import argparse
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from itertools import product
from pathlib import Path
from types import MethodType
import importlib.util
import json
import sys
sys.dont_write_bytecode=True
CERTIFICATE='certificates/source_norms/j-geometry/j_face_generalized_factorial_heads.json'
PINS={'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2', 'frontier/j-geometry/j_face_shifted_factorial_quadratic_heads.py': 'c39300eff6da9c448a40c57c1a94e6000f85a4c3e9f9e3f1917875e49a3000f6', 'certificates/source_norms/j-geometry/j_face_shifted_factorial_quadratic_heads.json': 'cef14f340414a79a040070219f8540cf8d896392d996b12a9973cc443622898d', 'profile-notes/257-320/270-shifted-factorial-heads-strengthen-three-original-j-quadratic-costs.md': 'd7b85e393d321d5f90ebc6eb8eee60fa45dd4368d8c201530fd4d680f686a8ee', 'frontier/j-geometry/j_face_joint_factorial_cross_heads.py': '082e39367404a0de7fb0a90926817523576795d322b6d15433f600b10508cd13', 'certificates/source_norms/j-geometry/j_face_joint_factorial_cross_heads.json': 'adc3822f5b69e246069681c3280fbd773921d35f049af66ddda59f77ef9a9da0', 'profile-notes/257-320/272-joint-raw-and-survivor-crosses-strengthen-three-original-j-costs.md': '0629a27b16725c974556474abd0ebf8ae211341d073aab030a33c874bbc64f15', 'frontier/j-geometry/j_face_joint_factorial_cross_complete_moment_cost_comparison.py': '380274d869d520f3b451fd88f0ed1c6c1344edaa99bd1f3873bfd477b4f26065', 'certificates/source_norms/j-geometry/j_face_joint_factorial_cross_complete_moment_cost_comparison.json': '974fb2d1423b90942cde90d149266a188c5274f601953b6794332380906a0557', 'profile-notes/257-320/273-joint-factorial-crosses-improve-the-complete-j-comparison.md': 'ddb5a0f7147d40431832040eb88243776bb384764ef4df5e56b4cfad778a4434'}
TARGETS=((48,3),(49,2))
OLD_WEIGHTS=(F(1,18),F(1,20),F(1,20),F(1,20),F(1,72))
SELECTED_WEIGHTS=(F(1,27)+F(1,81),F(1,25)+F(1,125),F(1,25),F(0),F(1,135))
REMAINING_WEIGHTS=tuple(a-b for a,b in zip(OLD_WEIGHTS,SELECTED_WEIGHTS))
RAW_MASK_WEIGHTS=(F(1,245),F(1,35),F(1,245),F(1,35),F(1,5))
U1,U2=F(6,35),F(6,245)


def require(ok,message):
    if not ok:raise ValueError(message)


def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    require(spec is not None and spec.loader is not None,'Loadable actual mathematical input')
    value=importlib.util.module_from_spec(spec);spec.loader.exec_module(value);return value


def encode(value):
    if isinstance(value,F):return str(value)
    if isinstance(value,dict):return {str(k):encode(v) for k,v in value.items()}
    if isinstance(value,(tuple,list)):return [encode(v) for v in value]
    return value


def check_partitions():
    old3=F(1,27)/(1-F(1,3));old5=F(1,25)/(1-F(1,5))
    mixed=old3*F(1,5)/(1-F(1,5))
    require(OLD_WEIGHTS==(old3,old5,old5,old5,mixed),'Complete original zero7 geometric series')
    require(REMAINING_WEIGHTS==(F(1,162),F(1,500),F(1,100),F(1,20),F(7,1080))
            and min(REMAINING_WEIGHTS)>0,'Exactly the six assigned old labels removed from their own series')
    selected=((27,0,F(1,27)),(81,0,F(1,81)),(25,1,F(1,25)),(125,1,F(1,125)),(75,2,F(1,25)),(135,4,F(1,135)))
    require(tuple(sum(weight for _,k,weight in selected if k==i)for i in range(5))==SELECTED_WEIGHTS,
            '75 uses its root-family coefficient at5^-2;135 is the mixed(3,1) label')
    total=U1/(1-F(1,7))
    require(total==F(1,5) and U2==U1/7
            and RAW_MASK_WEIGHTS==(total-U1-U2,total-U1,total-U1-U2,total-U1,total),
            'Every complete positive7 cofactor series keeps all remaining depths')
    return {'old_zero7_weights':OLD_WEIGHTS,'selected_zero7_labels':selected,
            'selected_zero7_weights':SELECTED_WEIGHTS,'remaining_zero7_weights':REMAINING_WEIGHTS,
            'positive7_first_depth_weight':U1,'positive7_second_depth_weight':U2,
            'complete_positive7_weight':total,'raw_mask_residual_weights':RAW_MASK_WEIGHTS}


def shifted_identity(source,quad,tag,k):
    require(isinstance(k,int) and k>=1,'Positive integer factorial threshold')
    original=quad.quadratic_expansion(source,tag)
    old={int(t):F(v) for t,v in original['hinge_coefficients'].items()}
    fc,atone=F(original['factorial_tail_coefficient']),F(original['at_one'])
    last=max(max(old),k)
    co={t:old.get(t,F(0))+fc*(int(t>=5)-int(t>=k)) for t in range(1,last+1)}
    co={t:v for t,v in co.items() if v}
    require(fc>0 and atone>=0 and co and all(1<=t<=8 and v>0 for t,v in co.items()),'Nonnegative same-cost shifted expansion')
    phi=lambda n:F(max(n-k,0)*max(n-k+1,0),2)
    expand=lambda n:atone+sum(a*max(n-t,0) for t,a in co.items())+fc*phi(n)
    entrance=max(last,original['polynomial_tail']['entrance'])
    finite={n:source.zero5_cost(tag,n) for n in range(1,entrance+2)}
    require(all(expand(n)==v for n,v in finite.items()),'All finite original transitions before the common tail')
    tail=(atone-sum(t*a for t,a in co.items())+fc*F(k*(k-1),2),
          sum(co.values())+fc*F(1-2*k,2),fc/2)
    require(tail==(F(original['polynomial_tail']['constant']),F(0),F(original['polynomial_tail']['leading'])),
            'Exact constant, linear and quadratic coefficients for every larger load')
    return {'factorial_threshold':k,'at_one':atone,'hinge_coefficients':co,'factorial_coefficient':fc,
        'original_phi5_expansion':original,'finite_transition_values':finite,
        'polynomial_tail':{'entrance':entrance,'constant':tail[0],'linear':tail[1],'leading':tail[2]}}

def all_tail_split(k):
    require(isinstance(k,int) and k>=1,'Positive integer factorial threshold')
    records=[]
    for b in range(1,7):
        d=b-k;phi=F(max(d,0)*max(d+1,0),2);h=max(d+1,0)
        if b>=k-1:
            require(phi==F(d*(d+1),2) and h==d+1,'For all nonnegative integer T the two quadratics agree')
            records.append({'head':b,'case':'all-T-exact-quadratic','constant':phi,
                'linear':F(2*d+1,2),'quadratic':F(1,2)})
        else:
            require(phi==0 and h==0 and d+1<0,'Shifted binomial argument is bounded by nonnegative T')
            records.append({'head':b,'case':'all-T-monotone-integer-binomial','argument_shift':d+1})
    return records

def make_problem(base,j,core,pair,depth,second,moment,shift,prior244,prior251,
                 complete_pair_tail,threshold,bank=None,proposer=None):
    """Fresh threshold-specific270 scanner with actual X/Y/V factorial crosses.

    The threshold is fixed before any part or objective cache is populated.
    All pruning lines are recomputed with the same complete original cost.
    """
    require(isinstance(threshold,int) and threshold>=2,'Integer factorial threshold at least two')
    problem=shift.make_problem(base,j,core,pair,depth,second,moment,prior244,prior251,
                               complete_pair_tail,bank=bank,proposer=proposer)
    require(problem.parts.cache_info().currsize==0,
            'Fresh threshold-specific instance before any cached factorial parts')
    problem.k=threshold
    original_objective=problem.objective
    problem.retain_zero7_cross=True

    @lru_cache(None)
    def cross_parts(self,layout,retain_zero7_cross):
        require(self.k==threshold,'The factorial threshold cannot change after construction')
        h=tuple(F(max(b-threshold+1,0))for b in self.head.bridge.head_load(layout));mom=self.mom
        z=tuple(w*v for w,v in zip(mom.w,h));p,d=mom.pre,mom.descendant
        coefficients=(max(sum(p[5*c+s]*z[5*c+s]for s in range(5))for c in range(5)),
            max(sum(d[5*c+s]*z[5*c+s]for c in range(5))for s in range(5)),
            max(sum(d[5*c+s]*z[5*c+s]for c in range(5)if j.ROOT[c]==r)for r,s in product(range(2),range(5))),
            max(a*b for a,b in zip(d,z)),max(z))
        old=sum(a*b for a,b in zip(coefficients,OLD_WEIGHTS))
        selected=sum(a*b for a,b in zip(coefficients,SELECTED_WEIGHTS)) if retain_zero7_cross else F(0)
        remaining=sum(a*b for a,b in zip(coefficients,REMAINING_WEIGHTS if retain_zero7_cross else OLD_WEIGHTS))
        require(old==mom.old_tail(z) and old==remaining+selected and min(old,selected,remaining)>=0,
                'Exact same-layout complete zero7 cross partition')
        endpoints=[]
        for theta in(j.LO,j.HI):
            residual=remaining+mom.old_tail(h)/5
            residual+=sum(weight*max(mom.lp(tuple(a*b for a,b in zip(mask,h)),theta)for mask in family)
                          for family,weight in zip(mom.masks[1:],RAW_MASK_WEIGHTS))
            require(residual>=0,'Nonnegative complete unretained cross endpoint')
            endpoints.append(residual)
        return {'h':h,'zero7_coefficients':coefficients,'old_zero7_cross':old,
                'selected_zero7_payment':selected,'remaining_zero7_cross':remaining,
                'complete_cross_residual_endpoints':tuple(endpoints)}

    def objective(self,co,layout,projection):
        require(self.k==threshold,'One fixed threshold per original-cost instance')
        obj,constant=original_objective(co,layout,projection)
        parts=self.cross_parts(layout,self.retain_zero7_cross);h=parts['h']
        c0,c1=parts['complete_cross_residual_endpoints'];old0,old1=(p[1]for p in self.parts(layout))
        obj[875]+=self.fc*((c1-c0)-(old1-old0));constant+=self.fc*(c0-old0)
        r,s,c63,r105,s105,r147,s245=projection
        for i,value in enumerate(h):
            c,k=divmod(i,5)
            first=int(j.ROOT[c]==r)+int(k==s)+int(c==c63)+int(j.ROOT[c]==r105 and k==s105)
            second_count=int(j.ROOT[c]==r147)+int(k==s245)
            positive7=self.fc*value*(F(1,5)+U1*first+U2*second_count)
            for mask in range(16):
                cell=16*i+mask;obj[cell]+=positive7
                if self.retain_zero7_cross:
                    obj[425+cell]+=self.fc*value*mask.bit_count()
                    for state,count in enumerate((1,1,2)):
                        obj[pair.V+400*state+cell]+=self.fc*value*count
        require(len(obj)==3306 and all(v>=0 for k,v in enumerate(obj)if k!=875),
                'Only the original common-theta secant coefficient may be signed')
        return obj,constant

    problem.cross_parts=MethodType(cross_parts,problem)
    problem.objective=MethodType(objective,problem)
    return problem


def calculate(base,bank,seed_rows):
    require(PINS,'Exact original mathematical source pins')
    io=module('generalized_io',base/'certificate_io.py');core=module('generalized_core',base/'frontier/j-geometry/j_face_joint_selected_heads.py')
    read=lambda name:json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', name+'.json')),object_pairs_hook=core.unique)
    prior244,prior251,source270,source272,comparison,source265=(read(name)for name in(
        'j_face_joint_selected_heads','j_face_retained135125_heads','j_face_shifted_factorial_quadratic_heads',
        'j_face_joint_factorial_cross_heads','j_face_joint_factorial_cross_complete_moment_cost_comparison','j_face_raw_prime_path_pairs'))
    pins=dict(PINS)
    for source in(prior244,prior251,source270,source272,comparison,source265):
        require(source['geometry']==source270['geometry'] and F(source['survivor_mass'])==F(3,20),
                'All sources use both identical entire actual saturated J faces')
        for path,pin in source['source_sha256'].items():
            require(path not in pins or pins[path]==pin,'Consistent mathematical input '+path);pins[path]=pin
    for path,pin in pins.items():require(sha256(io.read_artifact_bytes(base/path)).hexdigest()==pin,'Pinned actual source '+path)
    j=module('generalized_j',base/'frontier/j-geometry/j_face_coupled_seven_heads.py');pair=module('generalized_pair',base/'frontier/j-geometry/j_face_retained135125_heads.py')
    depth=module('generalized_depth',base/'frontier/comparison-bounds/second_depth_seven_comparison.py');second=module('generalized_second',base/'frontier/j-geometry/j_face_second_depth_retained_heads.py')
    moment=module('generalized_moment',base/'frontier/j-geometry/j_face_shared_square_factorial.py');shift=module('generalized_shift',base/'frontier/j-geometry/j_face_shifted_factorial_quadratic_heads.py')
    quad=module('generalized_quad',base/'frontier/moments-survival/whole_quadratic_same_head.py');inventory=module('generalized_inventory',base/'frontier/source-budgets/source_barrier_saturation.py')
    engine=inventory.Experiment(base)
    require(all(path in pins and pins[path]==pin for path,pin in engine.pins.items()),'The complete original52-cost inventory is pinned')
    tags=[row['tag']for row in engine.specs+engine.quadratic_specs]+[('s',F(81,n*n))for n in range(1,7)]
    require(len(tags)==52 and [(row['index'],row['threshold'])for row in seed_rows]==list(TARGETS),
            'Exactly the two unchanged original costs with explicit threshold-specific seeds')
    partitions=check_partitions();pairtail=F(source265['complete_tail_distinct_pairs'])
    require(pairtail==F(4879,7200)==F(source270['complete_pair_tail'])==F(source272['complete_pair_tail']),
            'The complete265 pair tail is unchanged at every threshold')
    previous={int(row['name'][5:]):F(row['upper'])for row in comparison['results']if row['name'].startswith('cost-')}
    rows=[];used=set();digest=sha256();layout_count=0
    for (index,k),seed in zip(TARGETS,seed_rows):
        expansion=shifted_identity(engine.source,quad,tags[index],k);split=all_tail_split(k)
        problem=make_problem(base,j,core,pair,depth,second,moment,shift,prior244,prior251,pairtail,k,bank=bank)
        require(problem.specification==source270['model']==source272['model'],
                'The entire unchanged3306-variable6354-inequality18-equality source model')
        problem.fc=expansion['factorial_coefficient'];problem.atone=expansion['at_one']
        layouts=0
        for layout in j.layouts():
            row={'index':index,'threshold':k,'layout':layout,'factorial_parts':problem.parts(layout),
                 'cross_components':problem.cross_parts(layout,True)}
            digest.update(json.dumps(encode(row),separators=(',',':')).encode());layouts+=1
        require(layouts==12500,'Every original head has a complete threshold-specific factorial and cross decomposition')
        layout_count+=layouts
        target={'index':index,'scan':{'coefficients':encode(expansion['hinge_coefficients']),
                                    'maximizing_certificate_branch':seed['branch']}}
        scan=problem.scan(target);upper=scan['complete_cost_upper']
        require(0<upper<previous[index] and scan['counts']['prior251_bounded']==0
                and scan['covered_containing_choices']==62500000,
                'A complete original-cost improvement over273 without hinge-only pruning')
        require(problem.used<=set(bank) and not problem.prior_used,'All full-cost duals supplied with no hinge-only bound')
        used.update(problem.used)
        branch=scan['maximizing_certificate_branch'];parts=problem.cross_parts(tuple(branch['layout']),True)
        rows.append({'index':index,'tag':tags[index],'factorial_threshold':k,'expansion':expansion,
            'all_head_tail_split':split,'retained_zero7_cross':True,'scan':scan,'complete_cost_upper':upper,
            'previous_adopted_upper':previous[index],'adopted_upper':upper,'improvement_over_previous':previous[index]-upper,
            'maximizing_cross_components':parts})
        print('Complete generalized factorial J cost'+str(index)+' threshold'+str(k)+' <= '+str(float(upper)),flush=True)
    kept={key:bank[key]for key in sorted(used)}
    encoded=problem.codec.encode_dual_bank(kept,inequality_count=6354,equality_count=18)
    require(problem.codec.decode_dual_bank(encoded,inequality_count=6354,equality_count=18)==kept,
            'Lossless canonical used full-objective rational dual bank')
    return encode({'schema':'erdos7-j-face-generalized-factorial-heads-v1','source_sha256':pins,'geometry':source270['geometry'],
        'source_mass':F(1,4),'survivor_mass':F(3,20),'model':problem.specification,'original_cost_indices':[v[0]for v in TARGETS],
        'factorial_thresholds':[v[1]for v in TARGETS],'positive7_cross_cost_indices':[v[0]for v in TARGETS],
        'zero7_cross_cost_indices':[v[0]for v in TARGETS],'complete_pair_tail':pairtail,
        'complete_positive7_hinge_tail':second.Z6,'cross_partitions':partitions,
        'original_head_count':12500,'threshold_layout_record_count':layout_count,'cross_endpoint_record_count':2*layout_count,
        'all_factorial_and_cross_components_sha256':digest.hexdigest(),'seed_rows':seed_rows,'results':rows,
        'encoded_rational_duals':encoded,'distinct_dual_count':len(kept),'rational_column_checks':3306*len(kept),
        'total_containing_choices':sum(row['scan']['covered_containing_choices']for row in rows),
        'total_independent_affine_checks':sum(row['scan']['independent_affine_checks']for row in rows),
        'scope':'Two unchanged original costs48/49 on both entire actual saturated J faces. Exact positive Phi3/Phi2 expansions and the all-nonnegative-integer-tail factorial bound use distinct fresh threshold-specific instances. Complete full-cost affine pruning is recomputed at the corresponding threshold. Positive-seven factorial crosses use actual common raw X with all six21/35/63/105/147/245 projections; zero-seven crosses use actual survivor Y and retained V for25/27/75/81/135/125. Every other cross remains in its complete geometric remainder and convex common-theta secant. The original3306-variable6354-inequality18-equality model and entire pair tail4879/7200 are unchanged. Each target covers62500000 original choices and every consumed dual column is checked. No actual attainment, off-face extension, full52-cost comparison, Lean verification or unrestricted Erdos7 result.'})


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    modes=parser.add_mutually_exclusive_group();modes.add_argument('--write',action='store_true');modes.add_argument('--check',action='store_true')
    parser.add_argument('--proposal',type=Path);args=parser.parse_args()
    io=module('generalized_reader',args.base/'certificate_io.py');core=module('generalized_json',args.base/'frontier/j-geometry/j_face_joint_selected_heads.py')
    require(args.proposal is None or args.write,'Only the writer accepts a proposal')
    require(not args.write or args.proposal is not None,'Writer requires a complete canonical dual proposal')
    proposed=json.loads(io.read_artifact_bytes(args.proposal if args.write else args.base/CERTIFICATE),object_pairs_hook=core.unique)
    codec=module('generalized_codec',args.base/'frontier/retained-transport/retained135_heavy_comparison.py')
    bank=codec.decode_dual_bank(proposed['encoded_rational_duals'],inequality_count=6354,equality_count=18)
    result=calculate(args.base,bank,proposed['seed_rows'])
    if args.write:io.write_certificate_text(args.base/CERTIFICATE,json.dumps(result,indent=2)+'\n')
    else:require(result==proposed,'Every complete generalized factorial original-cost certificate field recomputes exactly')
    print('PASS two original generalized-factorial costs;125000000 containing choices;'+str(result['distinct_dual_count'])+' exact3306-column duals; every full cross and pair tail.',flush=True)


if __name__=='__main__':
    try:main()
    except(ValueError,ArithmeticError,OSError,KeyError,TypeError,json.JSONDecodeError)as error:
        print('FAIL: '+str(error),file=sys.stderr);raise SystemExit(1)
