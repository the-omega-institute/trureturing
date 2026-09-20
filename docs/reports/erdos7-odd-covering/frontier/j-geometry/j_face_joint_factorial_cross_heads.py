#!/usr/bin/env python3
"""Original J quadratic costs with joint raw and survivor factorial crosses."""
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
CERTIFICATE='certificates/source_norms/j-geometry/j_face_joint_factorial_cross_heads.json'
PINS={'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b', 'frontier/j-geometry/j_face_shifted_factorial_quadratic_heads.py': '885e5b0d5bee98c0439b45faf1dc582f578af1b8da7a4704d7845c36083f048d', 'certificates/source_norms/j-geometry/j_face_shifted_factorial_quadratic_heads.json': '1ff643151c6b2bab8fc6d938aa5432830fcfe02be7539e9fb9eb3a3131014ea4', 'profile-notes/257-320/270-shifted-factorial-heads-strengthen-three-original-j-quadratic-costs.md': 'd7b85e393d321d5f90ebc6eb8eee60fa45dd4368d8c201530fd4d680f686a8ee', 'frontier/j-geometry/j_face_shifted_factorial_complete_moment_cost_comparison.py': 'ed0c235cbf8a5cb2059a0756cfb4e3cdeb07082f70438218982a0dbe622d317a', 'certificates/source_norms/j-geometry/j_face_shifted_factorial_complete_moment_cost_comparison.json': 'c8b6935cf40a099ebb0e021438cc97a79f7d16a77d3f542a7a17abdc8287901b', 'profile-notes/257-320/271-three-shifted-factorial-costs-improve-the-complete-j-comparison.md': '1e43a485dc646e789a2107892c0a22d21d892f5cff7ed4e0a660292b319c3504'}
INDICES=(41,47,48)
ZERO7_INDICES=(41,48)
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


def make_problem(base,j,core,pair,depth,second,moment,shift,prior244,prior251,
                 complete_pair_tail,bank=None,proposer=None):
    """Reuse270's complete pruning/scanner, with one actual X/Y cross objective.

    Set retain_zero7_cross per target. This changes only its complete LP
    objective; every old270 full-cost affine line remains a valid bound.
    """
    problem=shift.make_problem(base,j,core,pair,depth,second,moment,prior244,prior251,
                               complete_pair_tail,bank=bank,proposer=proposer)
    original_objective=problem.objective
    problem.retain_zero7_cross=False

    @lru_cache(None)
    def cross_parts(self,layout,retain_zero7_cross):
        h=tuple(F(max(b-3,0))for b in self.head.bridge.head_load(layout));mom=self.mom
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
    require(PINS,'Exact mathematical source pins')
    io=module('joint_cross_io',base/'certificate_io.py');core=module('joint_cross_core244',base/'frontier/j-geometry/j_face_joint_selected_heads.py')
    read=lambda name:json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', name+'.json')),object_pairs_hook=core.unique)
    prior244,prior251,source270,comparison,source265=(read(name)for name in('j_face_joint_selected_heads','j_face_retained135125_heads',
        'j_face_shifted_factorial_quadratic_heads','j_face_shifted_factorial_complete_moment_cost_comparison','j_face_raw_prime_path_pairs'))
    pins=dict(PINS)
    for source in(prior244,prior251,source270,comparison,source265):
        require(source['geometry']==source270['geometry'] and F(source['survivor_mass'])==F(3,20),
                'Every input concerns both identical entire actual saturated J faces')
        for path,pin in source['source_sha256'].items():
            require(path not in pins or pins[path]==pin,'Consistent source pin '+path);pins[path]=pin
    for path,pin in pins.items():require(sha256(io.read_artifact_bytes(base/path)).hexdigest()==pin,'Pinned actual source '+path)
    j=module('joint_cross_j',base/'frontier/j-geometry/j_face_coupled_seven_heads.py');pair=module('joint_cross_pair',base/'frontier/j-geometry/j_face_retained135125_heads.py')
    depth=module('joint_cross_depth',base/'frontier/comparison-bounds/second_depth_seven_comparison.py');second=module('joint_cross_second',base/'frontier/j-geometry/j_face_second_depth_retained_heads.py')
    moment=module('joint_cross_moment',base/'frontier/j-geometry/j_face_shared_square_factorial.py');shift=module('joint_cross_shift',base/'frontier/j-geometry/j_face_shifted_factorial_quadratic_heads.py')
    quad=module('joint_cross_quad',base/'frontier/moments-survival/whole_quadratic_same_head.py');inventory=module('joint_cross_inventory',base/'frontier/source-budgets/source_barrier_saturation.py')
    engine=inventory.Experiment(base)
    require(all(path in pins and pins[path]==pin for path,pin in engine.pins.items()),'The full original52-cost inventory is pinned')
    tags=[row['tag']for row in engine.specs+engine.quadratic_specs]+[('s',F(81,n*n))for n in range(1,7)]
    require(len(tags)==52 and [row['index']for row in seed_rows]==list(INDICES),'Three original cost targets and full-search seeds')
    partitions=check_partitions();pairtail=F(source265['complete_tail_distinct_pairs'])
    require(pairtail==F(4879,7200)==F(source270['complete_pair_tail']),'The complete265 pair tail is unchanged')
    problem=make_problem(base,j,core,pair,depth,second,moment,shift,prior244,prior251,pairtail,bank=bank)
    require(problem.specification==source270['model'],'The entire unchanged3306-variable source and all original rows')
    digest=sha256();layouts=0
    for layout in j.layouts():
        for mode in(False,True):
            row={'layout':layout,'retain_zero7_cross':mode,'cross_components':problem.cross_parts(layout,mode)}
            digest.update(json.dumps(encode(row),separators=(',',':')).encode())
        layouts+=1
    require(layouts==12500,'Both complete cross decompositions cover all original head layouts')
    previous={int(row['name'][5:]):F(row['upper'])for row in comparison['results']if row['name'].startswith('cost-')}
    original={row['index']:row for row in source270['results']};rows=[]
    for index,seed in zip(INDICES,seed_rows):
        expansion=shift.shifted_expansion(engine.source,quad,tags[index]);require(encode(expansion)==original[index]['expansion'],'The unchanged original all-load identity')
        problem.fc=expansion['factorial_coefficient'];problem.atone=expansion['at_one'];problem.retain_zero7_cross=index in ZERO7_INDICES
        target={'index':index,'scan':{'coefficients':encode(expansion['hinge_coefficients']),'maximizing_certificate_branch':seed['branch']}}
        scan=problem.scan(target);upper=scan['complete_cost_upper']
        require(0<upper<previous[index] and scan['counts']['prior251_bounded']==0,'A strict complete improvement over the271 original-cost upper')
        branch=scan['maximizing_certificate_branch'];parts=problem.cross_parts(tuple(branch['layout']),problem.retain_zero7_cross)
        rows.append({'index':index,'tag':tags[index],'expansion':expansion,'retained_zero7_cross':problem.retain_zero7_cross,
            'scan':scan,'complete_cost_upper':upper,'previous_adopted_upper':previous[index],'adopted_upper':upper,
            'improvement_over_previous':previous[index]-upper,'maximizing_cross_components':parts})
        print('Complete joint factorial cross J cost'+str(index)+' <= '+str(float(upper)),flush=True)
    require(problem.used<=set(bank) and not problem.prior_used,'All required full-cost duals supplied; no hinge-only bound used')
    kept={key:bank[key]for key in sorted(problem.used)};encoded=problem.codec.encode_dual_bank(kept,inequality_count=6354,equality_count=18)
    require(problem.codec.decode_dual_bank(encoded,inequality_count=6354,equality_count=18)==kept,'Lossless used full-objective dual bank')
    return encode({'schema':'erdos7-j-face-joint-factorial-cross-heads-v1','source_sha256':pins,'geometry':source270['geometry'],
        'source_mass':F(1,4),'survivor_mass':F(3,20),'model':problem.specification,'original_cost_indices':INDICES,
        'positive7_cross_cost_indices':INDICES,'zero7_cross_cost_indices':ZERO7_INDICES,
        'factorial_threshold':4,'complete_pair_tail':pairtail,'complete_positive7_hinge_tail':second.Z6,'cross_partitions':partitions,
        'original_head_count':layouts,'cross_mode_count':2,'cross_endpoint_record_count':4*layouts,
        'all_cross_components_sha256':digest.hexdigest(),'seed_rows':seed_rows,'results':rows,
        'encoded_rational_duals':encoded,'distinct_dual_count':len(kept),'rational_column_checks':3306*len(kept),
        'total_containing_choices':sum(row['scan']['covered_containing_choices']for row in rows),
        'total_independent_affine_checks':sum(row['scan']['independent_affine_checks']for row in rows),
        'scope':'Three unchanged original costs41/47/48 on both entire actual saturated J faces. CompletePhi4 expansions and original270 full-cost affine pruning remain. Positive-seven factorial crosses use the actual common raw X with all six21/35/63/105/147/245 projections;41/48 additionally use actual survivor Y and retained V for the six25/27/75/81/135/125 zero-seven labels. Every other zero-seven and positive-seven cross is retained in its complete geometric remainder and convex common-theta secant. The original3306-variable6354-inequality18-equality model and complete pair tail4879/7200 are unchanged. Each target covers62500000 original containing choices and every dual column is checked. No actual attainment, off-face extension, full52-cost comparison, Lean verification or unrestricted Erdos7 result.'})


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    modes=parser.add_mutually_exclusive_group();modes.add_argument('--write',action='store_true');modes.add_argument('--check',action='store_true')
    parser.add_argument('--proposal',type=Path);args=parser.parse_args()
    io=module('joint_cross_reader',args.base/'certificate_io.py');core=module('joint_cross_json',args.base/'frontier/j-geometry/j_face_joint_selected_heads.py')
    require(args.proposal is None or args.write,'Only the writer accepts a proposal')
    if args.write:
        require(args.proposal is not None,'Complete proposed dual bank and explicit seeds')
        proposed=json.loads(io.read_artifact_bytes(args.proposal),object_pairs_hook=core.unique);bank=proposed['bank'];seeds=proposed['seed_rows']
    else:
        proposed=json.loads(io.read_artifact_bytes(args.base/CERTIFICATE),object_pairs_hook=core.unique)
        codec=module('joint_cross_codec',args.base/'frontier/retained-transport/retained135_heavy_comparison.py')
        bank=codec.decode_dual_bank(proposed['encoded_rational_duals'],inequality_count=6354,equality_count=18);seeds=proposed['seed_rows']
    result=calculate(args.base,bank,seeds)
    if args.write:io.write_certificate_text(args.base/CERTIFICATE,json.dumps(result,indent=2)+'\n')
    else:require(result==proposed,'Every joint factorial cross original-cost certificate field recomputes exactly')
    print('PASS three original joint-cross quadratic costs;187500000 containing choices;'+str(result['distinct_dual_count'])+' exact3306-column duals; every full cross and pair tail.',flush=True)


if __name__=='__main__':
    try:main()
    except(ValueError,ArithmeticError,OSError,KeyError,TypeError,json.JSONDecodeError)as error:
        print('FAIL: '+str(error),file=sys.stderr);raise SystemExit(1)
