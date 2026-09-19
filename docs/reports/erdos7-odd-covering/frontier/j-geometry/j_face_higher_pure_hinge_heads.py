#!/usr/bin/env python3
"""Two complete higher pure-hinge observations on both original saturated J faces."""
import argparse,importlib.util,json,sys
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from pathlib import Path
sys.dont_write_bytecode=True
CERTIFICATE='certificates/source_norms/j-geometry/j_face_higher_pure_hinge_heads.json'
THRESHOLDS=(8,7)
PINS={'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2', 'frontier/j-geometry/j_face_triple_second_depth_heads.py': '4b3f190c4a8bf31d92b03cdadedba3644c66e258e583180f9868f449cab4d16c', 'certificates/source_norms/j-geometry/j_face_triple_second_depth_heads.json': '9740095781d0faa76071b8c39cb849b415ee9dbb0f63372aa27cd46451d15c2b', 'profile-notes/257-320/264-seven-retained-states-and-two-seven-depths-control-complete-j-heads.md': '137e1d47e3b589ea20555456b3d959f0abd70d6ff1394bf3e371fcb177d6f14f'}

def require(ok,message):
    if not ok:raise ValueError(message)

def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    require(spec is not None and spec.loader is not None,'Loadable existing mathematical provider')
    value=importlib.util.module_from_spec(spec);spec.loader.exec_module(value);return value

def encode(value):
    if isinstance(value,F):return str(value)
    if isinstance(value,dict):return {str(k):encode(v)for k,v in value.items()}
    if isinstance(value,(tuple,list)):return [encode(v)for v in value]
    return value

def inputs(base):
    require(PINS,'Pinned mathematical inputs')
    io=module('pure_hinge_io',base/'certificate_io.py')
    core=module('pure_hinge_core244',base/'frontier/j-geometry/j_face_joint_selected_heads.py')
    read=lambda n:json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', n+'.json')),object_pairs_hook=core.unique)
    prior244,prior251,prior256,prior264=(read(n)for n in('j_face_joint_selected_heads','j_face_retained135125_heads','j_face_second_depth_retained_heads','j_face_triple_second_depth_heads'))
    pins=dict(PINS)
    for source in(prior244,prior251,prior256,prior264):
        require(source['geometry']==prior264['geometry']and F(source['source_mass'])==F(1,4)
                and F(source['survivor_mass'])==F(3,20),'The same two entire actual saturated J faces')
        for path,pin in source['source_sha256'].items():
            require(path not in pins or pins[path]==pin,'Consistent complete source closure '+path);pins[path]=pin
    for path,pin in pins.items():require(sha256(io.read_artifact_bytes(base/path)).hexdigest()==pin,'Pinned mathematical source '+path)
    j=module('pure_hinge_affine',base/'frontier/j-geometry/j_face_coupled_seven_heads.py')
    pair=module('pure_hinge_pair',base/'frontier/j-geometry/j_face_retained135125_heads.py')
    depth=module('pure_hinge_depth',base/'frontier/comparison-bounds/second_depth_seven_comparison.py')
    triple=module('pure_hinge_triple264',base/'frontier/j-geometry/j_face_triple_second_depth_heads.py')
    require(j.Z4-F(6,245)*(F(1,8)+F(1,10))==triple.Z6==F(37,1225)
            and j.REMAINDERS[4]-sum(triple.CAPS)==F(6151,405000),
            'Only the retained135/125/225 and147/245 cap terms leave their original complete tails')
    return {'io':io,'core':core,'j':j,'pair':pair,'depth':depth,'triple':triple,'pins':pins,
            'prior244':prior244,'prior251':prior251,'prior256':prior256,'prior264':prior264}

def calculate(base,bank,seed_rows):
    data=inputs(base);j,triple=data['j'],data['triple']
    require([r['threshold']for r in seed_rows]==list(THRESHOLDS),'Exactly two complete pure-hinge targets in fixed order')
    layouts=set(j.layouts());projections=set(product(range(2),range(5),range(5),range(2),range(5)))
    rows=[];used=set();prior_used=set();depth_used=set()
    for t,seed in zip(THRESHOLDS,seed_rows):
        require(set(seed)=={'threshold','layout','projection21_35_63_105'}
                and tuple(seed['layout'])in layouts and tuple(seed['projection21_35_63_105'])in projections,
                'Original independent seed labels, without an optimality assumption')
        problem=triple.TripleSecondDepthJHead(base,*[data[k]for k in('j','core','pair','depth','prior244','prior251','prior256')],bank=dict(bank))
        require(problem.specification==data['prior264']['model']and problem.lp.nvars==6531
                and len(problem.lp.rows)==11211 and len(problem.lp.equalities)==19,
                'The unchanged264 actual raw/survivor model with seven135/125/225 states and their complement')
        target={'index':'H'+str(t),'scan':{'coefficients':{str(t):'1'},'maximizing_certificate_branch':{
            'layout':seed['layout'],'projection21_35_63_105':seed['projection21_35_63_105']}}}
        scan=problem.scan(target);upper=scan['complete_hinge_upper']
        require(upper>0 and scan['covered_containing_choices']==62500000 and problem.used<=set(bank),
                'Every complete original choice uses an exact supplied dual or complete affine bound')
        used.update(problem.used);prior_used.update(problem.prior_used);depth_used.update(problem.prior_depth_used)
        expansion={'at_one':F(0),'hinge_coefficients':{t:F(1)},'zero_branch_last_integer':t,
                   'finite_transition_values':{n:F(max(n-t,0))for n in range(1,t+2)},
                   'polynomial_tail':{'entrance':t,'constant':F(-t),'linear':F(1),'leading':F(0)}}
        rows.append({'name':'hinge'+str(t),'threshold':t,'expansion':expansion,'complete_hinge_upper':upper,'scan':scan,
                     'distinct_target_duals':len(problem.used)})
        print('Complete pure H'+str(t)+' <= '+str(float(upper)),flush=True)
    require(used==set(bank),'Every supplied rational dual is consumed on a complete original-target proof path')
    kept={key:bank[key]for key in sorted(used)}
    encoded=problem.codec.encode_dual_bank(kept,inequality_count=11211,equality_count=19)
    require(problem.codec.decode_dual_bank(encoded,inequality_count=11211,equality_count=19)==kept,
            'Canonical lossless rational-table/run-length dual bank')
    return encode({'schema':'erdos7-j-face-higher-pure-hinge-heads-v1','source_sha256':data['pins'],
        'geometry':data['prior264']['geometry'],'source_mass':F(1,4),'survivor_mass':F(3,20),'model':problem.specification,
        'new_basis_names':['hinge'+str(t)for t in sorted(THRESHOLDS)],'thresholds':THRESHOLDS,
        'retained_old_labels':[25,27,75,81,135,125,225],'retained_positive7_labels':[21,35,63,105,147,245],
        'complete_zero7_joint_remainder':j.REMAINDERS[4]-sum(triple.CAPS),
        'complete_zero7_affine_remainders':{t:j.REMAINDERS[min(t-1,4)]for t in THRESHOLDS},
        'removed_assigned_positive7_tail_caps':[F(3,980),F(3,1225)],'complete_positive7_tail':triple.Z6,
        'seed_rows':seed_rows,'results':rows,'encoded_rational_duals':encoded,'distinct_dual_count':len(kept),
        'rational_column_checks':6531*len(kept),'previous251_duals_used':sorted(prior_used),'previous256_duals_used':sorted(depth_used),
        'total_containing_choices':sum(r['scan']['covered_containing_choices']for r in rows),
        'total_independent_affine_checks':sum(r['scan']['independent_affine_checks']for r in rows),
        'scope':'Two complete higher pure-hinge observations H7/H8 on both entire actual saturated J faces. The original264 scanner and6531-variable actual raw/survivor constraints are unchanged. Each target includes every62500000 original independent containing choice, one common late interval, all seven135/125/225 membership states and their complement, independent147/245 labels, marked deletions and every exponent/cofactor tail. Pure Ht is exactly(n-t)_+ for every positive integer n. Each affine keeps its own original selected prefix and complete remainder; the joint objective keeps all seven old labels. No restricted seed maximum is extrapolated. A maximizing rational certificate bound is not an actual source attainment claim. The complete52-cost consumer, off-face extension, global join, Lean verification and unrestricted Erdos7 are outside this source certificate.'})

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    modes=parser.add_mutually_exclusive_group();modes.add_argument('--write',action='store_true');modes.add_argument('--check',action='store_true')
    parser.add_argument('--proposal',type=Path);args=parser.parse_args()
    require(args.proposal is None or args.write,'Only the writer accepts proposal data')
    require(not args.write or args.proposal is not None,'Writer requires complete exact duals and seed labels')
    io=module('pure_hinge_read_io',args.base/'certificate_io.py');core=module('pure_hinge_read_json',args.base/'frontier/j-geometry/j_face_joint_selected_heads.py')
    proposed=json.loads(io.read_artifact_bytes(args.proposal if args.write else args.base/CERTIFICATE),object_pairs_hook=core.unique)
    codec=module('pure_hinge_read_codec',args.base/'frontier/retained-transport/retained135_heavy_comparison.py')
    bank=codec.decode_dual_bank(proposed['encoded_rational_duals'],inequality_count=11211,equality_count=19)
    seeds=proposed['seed_rows']
    result=calculate(args.base,bank,seeds)
    if args.write:io.write_certificate_text(args.base/CERTIFICATE,json.dumps(result,indent=2)+'\n')
    else:require(result==proposed,'Every complete pure-hinge certificate field recomputes exactly')
    print('PASS two higher pure J hinges;'+str(result['total_containing_choices'])+' original choices;'+str(result['distinct_dual_count'])+' exact6531-column duals and complete exponent tails.',flush=True)

if __name__=='__main__':
    try:main()
    except(ValueError,ArithmeticError,OSError,KeyError,TypeError,json.JSONDecodeError)as error:
        print('FAIL: '+str(error),file=sys.stderr);raise SystemExit(1)
