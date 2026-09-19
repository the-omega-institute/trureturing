#!/usr/bin/env python3
"""Complete pure Phi2/Phi3 observations on both original saturated J faces."""
import argparse,importlib.util,json,sys
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from pathlib import Path
sys.dont_write_bytecode=True
CERTIFICATE='certificates/source_norms/j-geometry/j_face_pure_low_factorial_heads.json'
THRESHOLDS=(2,3)
PINS={'frontier/j-geometry/j_face_joint_pair_factorial_heads.py': '779a8fcc6aab4db3ce7c991033f6f3f463b17297b2b3150702dd9e9af0003f69', 'certificates/source_norms/j-geometry/j_face_joint_pair_factorial_heads.json': 'be3dec5ac358d697ead0868cf73e626d11ef2fec3895a5e5fed99748e57ce26f', 'profile-notes/257-320/276-actual-retained-tail-pairs-strengthen-original-j-costs-and-square.md': '397f1db9f44157a345c31826f96920ea8776db620cbeb62bbbfd671dd3eab652', 'frontier/j-geometry/j_face_joint_pair_factorial_complete_moment_cost_comparison.py': '7ae33f70e1b3ebe7269b175fe6155847083660947d4c1f0e8e546a62ef9e6d08', 'certificates/source_norms/j-geometry/j_face_joint_pair_factorial_complete_moment_cost_comparison.json': 'e94c52713b862c3ea1805bd9442a1c62c915db554bc789a80c861b9d87db220f', 'profile-notes/257-320/277-actual-retained-pairs-improve-the-complete-j-comparison.md': '0be2ba1284f7a6d5b081c1b3a081dec1439166c4ab23a4d24370c51e1508e68b'}

def require(ok,message):
    if not ok:raise ValueError(message)

def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    require(spec is not None and spec.loader is not None,'Loadable published mathematical source')
    value=importlib.util.module_from_spec(spec);spec.loader.exec_module(value);return value

def encode(value):
    if isinstance(value,F):return str(value)
    if isinstance(value,dict):return {str(k):encode(v)for k,v in value.items()}
    if isinstance(value,(tuple,list)):return [encode(v)for v in value]
    return value

def pure_factorial_scan(problem,conditional,seed_branches):
    """Exhaustive pure-factorial scan with complete layout and conditional pair pruning."""
    require(problem.k in (2,3) and problem.fc==1 and problem.atone==0,
            'The empty hinge sum represents exactly its pure factorial function without a synthetic hinge')
    layouts=tuple(problem.j.layouts())
    projections=tuple(product(range(2),range(5),range(5),range(2),range(5),range(2),range(5)))
    require(len(layouts)==12500 and len(projections)==5000,'All original independent containing choices')
    layout_set,projection_set=set(layouts),set(projections)
    require(len(seed_branches)==30 and len({(tuple(r['layout']),tuple(r['projection']))for r in seed_branches})==30,
            'Thirty distinct explicit seed branches, without any optimality assumption')
    used_before=set(problem.used)
    def affine(layout,projection):
        pp=problem.parts(layout);zz=conditional.endpoints(projection)
        line=tuple(part[0]+problem.pair_tail-F(89,240)+pzz for part,pzz in zip(pp,zz))
        require(all(a<=part[0]+problem.pair_tail for a,part in zip(line,pp)),
                'Only the entire conditional PZZ block replaces its assigned old cap in this affine')
        return line
    def branch(layout,projection):
        require(layout in layout_set and projection in projection_set,'Original independent seed or scanned labels')
        value,key,constant=problem.dual_upper({},layout,projection);line=affine(layout,projection)
        return {'layout':layout,'projection':projection,'conditional_affine':line,'dual_upper':value,
                'adopted':min(value,max(line)),'dual_key':key,'constant':constant}
    seeds=[];best=F(-1);witness=None
    for seed in seed_branches:
        record=branch(tuple(seed['layout']),tuple(seed['projection']));seeds.append(record)
        if record['adopted']>best:best=record['adopted'];witness=record
    seed_upper=best;digest=sha256()
    counts={k:0 for k in ('layouts','layout_bounded','conditional_projections','conditional_bounded','joint_dual_branches')}
    maxima={'layout':F(-1),'conditional':F(-1)}
    for layout in layouts:
        counts['layouts']+=1;pp=problem.parts(layout);oldline=tuple(part[0]+problem.pair_tail for part in pp)
        if max(oldline)<=best:
            counts['layout_bounded']+=1;maxima['layout']=max(maxima['layout'],max(oldline))
            digest.update(repr(('layout',layout,oldline)).encode());continue
        for projection in projections:
            counts['conditional_projections']+=1;line=affine(layout,projection)
            if max(line)<=best:
                counts['conditional_bounded']+=1;maxima['conditional']=max(maxima['conditional'],max(line))
                digest.update(repr(('conditional',layout,projection,line)).encode());continue
            record=branch(layout,projection);counts['joint_dual_branches']+=1
            digest.update(repr(('joint',layout,projection,line,record['dual_key'],str(record['dual_upper']),str(record['constant']))).encode())
            if record['adopted']>best:best=record['adopted'];witness=record
    require(counts['layouts']==12500
            and counts['conditional_projections']==5000*(12500-counts['layout_bounded'])
            and counts['conditional_bounded']+counts['joint_dual_branches']==counts['conditional_projections']
            and 5000*counts['layout_bounded']+counts['conditional_bounded']+counts['joint_dual_branches']==62500000
            and max(maxima.values())<=best,'Every original pure-factorial choice retains all exponent tails')
    require(branch(witness['layout'],witness['projection'])==witness and witness['adopted']==best,
            'The maximizing certificate bound recomputes exactly, without actual attainment')
    final_branch=dict(witness)
    final_branch['projection21_35_63_105_147_245']=final_branch.pop('projection')
    return {'scanner_kind':'pure-factorial-complete-conditional','coefficients':{},'complete_cost_upper':best,
            'counts':counts,'covered_containing_choices':62500000,'seed_upper':seed_upper,'seed_records':seeds,
            'maximizing_certificate_branch':final_branch,'complete_tail_constant':witness['constant'],
            'independent_affine_checks':0,'maximum_pruned':maxima,'new_distinct_duals':len(problem.used-used_before),
            'all_branch_decisions_sha256':digest.hexdigest()}


def expansion(k):
    require(k in THRESHOLDS,'The two new pure observations have thresholds two and three')
    phi=lambda n:F(max(n-k,0)*max(n-k+1,0),2)
    polynomial=(F(k*(k-1),2),F(1-2*k,2),F(1,2))
    require(all(phi(n)==0 for n in range(1,k+1))
            and polynomial==(F(k*(k-1),2),F(1-2*k,2),F(1,2)),
            'Below-threshold zero branch and exact expansion of (n-k)(n-k+1)/2')
    return {'factorial_threshold':k,'at_one':F(0),'factorial_coefficient':F(1),'hinge_coefficients':{},
            'zero_branch_last_integer':k,'finite_transition_values':{n:phi(n)for n in range(1,k+2)},
            'polynomial_tail':{'entrance':k,'constant':polynomial[0],'linear':polynomial[1],'leading':polynomial[2]}}


def inputs(base):
    source=module('pure_low_source276',base/'frontier/j-geometry/j_face_joint_pair_factorial_heads.py')
    data=source.inputs(base);io,core=data['io'],data['core']
    read=lambda name:json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', name+'.json')),object_pairs_hook=core.unique)
    heads=read('j_face_joint_pair_factorial_heads');comparison=read('j_face_joint_pair_factorial_complete_moment_cost_comparison')
    pins=dict(data['pins'])
    for item in(heads,comparison):
        require(item['geometry']==data['source274']['geometry'] and F(item['survivor_mass'])==F(3,20),
                'The exact same two entire saturated actual J faces')
        for path,pin in item['source_sha256'].items():
            require(path not in pins or pins[path]==pin,'Consistent full mathematical source '+path);pins[path]=pin
    for path,pin in PINS.items():
        require(path not in pins or pins[path]==pin,'Consistent direct current input '+path);pins[path]=pin
    for path,pin in pins.items():require(sha256(io.read_artifact_bytes(base/path)).hexdigest()==pin,'Pinned mathematical source '+path)
    require(encode(data['conditional'].record)==heads['conditional_positive7']
            and encode(data['payments'])==heads['pair_partitions']
            and heads['total_containing_choices']==250000000,
            'The complete published conditional pair tables and every retained-pair payment reconstruct exactly')
    previous=module('pure_low_comparison277',base/'frontier/j-geometry/j_face_joint_pair_factorial_complete_moment_cost_comparison.py')
    olddata=previous.inputs(base)
    require([r['name']for r in comparison['basis']]==olddata['names'] and len(olddata['names'])==26
            and [F(r['upper'])for r in comparison['basis']]==olddata['bounds'],
            'The exact final277 scalar observations before the two additions')
    data.update(source=source,pins=pins,heads=heads,comparison277=comparison,olddata=olddata)
    return data


def old_moment_separation(data,k,upper):
    """A published277 feasible measure violates the new bound; not an actual source."""
    phi=lambda n:F(max(n-k,0)*max(n-k+1,0),2)
    candidates=[]
    for row in data['comparison277']['proof_data']:
        witness={int(n):F(v)for n,v in row['finite_moment_witness'].items()}
        candidates.append((sum(v*phi(n)for n,v in witness.items()),row['name'],witness))
    value,name,witness=max(candidates,key=lambda r:(r[0],r[1]))
    old=data['olddata'];measured=[sum(v*f(n)for n,v in witness.items())for f in old['functions']]
    require(min(witness.values())>0 and sum(witness.values())==F(3,20)
            and measured[0]==old['bounds'][0]
            and all(a<=b for a,b in zip(measured[1:],old['bounds'][1:]))
            and value>upper,
            'An independently feasible old26-moment measure is removed by the new pure-factorial inequality')
    return {'published277_target':name,'finite_moment_witness':witness,'old_basis_names':old['names'],
            'old_witness_moments':measured,'old_witness_slacks':[b-a for a,b in zip(measured,old['bounds'])],
            'new_factorial_moment':value,'new_source_upper':upper,'strict_violation':value-upper,
            'scope':'A feasible old scalar-moment measure, not an actual source configuration or actual attainment claim.'}


def calculate(base,bank,seed_rows):
    data=inputs(base);source=data['source']
    require([r['threshold']for r in seed_rows]==list(THRESHOLDS),'Both pure targets in increasing-threshold order')
    rows=[];used=set();digest=sha256();layout_count=0
    for k,seed in zip(THRESHOLDS,seed_rows):
        ex=expansion(k)
        problem=source.make_problem(base,*[data[v]for v in('j','core','pair','depth','second','moment','shift','generalized','prior244','prior251')],
                                    F(4879,7200),k,data['conditional'],data['payments'],bank=bank)
        problem.fc=F(1);problem.atone=F(0)
        require(problem.specification==data['heads']['model'],'Unchanged original3306-variable source constraints')
        count=0
        for layout in data['j'].layouts():
            component={'name':'factorial'+str(k),'threshold':k,'layout':layout,'factorial_parts':problem.parts(layout),
                       'cross_components':problem.cross_parts(layout,True)}
            digest.update(json.dumps(encode(component),separators=(',',':')).encode());count+=1
        require(count==12500,'Every original head at this fixed factorial threshold');layout_count+=count
        scan=pure_factorial_scan(problem,data['conditional'],seed['branches']);upper=scan['complete_cost_upper']
        require(upper>0 and not problem.prior_used and problem.used<=set(bank),
                'Positive complete pure-factorial bound from exactly supplied joint duals, without hinge-only pruning')
        used.update(problem.used);branch=scan['maximizing_certificate_branch']
        rows.append({'name':'factorial'+str(k),'factorial_threshold':k,'expansion':ex,
                     'all_head_tail_split':data['generalized'].all_tail_split(k),'scan':scan,
                     'complete_factorial_upper':upper,'old_moment_separation':old_moment_separation(data,k,upper),
                     'maximizing_cross_components':problem.cross_parts(tuple(branch['layout']),True),
                     'maximizing_conditional_PZZ_endpoints':data['conditional'].endpoints(tuple(branch['projection21_35_63_105_147_245']))})
        print('Complete pure Phi'+str(k)+' <= '+str(float(upper)),flush=True)
    kept={key:bank[key]for key in sorted(used)}
    encoded=problem.codec.encode_dual_bank(kept,inequality_count=6354,equality_count=18)
    require(problem.codec.decode_dual_bank(encoded,inequality_count=6354,equality_count=18)==kept,'Canonical exact consumed dual bank')
    return encode({'schema':'erdos7-j-face-pure-low-factorial-heads-v1','source_sha256':data['pins'],
        'geometry':data['heads']['geometry'],'source_mass':F(1,4),'survivor_mass':F(3,20),'model':problem.specification,
        'new_basis_names':['factorial2','factorial3'],'factorial_thresholds':THRESHOLDS,
        'original_affine_pruning_pair_tail':F(4879,7200),'cross_partitions':data['heads']['cross_partitions'],
        'pair_partitions':data['payments'],'conditional_positive7':data['conditional'].record,
        'original_head_count':12500,'threshold_layout_record_count':layout_count,'cross_endpoint_record_count':2*layout_count,
        'all_factorial_and_cross_components_sha256':digest.hexdigest(),'seed_rows':seed_rows,'results':rows,
        'encoded_rational_duals':encoded,'distinct_dual_count':len(kept),'rational_column_checks':3306*len(kept),
        'total_containing_choices':sum(r['scan']['covered_containing_choices']for r in rows),
        'scope':'Two complete pure factorial observations Phi2/Phi3 on both entire saturated actual J faces. Each target retains all62500000 original choices, separate fixed-threshold caches, actual retained raw/survivor crosses and POO/POZ pairs, complete conditional PZZ heads, common-theta secants and all omitted prime/cofactor depths. The empty hinge sum is kept exactly; complete layout pruning retains the old4879/7200 pair bound, and fixed-projection refinement replaces only its old89/240 PZZ component before exact joint dual checks. Each new observation excludes an explicitly checked feasible measure for all26 prior277 scalar constraints. Such measures need not be actual sources. No original cost, old observation or survival term is removed. The full52-cost consumer, off-face extension, global join, Lean verification and unrestricted Erdos7 remain outside this source certificate.'})


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    modes=parser.add_mutually_exclusive_group();modes.add_argument('--write',action='store_true');modes.add_argument('--check',action='store_true')
    parser.add_argument('--proposal',type=Path);args=parser.parse_args()
    require(args.proposal is None or args.write,'Only the writer accepts a proposal')
    require(not args.write or args.proposal is not None,'Writer requires complete exact duals and seed branches')
    io=module('pure_low_io',args.base/'certificate_io.py');core=module('pure_low_json',args.base/'frontier/j-geometry/j_face_joint_selected_heads.py')
    proposed=json.loads(io.read_artifact_bytes(args.proposal if args.write else args.base/CERTIFICATE),object_pairs_hook=core.unique)
    codec=module('pure_low_codec',args.base/'frontier/retained-transport/retained135_heavy_comparison.py')
    bank=codec.decode_dual_bank(proposed['encoded_rational_duals'],inequality_count=6354,equality_count=18)
    result=calculate(args.base,bank,proposed['seed_rows'])
    if args.write:io.write_certificate_text(args.base/CERTIFICATE,json.dumps(result,indent=2)+'\n')
    else:require(result==proposed,'Every complete pure-factorial observation field recomputes exactly')
    print('PASS purePhi2/Phi3;'+str(result['total_containing_choices'])+' original choices;'+str(result['distinct_dual_count'])+' exact3306-column duals; two genuine new observations.',flush=True)


if __name__=='__main__':
    try:main()
    except(ValueError,ArithmeticError,OSError,KeyError,TypeError,json.JSONDecodeError)as error:
        print('FAIL: '+str(error),file=sys.stderr);raise SystemExit(1)
