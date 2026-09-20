#!/usr/bin/env python3
"""Independent positive-seven depths share one actual raw J source for pair bounds."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import combinations, product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j-geometry/j_face_coherent_positive7_pairs.json'
PINS = {'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b', 'frontier/j-geometry/j_face_shared_square_factorial.py': '19f35e9bcac13999e3912fd5d5a2d43ddcef667e5913d4b6d8ec4c171c911e44', 'certificates/source_norms/j-geometry/j_face_shared_square_factorial.json': '1db541160baeed8896d715a0250856ef98cfc7c0968d3ec2d18ea0efeb3dc2ce', 'frontier/j-geometry/j_face_pure_path_factorial.py': 'e8d473b5b497178b1fa6afa9eb90100bf1d096dc2ee750e223e62ace435883fb', 'certificates/source_norms/j-geometry/j_face_pure_path_factorial.json': 'ac8355ca4c908c15ba18983714aa4f00ce54a44717fdcdb30f105965008c5a55', 'profile-notes/193-256/248-the-complete-j-factorial-tail-retains-both-prime-paths.md': '9cfc69bc8dfe8a402664132f6c80736ecd822d8c16a3a4a6955b268cebd20379', 'frontier/j-geometry/j_face_pure_path_square.py': '08cfded9d14294958bea613816f376eb822c6977ceef767e988a8b682b350030', 'certificates/source_norms/j-geometry/j_face_pure_path_square.json': '5572358ded61518c7785e1336adf0183a53c16c74d675f50b5f1e75e2cad7f49', 'profile-notes/193-256/253-two-complete-prime-path-blocks-sharpen-the-j-square.md': '630c9bd4f1375ae70e7612a6efaea26eb3934fd657e515f4487040199fd7107c', 'frontier/j-geometry/j_face_joint_quadratic_heads.py': 'b792c6eb7ab8b5dd6e10e3bc986314fe0843c85a00f837e02996b373d1bd17a2', 'certificates/source_norms/j-geometry/j_face_joint_quadratic_heads.json': '57d46f22d0c289bc01d036bdc332ae7ffe7a9f53a39dd31c1304a6ed021c6b47', 'profile-notes/193-256/247-two-original-j-quadratic-costs-share-hinges-and-factorial-head.md': '46cb4ccbeb6773daac5d7848b1f529cf0db3f00e16d7745b97bb338a34ce00f2', 'profile-notes/001-064/63-six-original-labels-strengthen-the-endpoint-square.md': '7cd33178b924cf57f0e9253e45585954a8f41948c2e998ed8df958c7663a8801'}
HEAD = tuple(product(range(3), range(2)))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable original mathematical input')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Unique certificate key: '+key)
        result[key] = value
    return result


def raw_cap(a, b):
    if b == 0:
        return (F(1,4),F(1,8),F(1,12))[a] if a < 3 else F(3,4)*F(1,3**a)
    if a < 3:
        return (F(1,2),F(1,3),F(1,9))[a]*F(1,5**b)
    return F(1,3**a*5**b)


def complete_raw_omitted_tail(factorial, tail):
    g = factorial.geometric
    coefficients = tuple(map(F, ('3/4','1/2','1/3','1/9')))
    a0,aw,b1,b2,bw2 = g(3,3),g(3,3,2,1),g(5,1),g(5,2),g(5,2,2,1)
    pure = dict(zip(('pure3','pure5','root5','cell5'),
        (coefficients[0]*g(3,3,2,-6),coefficients[1]*g(5,2,2,-4),
         coefficients[2]*g(5,2,6,-10),coefficients[3]*g(5,2,10,-16))))
    mixed = g(3,3,6,-16)/5+aw*bw2-13*a0*b2
    pair = (sum(pure.values())+mixed)/2
    diagonal = coefficients[0]*a0+sum(coefficients[1:])*b2+a0*b1
    require((pair,diagonal) == (F(209,1440),F(37,360)) and min(*pure.values(),mixed) >= 0,
            'Complete original raw omitted pair and diagonal series, without survivor weights')
    require(tuple(F(tail['raw_cofactor_coefficients'][i]) for i in (3,4,5,6)) == coefficients,
            'The raw J coefficients from the original241 partition')
    checks = []
    for A,B in ((3,2),(5,4),(8,7)):
        labels = tuple(product(range(A+1),range(B+1)))
        omitted = tuple(x for x in labels if x not in HEAD)
        counts = dict.fromkeys(labels,0)
        for x,y in product(omitted,repeat=2):
            counts[max(x[0],y[0]),max(x[1],y[1])] += 1
        require(all(counts[x] == factorial.pair_multiplicities(*x)[0] for x in labels),
                'Independent original omitted-label counts at every finite-prefix LCM')
        direct = sum(raw_cap(max(x[0],y[0]),max(x[1],y[1])) for x,y in combinations(omitted,2))
        weighted = sum(F(counts[x]-1,2)*raw_cap(*x) for x in omitted)
        partial = lambda p,start,stop,slope=0,intercept=1: g(p,start,slope,intercept)-g(p,stop+1,slope,intercept)
        finite_pure = (coefficients[0]*partial(3,3,A,2,-6)
            +coefficients[1]*partial(5,2,B,2,-4)+coefficients[2]*partial(5,2,B,6,-10)
            +coefficients[3]*partial(5,2,B,10,-16))
        finite_mixed = (partial(3,3,A,6,-16)/5
            +partial(3,3,A,2,1)*partial(5,2,B,2,1)-13*partial(3,3,A)*partial(5,2,B))
        finite_diagonal = sum(raw_cap(*x) for x in omitted)
        require(direct == weighted == (finite_pure+finite_mixed)/2 and pair >= direct
                and finite_diagonal == coefficients[0]*partial(3,3,A)
                    +sum(coefficients[1:])*partial(5,2,B)+partial(3,3,A)*partial(5,1,B)
                and diagonal >= finite_diagonal,
                'Direct distinct pairs, ordered-minus-diagonal counts and exact geometric prefix agree')
        checks.append({'maximum_three_depth':A,'maximum_five_depth':B,'old_label_count':len(labels),
            'omitted_label_count':len(omitted),'raw_omitted_pair_prefix':direct,
            'complete_pair_remainder':pair-direct,'raw_omitted_diagonal_prefix':finite_diagonal,
            'complete_diagonal_remainder':diagonal-finite_diagonal})
    return {'raw_pure_coefficients':coefficients,'weighted_pure_blocks_before_halving':pure,
            'weighted_mixed_before_halving':mixed,'raw_omitted_distinct_pairs':pair,
            'raw_omitted_diagonal':diagonal,'independent_lcm_prefix_checks':checks}


def complete_positive7_partition(tail):
    q, density = F(1,7),F(6,5)
    same = density*q/(1-q)
    cross = density*q*q/(1-q)**2
    require((same,cross,same+2*cross) == (F(1,5),F(1,30),F(4,15)),
            'All equal positive depths and all unordered unequal positive depths')
    old_PZZ = F(tail['positive7_positive7_distinct'])
    square,linear = F(tail['raw_old_square_cap']),F(tail['raw_old_linear_cap'])
    pair = (square-linear)/2
    require((linear,square,old_PZZ) == (F(3,4),F(57,16),F(2,5))
            and old_PZZ == same*pair+cross*square,
            'The complete old assigned-cap PZZ series; no subtraction of unknown moments')
    checks = []
    for cut in (1,3,7):
        old_labels = tuple(product(range(5),range(4)))
        labels = [(a,b,e) for e in range(1,cut+1) for a,b in old_labels]
        finite_pair = sum(raw_cap(max(a,c),max(b,d)) for (a,b),(c,d) in combinations(old_labels,2))
        finite_square = sum(raw_cap(max(a,c),max(b,d)) for (a,b),(c,d) in product(old_labels,repeat=2))
        direct = sum(raw_cap(max(a,c),max(b,d))*density*q**max(e,f)
                     for (a,b,e),(c,d,f) in combinations(labels,2))
        finite_same = sum(density*q**e for e in range(1,cut+1))
        finite_cross = sum(density*q**f for e,f in combinations(range(1,cut+1),2))
        same_tail = density*q**(cut+1)/(1-q)
        cross_tail = density*q**(cut+1)*(F(cut)/(1-q)+q/(1-q)**2)
        require(direct == finite_same*finite_pair+finite_cross*finite_square
                and finite_same+same_tail == same and finite_cross+cross_tail == cross,
                'Independent finite original-label pair enumeration plus exact all-depth remainder')
        checks.append({'maximum_seven_depth':cut,'original_label_count':len(labels),
                       'direct_distinct_pair_cap_sum':direct,'finite_same_depth_weight':finite_same,
                       'finite_cross_depth_weight':finite_cross,'remaining_same_depth_weight':same_tail,
                       'remaining_cross_depth_weight':cross_tail})
    return {'old_raw_complete_assigned_pair_cap':pair,'old_raw_complete_assigned_square_cap':square,
            'old_raw_complete_assigned_diagonal_cap':linear,'complete_same_depth_weight':same,
            'complete_cross_depth_weight':cross,'old_PZZ':old_PZZ,
            'complete_tail_checks':checks}


def raw_head_scan(j, moment, joint, omitted):
    problem = moment.JMomentHead(j)
    geometries = []
    for theta in (j.LO,j.HI):
        _,caps,_,_ = j.source_tables(theta)
        flat = tuple(v for row in caps for v in row)
        supported = tuple(i for i in range(10,25) if flat[i] > 0)
        require((sum(flat[:5]),sum(flat[5:10]),sum(flat[10:])) == (F(1,24),F(1,12),F(2,15))
                and len(supported) == 8 and min(flat[i] for i in supported) >= F(1,90),
                'Exact raw group budgets and enough capacity for the common1/120 surplus correction')
        geometries.append({'theta':theta,'raw_caps':flat,'root1_positive_entries':supported})
    require(geometries[0]['root1_positive_entries'] == geometries[1]['root1_positive_entries'],
            'Fixed positive support and affine capacities on the entire late interval')
    best = {key:F(-1) for key in ('pair','square','whole_pair','whole_square')}
    witnesses = {key:[] for key in best}
    digest,count = sha256(),0
    for il,layout in enumerate(j.layouts()):
        B = joint.head_load(j,layout)
        pair = tuple(F(b*(b-1),2) for b in B)
        square = tuple(F(b*b) for b in B)
        cross = problem.old_tail(B)
        require(min(B) >= 1 and max(B) <= 6 and all(2*a+b == c for a,b,c in zip(pair,B,square)),
                'The same original six-label head for both raw objectives')
        for theta in (j.LO,j.HI):
            values = {'pair':problem.lp(pair,theta),'square':problem.lp(square,theta)}
            values['whole_pair'] = values['pair']+cross+omitted['raw_omitted_distinct_pairs']
            values['whole_square'] = values['square']+2*cross+2*omitted['raw_omitted_distinct_pairs']+omitted['raw_omitted_diagonal']
            row = {'layout':layout,'theta':theta,'raw_pair_upper':values['pair'],'raw_square_upper':values['square'],
                   'complete_raw_old_cross':cross,'whole_raw_pair_upper':values['whole_pair'],
                   'whole_raw_square_upper':values['whole_square']}
            digest.update(json.dumps(encode(row),separators=(',',':')).encode())
            for key,value in values.items():
                if value > best[key]:
                    best[key],witnesses[key] = value,[]
                if value == best[key]:
                    witnesses[key].append(row)
            count += 1
        if (il+1)%2500 == 0:
            print('Checked '+str(il+1)+' independent raw J heads at both endpoints',flush=True)
    require(count == 25000 and best == {'pair':F(91,120),'square':F(769,360),
                                      'whole_pair':F(377,288),'whole_square':F(481,144)}
            and all(len(rows) == 1 for rows in witnesses.values()),
            'Complete12500-layout, two-endpoint uniform raw pair and square maxima')
    require(all(tuple(rows[0]['layout']) == (1,4,4,1,4,4,4) and rows[0]['theta'] == j.HI
                for rows in witnesses.values()), 'Exact maximizing certificate layout, without source-attainment claim')
    return {'original_head_count':12500,'endpoint_record_count':count,'raw_objective_evaluations':2*count,
            'raw_source_endpoint_geometry':geometries,'complete_raw_head_pair_upper':best['pair'],
            'complete_raw_head_square_upper':best['square'],'complete_raw_old_pair_upper':best['whole_pair'],
            'complete_raw_old_square_upper':best['whole_square'],'maximizing_witnesses':witnesses,
            'all_endpoint_components_sha256':digest.hexdigest()}


def calculate(base):
    require(PINS and sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'],
            'Pinned canonical artifact reader')
    io = module('j_coherent7_io',base/'certificate_io.py')
    read = lambda name:json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', name+'.json')),
                                  object_pairs_hook=unique)
    original,factorial,square,quadratic = (read(name) for name in ('j_face_shared_square_factorial',
        'j_face_pure_path_factorial','j_face_pure_path_square','j_face_joint_quadratic_heads'))
    pins = dict(PINS)
    for source in (original,factorial,square,quadratic):
        for path,pin in source['source_sha256'].items():
            require(path not in pins or pins[path] == pin,'Consistent mathematical source '+path)
            pins[path] = pin
    for path,pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin,'Pinned mathematical input '+path)
    require(all(source['geometry'] == original['geometry'] and F(source['survivor_mass']) == F(3,20)
                for source in (factorial,square,quadratic)), 'The same two complete actual saturated J faces')
    j = module('j_coherent7_source',base/'frontier/j-geometry/j_face_coupled_seven_heads.py')
    moment = module('j_coherent7_moment',base/'frontier/j-geometry/j_face_shared_square_factorial.py')
    joint = module('j_coherent7_head',base/'frontier/j-geometry/j_face_joint_retained_square.py')
    tails = module('j_coherent7_tail',base/'frontier/moments-survival/complete_off_face_factorial_tail.py')
    tail = moment.complete_tail(tails)
    require(encode(tail) == original['complete_tail_partition'] == factorial['complete_tail_partition']
            == square['complete_original_tail_partition'] and F(quadratic['complete_tail_distinct_pairs']) == tail['distinct_tail_pairs'],
            'Exactly the common241 complete pair partition in all three later constructions')
    omitted = complete_raw_omitted_tail(tails,tail)
    partition = complete_positive7_partition(tail)
    scan = raw_head_scan(j,moment,joint,omitted)
    new_PZZ = partition['complete_same_depth_weight']*scan['complete_raw_old_pair_upper']
    new_PZZ += partition['complete_cross_depth_weight']*scan['complete_raw_old_square_upper']
    gain = partition['old_PZZ']-new_PZZ
    new_pairs = tail['distinct_tail_pairs']-gain
    new_ordered = tail['complete_ordered_tail_square']-2*gain
    require((gain,new_PZZ,new_pairs,new_ordered) == (F(29,1080),F(403,1080),F(14687,21600),F(17261,10800))
            and new_pairs == tail['old_old_distinct']+tail['old_positive7']+new_PZZ
            and new_ordered == 2*new_pairs+tail['old_diagonal']+tail['positive7_diagonal'],
            'Strict PZZ replacement; every other pair and both diagonals remain')
    prior_factorial,prior_square = F(factorial['complete_factorial_upper']),F(square['complete_square_upper'])
    require(prior_factorial == F(6313,7200) and prior_square == F(5509,1200)
            and F(factorial['combined_head_maximum'])+tail['distinct_tail_pairs'] == prior_factorial,
            'The248 zero-seven prime-path changes are outside this PZZ block')
    final_factorial = F(factorial['combined_head_maximum'])+new_pairs
    final_square = prior_square-2*gain
    other_square = F(square['other_head_maximum'])-2*gain
    require(F(square['unchanged_ordered_distinct_pairs']) >= 2*partition['old_PZZ']
            and F(square['controller_complete_upper']) == prior_square
            and square['original_head_count'] == 12500 and square['inherited_other_complete_head_count'] == 12499
            and final_square-other_square == F(square['other_head_gap_to_new_upper']) == F(11,450),
            'Apply the same PZZ replacement to the controller and every other253 layout, disjoint from its zero-seven path blocks')
    require((final_factorial,final_square,other_square) == (F(18359,21600),F(49001,10800),F(48737,10800)),
            'Complete factorial and square outputs with the same uniform tail replacement')
    costs = []
    require(quadratic['original_cost_indices'] == [47,48], 'The two unchanged independent original quadratic costs')
    for row in quadratic['quadratic_results']:
        coefficient = F(row['expansion']['factorial_tail_coefficient'])
        old_upper = F(row['cost_upper'])
        old_outside = F(row['constant_mass_and_complete_pair_tail'])
        new_outside = old_outside-coefficient*gain
        new_upper = F(row['scan']['joint_head_upper'])+new_outside
        require(coefficient == 2 and F(row['expansion']['at_one']) == 0
                and old_outside == coefficient*tail['distinct_tail_pairs']
                and old_upper == F(row['scan']['joint_head_upper'])+old_outside
                and new_upper == old_upper-2*gain > 0,
                'Each exact original247 cost keeps its own whole-head bound and replaces its same complete pair constant')
        costs.append({'index':row['index'],'tag':row['tag'],'previous_cost_upper':old_upper,
                      'unchanged_joint_head_upper':F(row['scan']['joint_head_upper']),
                      'old_complete_pair_charge':old_outside,'new_complete_pair_charge':new_outside,
                      'cost_upper':new_upper,'cost_improvement':2*gain})
    return encode({'schema':'erdos7-j-face-coherent-positive7-pairs-v1','source_sha256':pins,
        'geometry':original['geometry'],'survivor_mass':F(3,20),'complete_mean_upper':F(16,25),
        'original_complete_tail_partition':tail,'complete_raw_omitted_tail':omitted,
        'complete_positive7_partition':partition,'raw_head_scan':scan,
        'complete_PZZ_upper':new_PZZ,'complete_pair_improvement':gain,
        'complete_tail_distinct_pairs':new_pairs,'complete_ordered_tail_square':new_ordered,
        'previous_complete_factorial_upper':prior_factorial,'complete_factorial_upper':final_factorial,
        'complete_factorial_improvement':gain,'previous_complete_square_upper':prior_square,
        'complete_square_upper':final_square,'complete_square_improvement':2*gain,
        'updated_other12499_square_upper':other_square,'remaining_other_head_gap':final_square-other_square,
        'quadratic_results':costs,'original_cost_indices':[47,48],
        'inherited248_all_head_components_sha256':factorial['all_head_components_sha256'],
        'inherited253_other_layout_digest':square['inherited245_all_head_components_sha256'],
        'scope':'Both whole actual saturated J faces and all12500 independent raw six-label layouts at both common-theta endpoints, retaining the complete raw omitted-cofactor crosses, distinct pairs and diagonals. Each positive-seven depth has its own complete original old-cofactor load Fe; same-depth distinct pairs use377/288 and cross-depth products on the same actual raw source use2FeFf<=Fe^2+Ff^2 and481/144. The entire positive7/positive7 distinct-pair block is replaced; every other original pair and both complete diagonals remain. The PZZ gain is disjoint from248/253 zero-seven prime-path blocks and replaces every247 cost47/48 complete pair constant. No common head across depths or costs, actual attainment, off-face/full52-cost comparison, Lean verification or unrestricted Erdos7 result.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write',action='store_true')
    modes.add_argument('--check',action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('j_coherent7_writer',args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE,json.dumps(result,indent=2)+'\n')
    else:
        require(result == json.loads(io.read_artifact_bytes(args.base/CERTIFICATE),object_pairs_hook=unique),
                'Every exact coherent positive-seven pair and consumer field recomputes')
    print('PASS:PZZ='+result['complete_PZZ_upper']+'; Phi5='+result['complete_factorial_upper']
          +'; square='+result['complete_square_upper']+'; both original quadratic costs improve by29/540.',flush=True)


if __name__ == '__main__':
    try:
        main()
    except(ValueError,ArithmeticError,OSError,KeyError,TypeError,json.JSONDecodeError) as error:
        print('FAIL: '+str(error),file=sys.stderr)
        raise SystemExit(1)
