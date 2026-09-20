#!/usr/bin/env python3
"""Complete raw J prime-path blocks improve both positive-seven pair inputs."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import importlib.util,json
from pathlib import Path
import sys
sys.dont_write_bytecode=True
CERTIFICATE='certificates/source_norms/j-geometry/j_face_raw_prime_path_pairs.json'
PINS={'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b', 'frontier/j-geometry/j_face_coherent_positive7_pairs.py': 'e88cd1035ccb6e3283475233584fd0ff101cc12ce33cdbbee52ccced22e637f0', 'certificates/source_norms/j-geometry/j_face_coherent_positive7_pairs.json': 'c3476d1aec97ab3be8fada4155d736b4a90bdd11f80230524d78d42304f6b074', 'profile-notes/257-320/258-independent-positive-seven-depths-share-one-complete-raw-source.md': 'b73e21d5f79bf242403f8ba8f463486319cdebfa6b7a9b3743ba3d6e97667c75', 'frontier/j-geometry/j_face_pure_path_square.py': '08cfded9d14294958bea613816f376eb822c6977ceef767e988a8b682b350030', 'profile-notes/193-256/253-two-complete-prime-path-blocks-sharpen-the-j-square.md': '630c9bd4f1375ae70e7612a6efaea26eb3934fd657e515f4487040199fd7107c'}


def require(ok,message):
    if not ok:raise ValueError(message)


def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    require(spec is not None and spec.loader is not None,'Loadable existing mathematics')
    value=importlib.util.module_from_spec(spec);spec.loader.exec_module(value);return value


def encode(value):
    if isinstance(value,F):return str(value)
    if isinstance(value,dict):return {str(k):encode(v) for k,v in value.items()}
    if isinstance(value,(list,tuple)):return [encode(v) for v in value]
    return value


def path_bound(prime,start,cross,caps,square):
    """One all-depth BR+binom(R,2) or2BR+R^2 block, including exact diagonals."""
    r=F(1,prime);initial=r**start;records=[]
    diagonal=initial/(1-r);pairs=initial*r/(1-r)**2
    for a,c in zip(cross,caps):
        reward0=2*a+c if square else a;rewardstep=2*c if square else c
        v0=reward0/(1-r)+rewardstep*r/(1-r)**2;v1=rewardstep/(1-r)
        require(reward0+r*(v0+v1)==v0 and rewardstep+r*v1==v1 and (1-r)*v0-reward0>=0,
                'All-count discounted Bellman identity and unchanged-component reward domination')
        records.append({'raw_head_cross_coefficient':a,'raw_density_cap':c,'reward_constant':reward0,
                        'reward_count_coefficient':rewardstep,'potential_constant':v0,'potential_count_coefficient':v1,
                        'unchanged_component_reward_slack':(1-r)*v0-reward0,'complete_path_upper':initial*v0})
    oldcross=(2 if square else 1)*max(cross)*diagonal
    oldpair=(2 if square else 1)*max(caps)*pairs
    olddiag=max(caps)*diagonal if square else F(0)
    old=oldcross+oldpair+olddiag;new=max(row['complete_path_upper'] for row in records)
    require(0<=new<=old,'A complete nonnegative raw prime-path block replaces exactly its own terms')
    return {'prime':prime,'first_depth':start,'square_block':square,'discount':r,'initial_weight':initial,
            'diagonal_geometric_weight':diagonal,'distinct_geometric_weight':pairs,
            'old_head_cross':oldcross,'old_distinct_pairs':oldpair,'old_diagonal':olddiag,
            'old_complete_block':old,'new_complete_block':new,'block_change':new-old,'path_records':records,
            'maximizing_cells_or_slots':[i for i,row in enumerate(records) if row['complete_path_upper']==new]}


def scan(j,moment,joint,p,e,c3,c5,omitted):
    problem=moment.JMomentHead(j);best={k:F(-1) for k in ('pair','square')};witness={k:[] for k in best}
    digest=sha256();count=0;strict={k:0 for k in best}
    for il,layout in enumerate(j.layouts()):
        B=joint.head_load(j,layout);cross=problem.old_tail(B)
        A3=tuple(sum(p[c][s]*B[5*c+s] for s in range(5)) for c in range(5))
        A5=tuple(sum(e[c][s]*B[5*c+s] for c in range(5)) for s in range(5))
        blocks={name:[path_bound(3,3,A3,c3,name=='square'),path_bound(5,2,A5,c5,name=='square')] for name in best}
        changes={name:sum(row['block_change'] for row in rows) for name,rows in blocks.items()}
        for theta in (j.LO,j.HI):
            oldpair=problem.lp(tuple(F(b*(b-1),2) for b in B),theta)+cross+omitted['raw_omitted_distinct_pairs']
            oldsquare=problem.lp(tuple(F(b*b) for b in B),theta)+2*cross+2*omitted['raw_omitted_distinct_pairs']+omitted['raw_omitted_diagonal']
            old={'pair':oldpair,'square':oldsquare};new={name:old[name]+changes[name] for name in best}
            row={'layout':layout,'theta':theta,'raw_cross_coefficients3':A3,'raw_cross_coefficients5':A5,
                 'complete_raw_old_cross':cross,'previous_pair_upper':oldpair,'previous_square_upper':oldsquare,
                 'pair_change':changes['pair'],'square_change':changes['square'],'complete_pair_upper':new['pair'],'complete_square_upper':new['square']}
            digest.update(json.dumps(encode(row),separators=(',',':')).encode())
            for name in best:
                strict[name]+=int(new[name]<old[name])
                if new[name]>best[name]:best[name]=new[name];witness[name]=[]
                if new[name]==best[name]:witness[name].append({**row,'complete_prime_blocks':blocks[name]})
            count+=1
        if (il+1)%2500==0:print('Raw prime-path J heads: '+str(il+1)+' of12500, both endpoints',flush=True)
    require(count==25000 and best=={'pair':F(125,96),'square':F(53,16)},'All12500 independent original layouts and both endpoints give the complete uniform raw bounds')
    require(all(len(rows)==1 and tuple(rows[0]['layout'])==(1,4,4,1,4,4,4) and rows[0]['theta']==j.HI for rows in witness.values()),
            'Exact maximizing certificate branch, without source-attainment assertion')
    return {'original_head_count':12500,'endpoint_record_count':count,'raw_objective_evaluations':2*count,
            'complete_raw_old_pair_upper':best['pair'],'complete_raw_old_square_upper':best['square'],
            'strictly_improved_endpoint_records':strict,'maximizing_witnesses':witness,'all_endpoint_components_sha256':digest.hexdigest()}


def calculate(base):
    require(PINS,'Pinned exact source closure')
    io=module('raw_path_io',base/'certificate_io.py');previous=module('raw_path_previous',base/'frontier/j-geometry/j_face_coherent_positive7_pairs.py')
    old=json.loads(io.read_artifact_bytes(base/previous.CERTIFICATE),object_pairs_hook=previous.unique)
    pins=dict(PINS)
    for path,pin in old['source_sha256'].items():
        require(path not in pins or pins[path]==pin,'Consistent exact J source closure '+path);pins[path]=pin
    for path,pin in pins.items():require(sha256(io.read_artifact_bytes(base/path)).hexdigest()==pin,'Pinned mathematical input '+path)
    j=module('raw_path_source',base/'frontier/j-geometry/j_face_coupled_seven_heads.py');moment=module('raw_path_moment',base/'frontier/j-geometry/j_face_shared_square_factorial.py');joint=module('raw_path_head',base/'frontier/j-geometry/j_face_joint_retained_square.py');tails=module('raw_path_tails',base/'frontier/moments-survival/complete_off_face_factorial_tail.py')
    p,raw,e,w=j.source_tables(j.LO);c3=tuple(sum(row) for row in p);c5=tuple(sum(row[s] for row in e) for s in range(5))
    require(c3==tuple(map(F,('3/4','3/4','3/10','1/2','1/2'))) and c5==tuple(map(F,('0','1/6','7/18','1/2','1/2'))),
            'Raw Lambda cylinder caps from the normalized ternary and absolute descendant-five source tables')
    require(all(j.source_tables(theta)[0]==p and j.source_tables(theta)[2]==e for theta in (j.LO,j.HI)),
            'The raw prime-cylinder operators have no late-parameter dependence')
    tail=moment.complete_tail(tails);omitted=previous.complete_raw_omitted_tail(tails,tail);partition=previous.complete_positive7_partition(tail)
    require(encode(tail)==old['original_complete_tail_partition'] and encode(omitted)==old['complete_raw_omitted_tail']
            and encode(partition)==old['complete_positive7_partition'],'Every inherited complete pair and diagonal tail remains exact')
    old_pair_blocks=(max(c3)*tails.geometric(3,3,1,-3),max(c5)*tails.geometric(5,2,1,-2))
    old_diagonals=(max(c3)*tails.geometric(3,3),max(c5)*tails.geometric(5,2))
    require(old_pair_blocks==(F(1,48),F(1,160)) and old_diagonals==(F(1,24),F(1,40))
            and omitted['raw_omitted_distinct_pairs']-sum(old_pair_blocks)>0
            and omitted['raw_omitted_diagonal']-sum(old_diagonals)>0,'Two disjoint pure-prime pair subseries and their exact assigned diagonals')
    result=scan(j,moment,joint,p,e,c3,c5,omitted)
    P=result['complete_raw_old_pair_upper'];Q=result['complete_raw_old_square_upper']
    newPZZ=partition['complete_same_depth_weight']*P+partition['complete_cross_depth_weight']*Q
    gain=F(old['complete_PZZ_upper'])-newPZZ
    require(newPZZ==F(89,240) and gain==F(1,432)>0,'Complete same-depth and independent cross-depth raw-source improvement')
    pairs=F(old['complete_tail_distinct_pairs'])-gain;ordered=F(old['complete_ordered_tail_square'])-2*gain
    square=F(old['complete_square_upper'])-2*gain;factorial=F(old['complete_factorial_upper'])-gain
    other=F(old['updated_other12499_square_upper'])-2*gain
    require(pairs==tail['old_old_distinct']+tail['old_positive7']+newPZZ and ordered==2*pairs+tail['old_diagonal']+tail['positive7_diagonal']
            and square-other==F(old['remaining_other_head_gap'])==F(11,450),'Replace only the complete PZZ block in every controller and complementary layout')
    costs=[]
    for row in old['quadratic_results']:
        prior=F(row['cost_upper']);charge=F(row['new_complete_pair_charge'])-2*gain;upper=F(row['unchanged_joint_head_upper'])+charge
        require(upper==prior-2*gain and charge==2*pairs,'Each independent quadratic head retains its whole function and exact pair charge')
        costs.append({'index':row['index'],'tag':row['tag'],'previous_cost_upper':prior,'unchanged_joint_head_upper':F(row['unchanged_joint_head_upper']),
                      'new_complete_pair_charge':charge,'cost_upper':upper,'cost_improvement':2*gain})
    return encode({'schema':'erdos7-j-face-raw-prime-path-pairs-v1','source_sha256':pins,'geometry':old['geometry'],'raw_source_mass':F(1,4),
        'survivor_mass':F(3,20),'complete_mean_upper':F(16,25),'raw_prime_caps':{'three_cells':c3,'five_slots':c5},
        'complete_raw_omitted_tail':omitted,'complete_positive7_partition':partition,'raw_head_scan':result,
        'old_raw_pure_prime_distinct_pair_blocks':old_pair_blocks,'old_raw_pure_prime_diagonals':old_diagonals,
        'previous_PZZ_upper':F(old['complete_PZZ_upper']),'complete_PZZ_upper':newPZZ,'complete_pair_improvement':gain,
        'complete_tail_distinct_pairs':pairs,'complete_ordered_tail_square':ordered,'previous_complete_square_upper':F(old['complete_square_upper']),
        'complete_square_upper':square,'complete_square_improvement':2*gain,'previous_complete_factorial_upper':F(old['complete_factorial_upper']),
        'complete_factorial_upper':factorial,'complete_factorial_improvement':gain,'updated_other12499_square_upper':other,'remaining_other_head_gap':square-other,
        'original_cost_indices':[47,48],'quadratic_results':costs,
        'scope':'Both whole actual saturated J faces, every12500 independent six-label raw head at both common-theta endpoints and all omitted original cofactor depths. Disjoint raw pure3/pure5 head-cross/self-pair blocks use complete discounted potentials with Lambda caps, without importing survivor density or survivor-specific caps. Distinct positive-seven depths retain independent full tests on one raw source; the PZZ block is replaced in every complete factorial/square/quadratic consumer and complementary square layout. No simultaneous source optimizer, off-face/full52-cost comparison, Lean verification or unrestricted Erdos7 result.'})


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2]);modes=parser.add_mutually_exclusive_group();modes.add_argument('--write',action='store_true');modes.add_argument('--check',action='store_true');args=parser.parse_args()
    result=calculate(args.base);io=module('raw_path_writer',args.base/'certificate_io.py');old=module('raw_path_json',args.base/'frontier/j-geometry/j_face_coherent_positive7_pairs.py')
    if args.write:io.write_certificate_text(args.base/CERTIFICATE,json.dumps(result,indent=2)+'\n')
    else:require(result==json.loads(io.read_artifact_bytes(args.base/CERTIFICATE),object_pairs_hook=old.unique),'Every complete raw prime-path certificate field recomputes exactly')
    print('PASS raw prime paths:Praw='+result['raw_head_scan']['complete_raw_old_pair_upper']+', Qraw='+result['raw_head_scan']['complete_raw_old_square_upper']+', PZZ='+result['complete_PZZ_upper']+'; all25000 endpoint records and complete tails.',flush=True)


if __name__=='__main__':
    try:main()
    except(ValueError,ArithmeticError,OSError,KeyError,TypeError,json.JSONDecodeError)as error:
        print('FAIL: '+str(error),file=sys.stderr);raise SystemExit(1)
