#!/usr/bin/env python3
"""Complete saturated-J AP11 and affine-tail costs using one common late split.

Fifteen new scans retain219's entire theta interval and every original
containing branch. The existing AP13 and two heavy scans are consumed only.
No K-source cost or bound is used as a J input.
"""
import argparse
from concurrent.futures import ProcessPoolExecutor, as_completed
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
from time import perf_counter

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j-geometry/j_face_complete_survival_linear_heads.json'
PINS = {'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b', 'verify_joint_frontier.py': '0b5cd35851d36f3af83aee19e02267cb05abc8bf07611a12083fca6f3d9bd765', 'frontier/source-budgets/source_barrier_saturation.py': '6fe57e39274df1fa4a80ae4d4a22cab7b1d78d28c4f428b789071e3fb7776a64', 'frontier/j-geometry/j_face_coupled_seven_heads.py': '78b6846a4eaa01ed568eb96e8c49dca67d0a19df094bc1e28ba5214100dc70a0', 'certificates/source_norms/j-geometry/j_face_coupled_seven_heads.json': 'ecdd57e17e466435943a0fff4d63da9841e72ef2631651d5ecc451dcac586449', 'profile-notes/193-256/219-one-late-source-split-controls-complete-saturated-j-heads.md': 'd0f78950c8ca3040b2a90c5b5d470655cd53e68f39b54d531f793915490ff73d', 'profile-notes/129-192/130-the-whole-j-face-forces-source-anti-alignment.md': 'c9c11d0250836f7abc67eed901716f867b7a916a9797afcaa14b3f70584e33a8'}
LINEAR_INDICES = (1,2,7,10,17,18,23,26,32,33,36)
MASS, MEAN, HINGE1 = F(3,20), F(16,25), F(49,100)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name,path)
    require(spec is not None and spec.loader is not None, 'Loadable J proof provider')
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def encode(value):
    if isinstance(value,F):
        return str(value)
    if isinstance(value,dict):
        return {str(k):encode(v) for k,v in value.items()}
    if isinstance(value,(tuple,list)):
        return [encode(v) for v in value]
    return value


def prepare_jobs(source, engine):
    """The original function/count identities are independent of source face."""
    probabilities = {n:source.ap_count_probability(11,F(5,3),n) for n in range(1,5)}
    identities = {1:{5:F(1)},2:{2:F(1),3:F(1)},3:{1:F(1),2:F(2)},4:{1:F(3),2:F(1)}}
    tail0,tail1 = tuple(F(50,3)*v for v in source.geom(11,5)[:2])
    require((tail0,tail1)==(F(5,43923),F(17,29282))
            and sum(probabilities.values())+tail0==1
            and sum(n*p for n,p in probabilities.items())+tail1==F(7,6),
            'Complete original count distribution and infinite first moment')
    for n,a in identities.items():
        require(min(a.values())>0 and sum(a.values())==n and sum(t*v for t,v in a.items())==5
                and all(sum(v*max(k-t,0) for t,v in a.items())==max(n*k-5,0) for k in range(1,7)),
                'All finite count transitions and the entire affine continuation')
    jobs = []
    for block in range(4):
        a = {t:sum(probabilities[n]*identities[n].get(t,0)/n for n in range(block+1,5))
                 +(tail0 if t==1 else 0) for t in (1,2,3,5)}
        a = {t:v for t,v in a.items() if v}
        jobs.append({'name':'AP11-'+str(block),'kind':'AP11','block':block,'coefficients':a,'at_one':F(0)})
    for i in LINEAR_INDICES:
        tag = engine.specs[i]['tag']
        f = lambda n:engine.source.zero5_cost(tag,n)
        degree,leading,constant,cutoff = engine.source.zero5_cost_metadata(tag)
        a = {1:f(2)-f(1)}|{t:f(t+1)-2*f(t)+f(t-1) for t in range(2,9)}
        require(degree==1 and 1<=cutoff<=8 and min(a.values())>=0 and f(1)>=0
                and all(f(1)+sum(v*max(n-t,0) for t,v in a.items())==f(n) for n in range(1,10))
                and sum(a.values())==leading and f(1)-sum(t*v for t,v in a.items())==constant,
                'The exact original affine cost for every positive integer load')
        jobs.append({'name':'linear-'+str(i),'kind':'cost','index':i,'original_tag':tag,
                     'coefficients':{t:v for t,v in a.items() if v},'at_one':f(1),
                     'complete_tail_entrance':cutoff,'complete_tail_slope':leading,'complete_tail_constant':constant})
    require(len(jobs)==15 and len({j['name'] for j in jobs})==15, 'Four independent AP11 blocks and eleven original costs')
    return jobs, {'probabilities':probabilities,'all_load_identities':identities,'tail_probability':tail0,
                  'tail_first_moment':tail1,'remaining_hinge1_coefficient':tail1-4*tail0,
                  'whole_constant_coefficient':tail1-5*tail0}


def scan_job(base_string, job):
    """One fresh objective; the original219 scanner owns all branch semantics."""
    start = perf_counter()
    base = Path(base_string)
    provider = module('j_additional_scanner',base/'frontier/j-geometry/j_face_coupled_seven_heads.py')
    problem = provider.SaturatedJCoupledSevenHead(base)
    scan = problem.scan(job['coefficients'])
    require(scan['original_head_projection_branches']==125000
            and scan['expanded_branches']+scan['bounded_without_extra_projections']==125000
            and scan['expanded_objective_count_including_seed']==500+50*scan['expanded_branches'],
            'All6250000 containing choices covered by evaluated or uniformly bounded branches')
    require(scan['independent_rational_checks']==10, 'Independent unscaled branch and maximizing-witness checks')
    raw = job['at_one']*MASS+scan['complete_hinge_upper']
    mean = job['at_one']*MASS+sum(job['coefficients'].values())*HINGE1
    result = {**job,'scan':scan,'complete_head_upper':raw,'complete_mean_only_upper':mean,
              'adopted_upper':min(raw,mean),'improvement_over_mean_only':mean-min(raw,mean),
              'covered_containing_choices':6250000}
    return result,perf_counter()-start


def calculate(base, workers=2):
    require(type(workers) is int and workers in (1,2), 'One or two independent scan processes')
    io = module('j_additional_io',base/'certificate_io.py')
    predecessor = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/j-geometry/j_face_coupled_seven_heads.json'))
    pins = dict(PINS)
    for path,pin in predecessor['source_sha256'].items():
        require(path not in pins or pins[path]==pin, 'Consistent original J theorem input '+path)
        pins[path] = pin
    engine = module('j_additional_inventory',base/'frontier/source-budgets/source_barrier_saturation.py').Experiment(base)
    for path,pin in engine.pins.items():
        require(path not in pins or pins[path]==pin, 'Consistent original cost definition '+path)
        pins[path] = pin
    for path,pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest()==pin, 'Pinned mathematical input '+path)
    geometry = predecessor['geometry']
    require(F(geometry['source_mass'])==F(1,4) and F(geometry['survivor_mass'])==MASS
            and list(map(F,geometry['late_split_interval']))==[F(1,135),F(1,90)]
            and F(predecessor['complete_mean_upper'])==MEAN
            and F(predecessor['hinge1_upper'])==HINGE1==MEAN-MASS,
            'The entire original219 J domain and complete mean interface')
    inherited = {str(r['index']):r for r in predecessor['results']}
    require(set(inherited)=={'AP13','0','16'}, 'Consume the three previous J heads without rescanning them')
    source = module('j_additional_count',base/'verify_joint_frontier.py')
    jobs,count = prepare_jobs(source,engine)
    outputs = {}
    if workers==1:
        results = (scan_job(str(base),job) for job in jobs)
        for row,seconds in results:
            outputs[row['name']] = row
            print(row['name']+': '+str(float(row['adopted_upper']))+'; expanded='+str(row['scan']['expanded_branches'])
                  +'; crossings='+str(row['scan']['strict_crossing_branches_including_seed'])+'; seconds='+str(round(seconds,3)),flush=True)
    else:
        with ProcessPoolExecutor(max_workers=workers) as pool:
            pending = [pool.submit(scan_job,str(base),job) for job in jobs]
            for future in as_completed(pending):
                row,seconds = future.result()
                outputs[row['name']] = row
                print(row['name']+': '+str(float(row['adopted_upper']))+'; expanded='+str(row['scan']['expanded_branches'])
                      +'; crossings='+str(row['scan']['strict_crossing_branches_including_seed'])+'; seconds='+str(round(seconds,3)),flush=True)
    rows = [outputs[j['name']] for j in jobs]
    require(len(rows)==15 and sum(r['covered_containing_choices'] for r in rows)==93750000,
            'All fifteen independent complete objectives retain all original choices')
    U4 = F(inherited['AP13']['adopted_upper'])
    require(U4==F(29483,147000), 'The existing219 J AP13 result')
    tail = count['remaining_hinge1_coefficient']*HINGE1+count['whole_constant_coefficient']*MASS
    require(count['remaining_hinge1_coefficient']==F(1,7986)
            and count['whole_constant_coefficient']==F(1,87846), 'Entire positive infinite count tail')
    AP11 = sum(outputs['AP11-'+str(i)]['adopted_upper'] for i in range(4))
    denominator = MASS-U4/6-(AP11+tail)/7
    require(denominator>0, 'Complete positive J survival denominator')
    return encode({'schema':'erdos7-j-face-complete-survival-linear-heads-v1','source_sha256':pins,
        'geometry':geometry,'source_mass':F(1,4),'mass':MASS,'complete_mean_upper':MEAN,'hinge1_upper':HINGE1,
        'original_linear_indices':LINEAR_INDICES,'count_law':count,'results':rows,
        'inherited_AP13_upper':U4,'inherited_heavy_costs':{i:F(inherited[str(i)]['adopted_upper']) for i in (0,16)},
        'complete_count_tail_upper':tail,'complete_AP11_sum_upper':AP11,'uniform_denominator_lower':denominator,
        'new_objective_count':15,'total_containing_choices':93750000,
        'total_expanded_four_projection_evaluations_including_seeds':sum(r['scan']['expanded_objective_count_including_seed'] for r in rows),
        'total_independent_rational_checks':sum(r['scan']['independent_rational_checks'] for r in rows),
        'scope':'Four complete AP11 blocks and eleven original affine-tail costs on both entire saturated actual J faces, plus the complete AP survival denominator using the existing219 independent AP13 result. Every objective retains all6250000 containing choices, one common theta in[1/135,1/90], both affine endpoints and every exact interior crossing, J survivor mass3/20 and all infinite exponent/count tails. Existing219 AP13/heavy0/heavy16 are consumed without rescanning. No K-source145 cost, K forced27 rule, actual attainment, off-face extension, complete52-cost/global comparison, Lean verification or unrestricted Erdos7 result is asserted.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    parser.add_argument('--workers',type=int,choices=(1,2),default=2)
    modes = parser.add_mutually_exclusive_group();modes.add_argument('--write',action='store_true');modes.add_argument('--check',action='store_true')
    args = parser.parse_args();result = calculate(args.base,args.workers)
    io = module('j_additional_output',args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE,json.dumps(result,indent=2)+'\n')
    else:
        require(result==json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)), 'Exact complete J survival/linear certificate')
    print('Complete J survival denominator >= '+str(float(F(result['uniform_denominator_lower']))))
    print('PASS:15 complete J heads,93750000 containing choices,150 independent rational checks and the entire AP count tail.')


if __name__=='__main__':
    try:
        main()
    except(ValueError,ArithmeticError,OSError,KeyError,TypeError,json.JSONDecodeError) as error:
        print('FAIL: '+str(error),file=sys.stderr)
        raise SystemExit(1)
