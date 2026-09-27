#!/usr/bin/env python3
"""Exact outside-weight budget for a finite joint exponent region.

Uses the verified literal154 depth profile and its full geometric extension.
The degree7 region is a sufficient outside-union budget under one actual law;
its polynomial product is auxiliary accounting, not actual independence.
All required checks remain active under Python -O.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from pathlib import Path
import json
import sys
sys.dont_write_bytecode=True
SOURCES=('certificate_io.py', 'frontier/source-budgets/head_exponent_downset.py', 'problem-details/56-exponent-frontiers-and-cylinder-cover-certificates.md', 'problem-details/57-balanced-depth-profile-and-degree-seven-frontier.md', 'problem-details/54-depth-profile-head-laws-with-unrestricted-original-tails.md', 'problem-details/55-adaptive-read-once-head-orders-with-unrestricted-tail-comparison.md', 'problem-details/04b-arbitrary-star-head-residues-with-unrestricted-tails.md', 'problem-details/04c-full-history-capped-laws-and-exact-global-optimization.md', 'problem-details/04-a-complete-star-family-refutes-the-unrestricted-gamma-73-bound.md', 'frontier/source-budgets/balanced_profile_head_input.json', 'frontier/source-budgets/capped_head_bellman.py', 'frontier/source-budgets/balanced_profile_tail_budget.py', 'certificates/source_norms/source-budgets/balanced_profile_tail_budget.json', '../../../D5/S3/Arith/Congruence/ConditionalComparison/ThreePrime/Comparison.lean', '../../../D5/S3/Arith/Congruence/ConditionalComparison/CappedGainRearrangement.lean', '../../../Library/Arith/schroeder2026noncoverage.md', '../../../Library/Arith/balister2018covering.md')
def require(ok,message):
    if not ok:raise ValueError(message)


def load_module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    require(spec is not None and spec.loader is not None,'readable canonical module')
    value=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value

def bind_certificate(base, io, source_bytes, path, producer, schema):
    raw = io.read_artifact_bytes(base/path)
    record = json.loads(raw, object_pairs_hook=io._unique)
    require(record['schema'] == schema, 'canonical certificate schema: '+path)
    producer_raw = io.read_artifact_bytes(base/producer)
    require(record['producer_sha256'] == sha256(producer_raw).hexdigest(), 'current producer: '+producer)
    source_bytes[path] = raw
    source_bytes[producer] = producer_raw
    for name, digest in record['source_sha256'].items():
        dep = io.read_artifact_bytes(base/name)
        require(sha256(dep).hexdigest() == digest, 'current dependency: '+name)
        require(name not in source_bytes or source_bytes[name] == dep, 'consistent dependency: '+name)
        source_bytes[name] = dep
    return record


def calculate(base):
    io=load_module('head_region_io',base/'certificate_io.py')
    source_bytes={name:io.read_artifact_bytes(base/name) for name in SOURCES}
    record=bind_certificate(base,io,source_bytes,'certificates/source_norms/source-budgets/balanced_profile_tail_budget.json','frontier/source-budgets/balanced_profile_tail_budget.py','balanced-profile-tail-budget-v1')
    verified=bind_certificate(base,io,source_bytes,'certificates/source_norms/source-budgets/balanced_profile_tail_verification.json','frontier/source-budgets/verify_balanced_profile_tail_budget.py','balanced-profile-tail-verification-v1')
    require(verified['C_upper']==record['C_upper'] and verified['J_upper']==record['J_upper'],'same independently verified tail budget')
    data=json.loads(source_bytes['frontier/source-budgets/balanced_profile_head_input.json'],object_pairs_hook=io._unique)
    convolve=load_module('existing_exponent_convolution',base/'frontier/source-budgets/head_exponent_downset.py').convolve
    require(record['profiles']==data['profiles'] and data['schema']=='depth-profile-head-input-v1',
            'same original profile and coordinate inventory')
    require(record['B']==16384 and record['global_prime_index']==1900 and record['tail_stages']==1879,
            'complete previously verified continuation interval')
    require(F(record['T_lower'])>=F(326059,4),'certified stopping threshold')
    literal=load_module('head_region_literal_labels',base/'frontier/source-budgets/capped_head_bellman.py')
    labels=literal.counterexample_154_labels()
    require(data['head_label_source']=='frontier/source-budgets/capped_head_bellman.py' and
            data['head_label_factory']=='counterexample_154_labels','unique literal154 source')
    p=data['prime_order'];profiles=[[F(x) for x in row] for row in record['profiles']]
    total=F(1);coefficients=[F(1)];counts=[F(1)]
    for prime,row in zip(p,profiles):
        h=len(row)-1
        lifted=lambda e:row[e] if e<=h else row[h]/prime**(e-h)
        total*=sum(row)+row[-1]/(prime-1)
        coefficients=convolve(coefficients,[lifted(e) for e in range(6)])
        counts=convolve(counts,[F(1)]*6)
    epsilon,C,J=map(F,(record['epsilon_exact'],record['C_upper'],record['J_upper']))
    T=F(326059,4)
    records=[]
    for d in [6,7]:
        outside=total-sum(coefficients[:d+1])
        score=epsilon+C+outside+(J-1)/(T-1)
        records.append({'total_degree_max':d,'individual_exponent_max':5,'downset_cardinality_including_one':str(sum(counts[:d+1])),
                        'outside_weight':str(outside),'outside_float':float(outside),
                        'consumer_score_upper':str(score),'consumer_score_float':float(score)})
    outside=F(records[1]['outside_weight'])
    require(outside<F(1,25),'strict degree7 outside bound')
    require(epsilon<F(61,200) and C<F(521,1000) and J<9876,'clean balanced same-law components')
    survival_lower=1-F(61,200)-F(521,1000)-F(1,25)
    gamma_upper=1+F(9875)/survival_lower
    require(survival_lower==F(67,500) and gamma_upper==F(4937567,67)<T,'strict clean conclusion')

    require(len(p)==len(profiles)==20 and p==data['prime_order'] and p[-1]==73,
            'all twenty original odd head primes')
    require(F(records[0]['consumer_score_upper'])>1 and F(records[1]['consumer_score_upper'])<1,
            'degree6 certificate insufficient and degree7 strictly sufficient')
    original_vectors=[]
    for n,a in labels:
        rest=n;vector=[]
        for prime in p:
            exponent=0
            while rest%prime==0:
                rest//=prime;exponent+=1
            vector.append(exponent)
        require(rest==1,'all original factors retained')
        original_vectors.append(vector)
    require(len(labels)==len({n for n,_ in labels})==154 and
            [max(v[i] for v in original_vectors) for i in range(20)]==data['heights'],
            'complete literal154 heights')
    require(max(map(sum,original_vectors))==5 and all(max(v)<=5 and sum(v)<=7 for v in original_vectors),
            'all original head vectors are inside the degree7 region')
    require(len(coefficients)==len(counts)==101 and all(c>=0 for c in coefficients)
            and all(c.denominator==1 for c in counts), 'complete finite polynomial product')
    require(all(io.read_artifact_bytes(base/name)==value for name,value in source_bytes.items()),
            'source inputs unchanged during calculation')
    result=dict(schema='balanced-profile-exponent-frontier-v1',
                scope='Same-law outside-union bound for the verified literal154 profile. Extra distinct73-smooth head moduli are allowed outside e_p<=5 and sum(e_p)<=7; their arbitrary fixed residues and every original exponent are retained. Numerical tails follow the existing continuation. Direct application of the existing cutoff accounting, not unrestricted noncoverage.',
                status='CERTIFIED_STRICT_PASS_FOR_DEGREE7',
                primes=p,records=records,epsilon_upper='61/200',C_upper='521/1000',J_upper='9876',
                diagonal_error_upper='1/25',survival_lower=str(survival_lower),
                Gamma_upper=str(gamma_upper),T_lower=str(T),Gamma_margin=str(T-gamma_upper),
                epsilon_exact=str(epsilon),C_exact_upper=str(C),J_exact_upper=str(J),
                profiles=record['profiles'],original_heights=data['heights'],
                original_label_source='frontier/source-budgets/capped_head_bellman.py',
                original_label_count=len(labels),
                original_labels_sha256=sha256(json.dumps(labels,separators=(',',':')).encode()).hexdigest(),
                original_modulus_exponents=[dict(modulus=n,exponents=v) for (n,a),v in zip(labels,original_vectors)],
                maximum_original_total_degree=max(map(sum,original_vectors)),
                total_infinite_weight=str(total),
                full_product_coefficients=list(map(str,coefficients)),
                full_coefficient_counts=[str(c) for c in counts],
                source_sha256={name:sha256(value).hexdigest() for name,value in source_bytes.items()},
                producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    mode=parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write',action='store_true')
    mode.add_argument('--check',action='store_true')
    args=parser.parse_args()
    io=load_module('balanced_output_io',args.base/'certificate_io.py')
    result=calculate(args.base)
    path=args.base/'certificates/source_norms/source-budgets/balanced_profile_exponent_frontier.json'
    if args.write:
        io.write_certificate_text(path,json.dumps(result,indent=2)+'\n')
    else:
        require(result==json.loads(io.read_artifact_bytes(path),object_pairs_hook=io._unique),
                'exact canonical balanced-profile replay')
    print(json.dumps({key:result[key] for key in ('schema', 'records', 'survival_lower', 'Gamma_upper', 'Gamma_margin')},indent=2))

if __name__=='__main__':
    main()
