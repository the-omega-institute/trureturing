"""Independent logarithmic-derivative and bounded-composition degree7 verification."""
from fractions import Fraction as F
from hashlib import sha256
from math import comb, prod
from pathlib import Path
import argparse, importlib.util, json, sys
sys.dont_write_bytecode=True
def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate JSON key')
        result[key] = value
    return result


def factor_with_primes(n, primes):
    powers = []
    for p in primes:
        e = 0
        while n % p == 0:
            e += 1
            n //= p
        powers.append(e)
    require(n == 1, 'all original modulus prime factors retained')
    return powers


def product_coefficients_by_log_derivative(polynomials, maximum):
    B = [F(0)]*(maximum + 1)
    local = []
    for a in polynomials:
        require(a[0] == 1, 'unit local constant coefficient')
        b = [F(0)]*(maximum + 1)
        for n in range(1, maximum + 1):
            b[n] = n*(a[n] if n < len(a) else F(0))
            b[n] -= sum((b[j]*a[n-j] for j in range(1, n) if n-j < len(a)), F(0))
            B[n] += b[n]
        local.append(b)
    c = [F(1)]
    for n in range(1, maximum + 1):
        c.append(sum((B[j]*c[n-j] for j in range(1, n + 1)), F(0))/n)
        require(c[n] >= 0, 'nonnegative exact product coefficient')
    return c, local


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


def load_module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    require(spec is not None and spec.loader is not None,'readable module')
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def calculate(base):
    io=load_module('balanced_independent_frontier_io',base/'certificate_io.py')
    source_bytes={name:io.read_artifact_bytes(base/name) for name in ('certificate_io.py', 'problem-details/57-balanced-depth-profile-and-degree-seven-frontier.md', 'frontier/source-budgets/balanced_profile_head_input.json')}
    head=bind_certificate(base,io,source_bytes,'certificates/source_norms/source-budgets/balanced_profile_head_verification.json','frontier/source-budgets/verify_balanced_profile_head.py','balanced-profile-head-verification-v1')
    tail=bind_certificate(base,io,source_bytes,'certificates/source_norms/source-budgets/balanced_profile_tail_verification.json','frontier/source-budgets/verify_balanced_profile_tail_budget.py','balanced-profile-tail-verification-v1')
    candidate=bind_certificate(base,io,source_bytes,'certificates/source_norms/source-budgets/balanced_profile_exponent_frontier.json','frontier/source-budgets/balanced_profile_exponent_frontier.py','balanced-profile-exponent-frontier-v1')
    require(head['profiles']==tail['profiles'] and head['epsilon_exact']==tail['epsilon_exact'],
            'one independently reviewed balanced profile and head mass')
    require(tail['tail_stages']==1879 and tail['independent_T_lower']=='326059/4',
            'full previous continuation and conservative threshold')
    P,H=head['prime_order'],head['heights']
    R=[[F(x) for x in row] for row in head['profiles']]
    require(len(P)==len(H)==len(R)==20 and P[-1]==73,'full original odd-prime coordinates')
    literal=load_module('balanced_frontier_literal',base/'frontier/source-budgets/capped_head_bellman.py')
    labels=literal.counterexample_154_labels()
    vectors=[factor_with_primes(n,P) for n,a in labels]
    require(len(vectors)==len({n for n,a in labels})==154 and
            max(map(sum,vectors))==5 and all(max(e)<=5 and sum(e)<=7 for e in vectors),
            'full literal154 inside degree7 region, extra moduli disjoint')
    total=F(1);polynomials=[]
    for p,h,r in zip(P,H,R):
        require(len(r)==h+1 and r[0]==1 and all(F(1,p**e)<=r[e]<=r[e-1] for e in range(1,h+1)),
                'actual feasible full-height profile')
        total*=sum(r)+r[h]/(p-1)
        polynomials.append([r[e] if e<=h else r[h]/p**(e-h) for e in range(6)])
    coefficients,_=product_coefficients_by_log_derivative(polynomials,7)
    require(list(map(F,candidate['full_product_coefficients'][:8]))==coefficients,'all independent coefficients through degree7')
    epsilon,C,J=map(F,(head['epsilon_exact'],tail['C_upper'],tail['J_upper']))
    T=F(326059,4);records=[]
    require(total==F(tail['exact_head_mean']),'same full infinite geometric head envelope')
    for degree in (6,7):
        outside=total-sum(coefficients[:degree+1])
        score=epsilon+C+outside+(J-1)/(T-1)
        count=sum((-1)**j*comb(20,j)*comb(degree-6*j+20,20) for j in range(degree//6+1))
        row=next(row for row in candidate['records'] if row['total_degree_max']==degree)
        require(F(row['outside_weight'])==outside and F(row['consumer_score_upper'])==score and int(row['downset_cardinality_including_one'])==count,
                'independent exact outside budget, score and bounded-composition count')
        records.append(dict(total_degree_max=degree,individual_exponent_max=5,
                            count_including_zero=count,outside_weight=str(outside),outside_decimal=float(outside),
                            score_upper=str(score),score_decimal=float(score)))
    error=F(records[1]['outside_weight'])
    require(error<F(1,25) and F(records[1]['score_upper'])<1 and records[1]['count_including_zero']==887610,
            'strict degree7 budget and exact region count')
    require(F(records[0]['score_upper'])>1,'degree6 upper certificate insufficient')
    require(epsilon<F(61,200) and C<F(521,1000) and J<9876,'clean same-law component bounds')
    survival=1-F(61,200)-F(521,1000)-F(1,25)
    gamma=1+F(9875)/survival
    require(survival==F(67,500) and gamma==F(4937567,67)<T,'short sufficient surviving mass/moment chain')
    require(all(io.read_artifact_bytes(base/name)==raw for name,raw in source_bytes.items()),'audit sources unchanged')
    return dict(schema='balanced-profile-exponent-frontier-verification-v1',
                scope='Direct same-law exponent-region application for the independently verified balanced literal154 profile and infinite geometric envelope. Numerical tail schedule and T=326059/4 retained. Additional distinct73-smooth head moduli have some exponent>=6 or total degree>=8; arbitrary phases and finite exponents. No change to Chapters54/55/56 and no degree7 optimality or unrestricted covering claim.',
                primes=P,original_heights=H,original_label_count=154,maximum_original_total_degree=5,
                total_infinite_weight=str(total),product_coefficients_through7=list(map(str,coefficients)),
                degree_records=records,epsilon_exact=str(epsilon),C_upper=str(C),J_upper=str(J),T_lower=str(T),
                simple_epsilon_strict_upper='61/200',simple_C_strict_upper='521/1000',
                simple_J_strict_upper='9876',simple_outside_strict_upper='1/25',
                simple_survival_strict_lower=str(survival),simple_Gamma_strict_upper=str(gamma),
                simple_threshold_margin=str(T-gamma),
                source_sha256={name:sha256(raw).hexdigest() for name,raw in source_bytes.items()},
                producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest())

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    mode=parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write',action='store_true')
    mode.add_argument('--check',action='store_true')
    args=parser.parse_args()
    io=load_module('balanced_output_io',args.base/'certificate_io.py')
    result=calculate(args.base)
    path=args.base/'certificates/source_norms/source-budgets/balanced_profile_exponent_frontier_verification.json'
    if args.write:
        io.write_certificate_text(path,json.dumps(result,indent=2)+'\n')
    else:
        require(result==json.loads(io.read_artifact_bytes(path),object_pairs_hook=io._unique),
                'exact canonical balanced-profile replay')
    print(json.dumps({key:result[key] for key in ('schema', 'degree_records', 'simple_survival_strict_lower', 'simple_Gamma_strict_upper', 'simple_threshold_margin')},indent=2))

if __name__=='__main__':
    main()
