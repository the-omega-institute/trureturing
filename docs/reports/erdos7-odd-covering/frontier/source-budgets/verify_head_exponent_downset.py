"""Independent rational log-derivative audit of the exponent downset budget.

The candidate convolution is neither imported nor executed. Coefficients
through degree nine are obtained from local logarithmic derivatives and the
product differential identity. Cardinalities use bounded-composition
inclusion-exclusion. All required checks remain active under Python -O.
"""
from fractions import Fraction as F
from hashlib import sha256
from math import comb, prod
from pathlib import Path
import argparse
import importlib.util
import json
import sys
sys.dont_write_bytecode = True

INPUT = 'frontier/source-budgets/depth_profile_head_input.json'
PROFILE = 'certificates/source_norms/source-budgets/depth_profile_tail_budget.json'
LITERAL = 'frontier/source-budgets/capped_head_bellman.py'
CANDIDATE_PROGRAM = 'frontier/source-budgets/head_exponent_downset.py'
CANDIDATE = 'certificates/source_norms/source-budgets/head_exponent_downset.json'
PROOF = 'problem-details/56-exponent-frontiers-and-cylinder-cover-certificates.md'
CERTIFICATE = 'certificates/source_norms/source-budgets/head_exponent_downset_verification.json'
SOURCES = ('certificate_io.py', INPUT, PROFILE, LITERAL, CANDIDATE_PROGRAM,
           CANDIDATE, PROOF, 'frontier/source-budgets/depth_profile_tail_budget.py',
           'frontier/source-budgets/depth_cap_bellman.py',
           'certificates/source_norms/source-budgets/depth_cap_bellman.json')


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


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'readable canonical source')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def calculate(base):
    io = load_module('independent_downset_io', base/'certificate_io.py')
    source_bytes = {name: io.read_artifact_bytes(base/name) for name in SOURCES}

    def checked_certificate(name, producer, schema):
        record = json.loads(source_bytes[name], object_pairs_hook=io._unique)
        require(record['schema'] == schema, 'certificate schema: ' + name)
        require(record['producer_sha256'] == sha256(source_bytes[producer]).hexdigest(),
                'current certificate producer: ' + name)
        for dependency, digest in record['source_sha256'].items():
            raw = io.read_artifact_bytes(base/dependency)
            require(sha256(raw).hexdigest() == digest, 'fresh certificate source: ' + dependency)
            if dependency in source_bytes:
                require(source_bytes[dependency] == raw, 'unchanged shared source')
            source_bytes[dependency] = raw
        return record

    profile_input = json.loads(source_bytes[INPUT], object_pairs_hook=io._unique)
    require(set(profile_input) == {'schema', 'head_label_source', 'head_label_factory',
                                  'prime_order', 'heights', 'profiles'} and
            profile_input['schema'] == 'depth-profile-head-input-v1', 'canonical profile input')
    require(profile_input['head_label_source'] == LITERAL and
            profile_input['head_label_factory'] == 'counterexample_154_labels', 'unique original label source')
    literal = load_module('independent_downset_literals', base/LITERAL)
    data = dict(prime_order=profile_input['prime_order'], heights=profile_input['heights'],
                labels=literal.counterexample_154_labels())
    head = checked_certificate('certificates/source_norms/source-budgets/depth_cap_bellman.json',
                               'frontier/source-budgets/depth_cap_bellman.py', 'depth-cap-bellman-v1')
    budget = checked_certificate(PROFILE, 'frontier/source-budgets/depth_profile_tail_budget.py',
                                 'depth-profile-tail-budget-v1')
    candidate = checked_certificate(CANDIDATE, CANDIDATE_PROGRAM, 'head-exponent-downset-v1')
    require(head['prime_order'] == data['prime_order'] and head['heights'] == data['heights'] and
            head['profiles'] == profile_input['profiles'] == budget['profiles'],
            'same canonical original coordinate profile throughout')
    require(head['original_label_source'] == LITERAL and head['original_label_count'] == 154 and
            head['original_labels_sha256'] == sha256(json.dumps(data['labels'],separators=(',',':')).encode()).hexdigest(),
            'current original literal head provenance')
    require(head['epsilon_exact'] == budget['epsilon_exact'] and budget['geometric_lift'] and
            budget['B'] == 16384 and budget['tail_stages'] == 1879,
            'same complete infinite-lift continuation budget')
    P, H = data['prime_order'], data['heights']
    profiles = [[F(x) for x in row] for row in budget['profiles']]
    require(len(P) == len(H) == len(profiles) == 20 and P[-1] == 73,
            'complete original twenty-prime head')
    normalized = ''.join(f'{m}:{a}\n' for m, a in data['labels'])
    require(sha256(normalized.encode()).hexdigest() ==
            'ae00ed2c19a8e06b4ccdcdd186a70d85e8f2aafaa1b0043c63e1d3780e877f42',
            'same original literal154 family')
    require(len({m for m, _ in data['labels']}) == len(data['labels']) == 154,
            '154 distinct original numerical moduli')
    original_vectors = [factor_with_primes(m, P) for m, _ in data['labels']]
    require([max(e[i] for e in original_vectors) for i in range(20)] == H,
            'actual full original coordinate heights')
    require(max(sum(e) for e in original_vectors) == 5 and
            all(max(e) <= 5 and sum(e) <= 9 for e in original_vectors),
            'every original vector belongs to both downsets under consideration')
    polynomials = []
    total = F(1)
    rectangle = F(1)
    for p, h, row in zip(P, H, profiles):
        require(len(row) == h + 1 and row[0] == 1, 'full exact profile row')
        require(all(F(1, p**e) <= row[e] <= row[e-1] for e in range(1, h + 1)),
                'feasible monotone coarse cap profile')
        a = [row[e] if e <= h else row[h]/p**(e-h) for e in range(6)]
        polynomials.append(a)
        rectangle *= sum(a)
        total *= sum(row) + row[h]/(p-1)
    coefficients, _ = product_coefficients_by_log_derivative(polynomials, 9)
    require(list(map(F, candidate['full_product_coefficients'][:10])) == coefficients,
            'independent product coefficients through degree9 match candidate')
    epsilon, C, J = (F(budget[key]) for key in ('epsilon_exact', 'C_upper', 'J_upper'))
    require(epsilon == F(850282109320449012581343404003218456990123,
                         2126237451649555718697975632038158000000000), 'previous exact head epsilon')
    require(C == F(467101552960255339,10**18) and J == F(559058126433247751329,62500000000000000),
            'previous exact complete infinite-lift C and J bounds')
    T = F(326059,4)
    require(F(budget['T_lower']) >= T, 'previous certified continuation threshold')
    rows = []
    for degree in (8, 9):
        inside = sum(coefficients[:degree+1])
        outside = total-inside
        cardinality = sum((-1)**j*comb(20,j)*comb(degree-6*j+20,20)
                          for j in range(degree//6+1))
        require(0 <= inside <= rectangle <= total, 'actual nested finite/infinite weight regions')
        score = epsilon+C+outside+(J-1)/(T-1)
        expected = next(row for row in candidate['records'] if row['total_degree_max'] == degree)
        require(expected['individual_exponent_max'] == 5 and
                F(expected['outside_weight']) == outside and
                F(expected['consumer_score_upper']) == score and
                int(expected['downset_cardinality_including_one']) == cardinality,
                'independent exact coefficient and count formula match candidate')
        rows.append(dict(individual_exponent_max=5, total_degree_max=degree,
                         cardinality_including_zero=cardinality,
                         inside_weight=str(inside), outside_weight=str(outside),
                         outside_weight_decimal=float(outside),
                         exact_consumer_score_upper=str(score), score_decimal=float(score)))
    outside9 = F(rows[1]['outside_weight'])
    require(outside9 < F(191,10000) and F(rows[1]['exact_consumer_score_upper']) < 1,
            'strict degree9 consumer certificate')
    require(F(rows[0]['exact_consumer_score_upper']) > 1, 'degree8 bound fails this sufficient criterion')
    require(epsilon < F(2,5) and C < F(47,100) and J < 9000,
            'same-law simple independent component bounds')
    survival = 1-F(2,5)-F(47,100)-F(191,10000)
    gamma = 1+F(8999)/survival
    require(survival == F(1109,10000) and gamma == F(89991109,1109) and
            T-gamma == F(1634995,4436) > 0, 'short exact survival and moment margin')
    require(rows[1]['cardinality_including_zero'] == 9979585, 'degree9 bounded-composition count')
    require(all(io.read_artifact_bytes(base/name) == raw for name,raw in source_bytes.items()),
            'audit sources unchanged')
    return dict(schema='head-exponent-downset-verification-v1',
                scope='Exact independent coefficient/count verification for the same previously reviewed literal154 profile and infinite-lift budget. Outside-weight union accounting is a direct extension of the existing cutoff formula to a finite exponent set. No claim of a new basic theorem, physical spacetime identity, unrestricted noncoverage, or degree9 optimality.',
                primes=P, original_heights=H, original_label_count=154,
                maximum_original_total_degree=5,
                total_infinite_weight=str(total), rectangle_weight=str(rectangle),
                rectangle_outside_weight=str(total-rectangle),
                product_coefficients_through9=list(map(str,coefficients)),
                degree_records=rows, epsilon=str(epsilon), C_upper=str(C), J_upper=str(J), T_lower=str(T),
                simple_outside_strict_upper='191/10000', simple_survival_strict_lower=str(survival),
                simple_Gamma_strict_upper=str(gamma), threshold_margin=str(T-gamma),
                source_sha256={name:sha256(raw).hexdigest() for name,raw in source_bytes.items()},
                producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    io = load_module('independent_downset_output_io', args.base/'certificate_io.py')
    result = calculate(args.base)
    path = args.base/CERTIFICATE
    if args.write:
        io.write_certificate_text(path, json.dumps(result, indent=2)+'\n')
    else:
        require(result == json.loads(io.read_artifact_bytes(path), object_pairs_hook=io._unique),
                'exact independent exponent-downset verification replay')
    print(json.dumps({key:result[key] for key in
                     ('schema','maximum_original_total_degree','degree_records','simple_outside_strict_upper',
                      'simple_survival_strict_lower','simple_Gamma_strict_upper','threshold_margin')},indent=2))


if __name__ == '__main__':
    main()
