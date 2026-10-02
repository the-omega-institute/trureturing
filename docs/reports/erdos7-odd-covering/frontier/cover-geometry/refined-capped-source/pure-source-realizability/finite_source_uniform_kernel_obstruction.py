"""Exact E=4 uniform transport of the Report824 C-only comparison bound.

Reconstructs one finite pure source and its complete depth inventories.
Consumes Report824's already verified dual/result; does not solve or replay
that dual, search depths, sample kernels, scan source domains, or import repo code.
"""
import argparse
from fractions import Fraction as F
import hashlib
import itertools
import json
from math import gcd, prod
from pathlib import Path

Q = (5, 7, 11, 13, 17, 19, 23)
SELECTED = (15, 21, 45, 33, 35, 39, 63, 51, 57, 55, 105, 75,
            69, 65, 99, 77, 85, 117, 95, 165, 91, 147, 225)
SCHEMA = 'e7-finite-source-uniform-kernel-obstruction-v1'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def exponent(n, p):
    e = 0
    while n % p == 0:
        n //= p
        e += 1
    return e


def a4(q):
    t = F(1, q - 1)
    return 15*t + 50*t*t + 60*t**3 + 24*t**4


def compute(cert, dual, prior, dual_sha, prior_sha):
    checks = 0

    def require(condition, message):
        nonlocal checks
        checks += 1
        if not condition:
            raise ValueError(message)

    require(cert['schema'] == SCHEMA, 'schema')
    require(cert['depth'] == 4 and cert['hinge_threshold'] == 16,
            'only the preregistered depth4 and h16 interface')
    require(tuple(cert['prime_order']) == Q, 'seven-prime coordinate order')
    require(tuple(cert['selected_labels']) == SELECTED, 'same23 numerical slots')
    require(cert['normalization'] == 'mu=nu_u restricted to U / nu_u(U)',
            'actual retained-survivor normalization')
    require(dual_sha == cert['upstream']['dual_sha256'] == prior['dual_sha256'],
            'same previously verified824 dual bytes')
    require(prior_sha == cert['upstream']['result_sha256'], 'same824 result bytes')
    cpoint = prior['phase31']
    require(dual['phase45'] == cpoint['phase45'] == 31, 'same actual31 phase')
    require(dual['semantic_matrix_sha256'] == cpoint['semantic_matrix_sha256']
            == cert['upstream']['semantic_matrix_sha256'], 'same824 semantic source model')
    require(F(dual['epsilon_upper']) == F(cpoint['epsilon_upper']), 'exact824 bound handoff')
    require([F(row['y']) for row in cpoint['joint_rows']] == [0, 0, 1],
            'the consumed bound is C-only')
    require(cpoint['nonzero_source_points'] == [2], 'no A or B source rows in the bound')
    require(F(cpoint['epsilon_residual']) == 0 and F(cpoint['epsilon_box_correction']) == 0,
            'unbounded-epsilon residual absent')
    c_upper = F(cpoint['epsilon_upper'])
    require(c_upper < F(cpoint['strict_upper']) == -F(9, 50), '824 strict rational upper')

    family = [tuple(row) for row in cert['actual_base_family']]
    actual = dict(family)
    require(len(family) == len(actual) == 25 and set(actual) == {3, 9, *SELECTED},
            'same25 actual originals')
    for m, a in family:
        require(type(m) is int and type(a) is int and m > 1 and m % 2 == 1
                and 0 <= a < m, 'legal actual original')
        if m in (3, 9, 45):
            require(a == {3: 0, 9: 1, 45: 31}[m], 'literal anchors and free45phase')
        else:
            h = exponent(m, 3)
            require(h in (0, 1, 2) and a % (m // 3**h) == 0, 'fixed nonternary phase')
            if h:
                require(a % 3**h == (1 if h == 1 else 4), 'fixed ternary phase')

    cap = {q: F(q - 1, q*(q - 2)) for q in Q}
    C = {q: F(q - 1, q - 2) for q in Q}
    pure, local, tv, gamma = [], {}, {}, {}
    for i, q in enumerate(Q):
        first, root = (2, 3) if q == 5 else (1, 2)
        originals = [(q, first)] + [(q**j, root + q**(j-1)) for j in range(2, 5)]
        require(originals == [tuple(row) for row in cert['pure_families'][str(q)]],
                'one literal finite comb per prime')
        for j, (m, a) in enumerate(originals):
            require(0 <= a < m and m % 2 == 1, 'legal pure original')
            for n, b in originals[j+1:]:
                require((a-b) % gcd(m, n) != 0, 'comb cylinders pairwise disjoint')
        survivor = 1 - sum((F(1, m) for m, _ in originals), F(0))
        require(survivor == (F(q-2)+F(1, q**4))/(q-1), 'finite pure survivor mass')
        a = F(1, q)/survivor
        target = [cap[q], cap[q], 1-2*cap[q]] if q == 5 else [cap[q], 1-cap[q]]
        pi = [a, a, 1-2*a] if q == 5 else [a, 1-a]
        require(target == [F(x) for x in cert['corner_C'][i]], 'same C source law')
        for probability in pi + target:
            require(probability > C[q]/q**2, 'every colour live above second-depth cap')
        require(pi[-1] >= cap[q], 'other-colour shallow clipping stays on cap branch')
        require(a < cap[q], 'protected singleton shallow clipping is its actual mass')
        ratios = [min(cap[q], x)/cap[q] for x in pi]
        require(all(min(cap[q], x)/cap[q] == 1 for x in target), 'all C shallow ratios equal one')
        tv[q] = sum((abs(x-y) for x, y in zip(pi, target)), F(0))/2
        gamma[q] = max(1-ratio for ratio in ratios)
        require(gamma[q] == F(1, q**4*(q-2)+1), 'exact shallow-ratio error')
        require(tv[q] == (2 if q == 5 else 1)*cap[q]*gamma[q], 'exact categorical TV')
        local[str(q)] = {'originals': originals, 'survivor_mass': str(survivor),
                         'pi_E4': list(map(str, pi)), 'pi_C': list(map(str, target)),
                         'shallow_ratios': list(map(str, ratios)),
                         'TV': str(tv[q]), 'gamma': str(gamma[q])}
        pure.extend(originals)

    actual_family = family + pure
    require(len(actual_family) == len({m for m, _ in actual_family}) == 53,
            '53 globally distinct odd nonunit originals from one actual family')
    require(all(4 % m != a for m, a in actual_family), 'integer4 survives the finite fixture')
    selected_by_type = {}
    for m in SELECTED:
        h = exponent(m, 3)
        n = m // 3**h
        ds = tuple(0 if n % q else (1 if exponent(n, q) == 1 else 2) for q in Q)
        require(n == prod(q**exponent(n, q) for q in Q), 'complete selected prime support')
        coefficient = prod((C[q] for q, t in zip(Q, ds) if t), start=F(1))/n
        key = (ds, h)
        selected_by_type[key] = selected_by_type.get(key, F(0)) + coefficient

    T29, T1600 = F(cert['T29']), F(cert['T1600'])
    require(T29 == F(120361, 74088), 'once-only inherited29 factor')
    require(T1600 == F(4301685063112470380207, 10**30), 'same complete804 tail')
    multiplier = 27*T29*T1600
    blocks = {(d, h): {'B': F(0), 'W': F(0), 'loss': F(0), 'debit': F(0)}
              for d in range(128) for h in range(3)}
    type_count = 0
    for ds in itertools.product(range(3), repeat=7):
        mask = sum(1 << i for i, t in enumerate(ds) if t)
        size = sum(t != 0 for t in ds)
        B = prod((cap[q] if t == 1 else C[q]/(q*(q-1))
                  for q, t in zip(Q, ds) if t), start=F(1))
        W = prod((15*cap[q] if t == 1 else C[q]*(a4(q)-F(15, q))
                  for q, t in zip(Q, ds) if t), start=F(1))
        require(B > 0 and W > 0, 'complete positive shallow/deep inventory')
        for h in range(3):
            allowed = (h == 0 and size >= 2) or (h in (1, 2) and size >= 1)
            residual = (B if allowed else F(0)) - selected_by_type.get((ds, h), F(0))
            require(residual >= 0, 'selected labels subtracted from their own complete type')
            loss = residual + (B/2 if h == 2 else F(0))
            debit = 12*loss + multiplier*W*(1, 15, 216)[h]
            block = blocks[(mask, h)]
            for key, value in [('B', B), ('W', W), ('loss', loss), ('debit', debit)]:
                block[key] += value
            type_count += 1
    require(type_count == 6561, 'all3^7 depth types and three ternary heights')

    debit_error = F(0)
    block_results = []
    for (mask, h), row in sorted(blocks.items()):
        support = [q for i, q in enumerate(Q) if mask & (1 << i)]
        beta = prod((F(1, q-2) for q in support), start=F(1))
        W = prod((C[q]*a4(q) for q in support), start=F(1))
        selected_cost = sum((prod((C[q] for q in support), start=F(1))/(m//3**h)
                             for m in SELECTED if exponent(m, 3) == h
                             and [q for q in Q if (m//3**h) % q == 0] == support), F(0))
        allowed = (h == 0 and len(support) >= 2) or (h in (1, 2) and bool(support))
        loss = (beta if allowed else F(0)) - selected_cost + (beta/2 if h == 2 else F(0))
        debit = 12*loss + multiplier*W*(1, 15, 216)[h]
        require(row == {'B': beta, 'W': W, 'loss': loss, 'debit': debit},
                'complete types aggregate exactly to384 C blocks')
        bD = sum((tv[q] for q in Q if q not in support), F(0)) + sum((gamma[q] for q in support), F(0))
        debit_error += debit*bD
        block_results.append({'D': mask, 'h': h, 'debit': str(debit), 'uniform_error': str(bD)})
    mass_error = 12*sum(tv.values(), F(0))
    delta = mass_error + debit_error
    require(delta == F(cert['expected_Delta4']), 'exact single-depth uniform error')
    require(delta < F(cert['strict_error_upper']) == F(1, 50), 'strict rational error bound')
    upper = c_upper + delta
    require(upper < F(cert['strict_finite_gate_upper']) == -F(4, 25),
            'all-kernel finite-source strict negative gate')
    return {'schema': SCHEMA, 'checks': checks,
            'normalization': cert['normalization'], 'depth': 4, 'hinge_threshold': 16,
            'upstream_dual_sha256': dual_sha, 'upstream_result_sha256': prior_sha,
            'semantic_matrix_sha256': cpoint['semantic_matrix_sha256'],
            'actual_family': actual_family, 'original_count': 53, 'finite_survivor': 4,
            'local_laws': local, 'full_type_count': type_count, 'aggregate_block_count': 384,
            'TV_sum': str(sum(tv.values(), F(0))), 'mass_error': str(mass_error),
            'debit_error': str(debit_error), 'Delta4': str(delta), 'Delta4_decimal': float(delta),
            'strict_error_upper': '1/50', 'C_gate_upper': str(c_upper),
            'finite_gate_upper': str(upper), 'finite_gate_upper_decimal': float(upper),
            'strict_finite_gate_upper': '-4/25', 'blocks': block_results,
            'scope': 'One53-original finite source; uniform over every legal source-adaptive w,u in the same first-colour/leaf interface. Only h16, inherited complete head caps, full-lambda hinge, capacity-aware retainednu fourth moment and804 tail. No actual covering or unrestricted impossibility claim.'}


def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path, default=here/'finite_source_uniform_kernel_obstruction_certificate.json')
    parser.add_argument('--result', type=Path, default=here/'finite_source_uniform_kernel_obstruction.json')
    parser.add_argument('--upstream-dual', type=Path, default=here/'free45_phase31_dual_certificate.json')
    parser.add_argument('--upstream-result', type=Path, default=here/'free45_live_cell_and_comparison_obstruction.json')
    parser.add_argument('--write-result', action='store_true')
    args = parser.parse_args()
    cert = json.loads(args.certificate.read_text())
    dual, prior = (json.loads(p.read_text()) for p in (args.upstream_dual, args.upstream_result))
    result = compute(cert, dual, prior, digest(args.upstream_dual), digest(args.upstream_result))
    if args.write_result:
        args.result.write_text(json.dumps(result, indent=2)+'\n')
    elif json.loads(args.result.read_text()) != json.loads(json.dumps(result)):
        raise ValueError('saved result differs from exact reconstruction')
    print(json.dumps({key: result[key] for key in ('checks', 'original_count', 'Delta4',
                       'Delta4_decimal', 'finite_gate_upper_decimal', 'strict_finite_gate_upper')}))


if __name__ == '__main__':
    main()
