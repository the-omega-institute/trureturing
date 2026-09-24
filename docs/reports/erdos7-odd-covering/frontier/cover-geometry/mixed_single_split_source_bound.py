"""Exact source bounds for one split prime among 7, 11, 13, 17, 19.

The source lower, valid 509 rows and 44 reference orbits are retained inputs.
This consumer recomputes the role-dependent weights, signed residuals and
complete infinite overflow, then deducts the same-source depth-four error.
No optimizer, source geometry or Lean rerun.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from math import prod
from collections import Counter, defaultdict
from functools import lru_cache
import argparse
import hashlib
import json

ROOT = Path(__file__).resolve().parent
PINS = {
    'mixed_split_zero_support_bound_certificate.json': '6d646fc00498e8c2d17258118b9a6c8fa1a5c746ce57a0318f51199ee000000b',
    'mixed_reference_zero_support_closure_certificate.json': 'ee5ba06e033563428b89e00f8498f74673bb62da77761d169f11ddffa9ac3fe8',
    'mixed_reference_zero_support_closure.json': '1d06b6151dcd73b6da63d41f4bc501f83c9438c81aee78fd41e2f52456ef1105',
    'mixed_anchor_prefix_lower.json': 'ce9002548ed3a3d50ebb52a102db6529fb5cf4b9ca297feee808263f07c54b26',
    'mixed_split_common_source_types.json': '1ee511ef8537455375068efd0ae3a6164998d62fc7a039416c6f904da469ceb8',
}
CAPS = ((7, F(3, 2)), (11, F(5, 3)), (13, F(3, 2)),
        (17, F(2)), (19, F(9, 5)))
ROW_KINDS = {'pairs': (2, 1), 'genuine_triples': (3, 2),
             'triangle_cliques': (3, 1), 'quads': (4, 3),
             'zero_pairs': (2, 1), 'zero_triangle_cliques': (3, 1),
             'order': (2, 0)}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def profile_load(s):
    return (prod(max(1, x) for x in s[:3])
            + prod(max(1, -x) for x in s[:3]) - 1) * prod(s[3:])


def profiles():
    result = []

    def extend(s):
        if len(s) == 7:
            result.append(s)
            return
        for f in range(1, 39):
            t = s + (f,)
            if profile_load(t) > 38:
                break
            extend(t)

    signed = list(range(2, 39)) + list(range(-2, -39, -1))
    for a, b, c in product(signed, signed + [0], [0] + signed):
        if profile_load((a, b, c)) <= 38:
            extend((a, b, c))
    need(len(result) == 23408 and len(set(result)) == 23408,
         'complete finite profile domain')
    return result


@lru_cache(None)
def shell(p, depth, reference, allowed, factor):
    if factor > depth:
        return F(p - 1, p ** factor) if reference in allowed else F()
    count = sum((x - reference) % p ** (factor - 1) == 0
                and (x - reference) % p ** factor != 0 for x in allowed)
    return F(count, p ** depth)


def initial_weights(reference, keys):
    a3, b3, a5, b5 = reference
    need(a3 % 3 == 2 and b3 % 3 == 1
         and a5 % 5 and b5 % 5 and a5 % 5 != b5 % 5,
         'declared3/5 first-root split')
    result = {}
    for a, b in keys:
        root = 2 if a > 0 else 1
        xs = tuple(x for x in range(27)
                   if x % 3 == root and x % 9 != 1 and x != 4)
        ys = tuple(y for y in range(25)
                   if y % 5 and y != 1 and not (root == 2 and y % 5 == 2))
        xmass = shell(3, 3, a3 if a > 0 else b3, xs, abs(a))
        if b == 0:
            ymass = F(sum(y % 5 not in (a5 % 5, b5 % 5) for y in ys), 25)
        else:
            ref5 = a5 if b > 0 else b5
            ymass = shell(5, 2, ref5,
                          tuple(y for y in ys if y % 5 == ref5 % 5), abs(b))
        result[a, b] = xmass * ymass
    return result


def load_prices(name, entries, denominator, source_rows, middle_count):
    need(type(denominator) is int and denominator > 0,
         'positive integer price denominator')
    units = [0] * middle_count
    row_price = 0
    seen = set()
    for kind, index, numerator in entries:
        need(kind in ROW_KINDS and type(index) is int
             and 0 <= index < len(source_rows[kind]), 'valid retained row index')
        need(type(numerator) is int and numerator > 0
             and (kind, index) not in seen, 'unique positive rational price')
        seen.add((kind, index))
        indices = source_rows[kind][index][:-1]
        arity, rhs = ROW_KINDS[kind]
        need(len(indices) == arity and len(set(indices)) == arity
             and all(type(i) is int and 0 <= i < middle_count for i in indices),
             'valid retained row shape')
        row_price += rhs * numerator
        for position, i in enumerate(indices):
            units[i] += (-1 if kind == 'order' and position == 1 else 1) * numerator
    return {'name': name, 'row_price': F(row_price, denominator),
            'loads': tuple(F(v, denominator) for v in units),
            'negative_loads': sum(v < 0 for v in units), 'rows': len(seen)}


def verify(input_dir, source_lower=None, certificate=None):
    base = Path(input_dir)
    lower_path = Path(source_lower) if source_lower else base / 'mixed_anchor_prefix_lower.json'
    data = {}
    for name, digest in PINS.items():
        path = lower_path if name == 'mixed_anchor_prefix_lower.json' else base / name
        raw = path.read_bytes()
        need(hashlib.sha256(raw).hexdigest() == digest, 'pinned input: ' + name)
        data[name] = json.loads(raw)
    lower_data = data['mixed_anchor_prefix_lower.json']
    need(lower_data['schema'] == 'mixed-anchor-prefix-lower-v1'
         and lower_data['actual_phase_pairs'] == 561
         and lower_data['stage_primes'] == [p for p, c in CAPS]
         and tuple(map(F, lower_data['conditional_caps'])) == tuple(c for p, c in CAPS),
         'same actual source lower and physical caps')
    lower = F(lower_data['uniform_lower'])
    need(lower > 0, 'positive retained source lower')
    nonworst_margin = F(data['mixed_split_common_source_types.json']
                       ['uniform_nonworst_margin_own_source'])
    need(nonworst_margin > 0, 'positive retained direct same-source nonworst margin')
    reference_data = data['mixed_reference_zero_support_closure.json']
    refs = [{'reference': r['reference'], 'configuration_count': r['configuration_count']}
            for r in reference_data['orbits']]
    need(reference_data['reference_orbits'] == 44 and len(refs) == 44
         and len({tuple(r['reference']) for r in refs}) == 44
         and sum(r['configuration_count'] for r in refs) == 24300,
         'inherited44 actual reference orbits')
    source_rows = data['mixed_split_zero_support_bound_certificate.json']
    need(source_rows['mode'] == 'zero_full7874', 'exact-zero row geometry')
    finite_profiles = profiles()
    middle = [s for s in finite_profiles if profile_load(s) >= 20]
    need(len(middle) == 20076, 'complete middle profile order')
    keys = sorted(set(s[:2] for s in finite_profiles))
    initial = {tuple(r['reference']): initial_weights(tuple(r['reference']), keys)
               for r in refs}
    certificate_path = Path(certificate) if certificate else base / 'mixed_single_split_source_bound_certificate.json'
    raw_certificate = certificate_path.read_bytes()
    new = json.loads(raw_certificate)
    need(new['schema'] == 'mixed-single-split-source-prices-v1'
         and new['source_certificate_sha256'] == PINS['mixed_split_zero_support_bound_certificate.json'],
         'new prices retain the509 geometric rows')
    new_by_name = {r['name']: r for r in new['prices']}
    need(len(new['prices']) == 2 and set(new_by_name) == {'ownsplit11', 'ownsplit19'},
         'exactly two new retained price vectors')
    previous = data['mixed_reference_zero_support_closure_certificate.json']
    need(previous['source_certificate_sha256'] == PINS['mixed_split_zero_support_bound_certificate.json'],
         'inherited516 row identity')
    inherited = [r for r in previous['prices'] if r['name'] == 'reference26']
    need(len(inherited) == 1, 'one inherited reference26 price vector')
    models = [load_prices('ownsplit11', new_by_name['ownsplit11']['rows'],
                          new['denominator'], source_rows, len(middle)),
              load_prices('reference26', inherited[0]['rows'],
                          previous['denominator'], source_rows, len(middle)),
              load_prices('ownsplit19', new_by_name['ownsplit19']['rows'],
                          new['denominator'], source_rows, len(middle))]
    need(models[0]['rows'] + models[2]['rows'] == 18706
         and models[1]['rows'] == 9735, 'two new prices and one inherited price')
    need(F(sum(all(n % m != a for m, a in
                   ((3, 0), (9, 1), (27, 4), (5, 0), (25, 1), (15, 2)))
               for n in range(675)), 675) == F(221, 675), 'literal initial chart mass')
    role_results = []
    all_results = []
    for split_prime, split_cap in CAPS:
        common_caps = tuple((p, c) for p, c in CAPS if p != split_prime)

        def later(s):
            result = (1 - 2 * split_cap / split_prime if s[2] == 0
                      else split_cap * F(split_prime - 1, split_prime ** abs(s[2])))
            for (p, cap), factor in zip(common_caps, s[3:]):
                result *= 1 - cap / p if factor == 1 else cap * F(p - 1, p ** factor)
            return result

        finite_factor = defaultdict(F)
        for s in finite_profiles:
            finite_factor[s[:2]] += later(s)
        middle_factors = tuple(later(s) for s in middle)
        rows = []
        for meta in refs:
            t = initial[tuple(meta['reference'])]
            weights = tuple(t[s[:2]] * c for s, c in zip(middle, middle_factors))
            overflow = F(221, 675) - sum((t[ab] * c for ab, c in finite_factor.items()), F())
            need(overflow >= 0, 'complete infinite role overflow')
            comparisons = []
            for model in models:
                residual = sum((max(w - l, F()) for w, l in zip(weights, model['loads'])), F())
                upper = model['row_price'] + residual + overflow
                comparisons.append({'price': model['name'], 'upper': str(upper),
                                    'positive_signed_residual': str(residual)})
            best = min(comparisons, key=lambda r: F(r['upper']))
            upper = F(best['upper'])
            margin = lower - upper
            need(margin > F(1, 6000), 'strict same-source margin above1/6000')
            row = {**meta, 'price': best['price'], 'upper': str(upper),
                   'margin': str(margin), 'overflow': str(overflow),
                   'comparisons': comparisons}
            rows.append(row)
            all_results.append({'split_prime': split_prime, **row})
        worst = min(rows, key=lambda r: F(r['margin']))
        separator = min(F(worst['margin']), nonworst_margin)
        late_reference_error = F(3, 8) * sum((cap / p ** 4 for p, cap in common_caps), F())
        late_reference_margin = separator - late_reference_error
        need(late_reference_margin > F(1, 10000),
             'strict same-source depth-four residual above 1/10000')
        role_results.append({'split_prime': split_prime,
                             'role_primes': [3, 5, split_prime] + [p for p, c in common_caps],
                             'reference_orbits': 44, 'covered_phase_cases': 44 * 561,
                             'price_counts': dict(Counter(r['price'] for r in rows)),
                             'minimum_margin': worst['margin'],
                             'same_source_separator': str(separator),
                             'late_reference_error': str(late_reference_error),
                             'late_reference_margin': str(late_reference_margin),
                             'worst': worst, 'references': rows})
    minimum = min(all_results, key=lambda r: F(r['margin']))
    late_worst = min(role_results, key=lambda r: F(r['late_reference_margin']))
    return {'inputs': PINS, 'certificate_sha256': hashlib.sha256(raw_certificate).hexdigest(),
            'uniform_source_lower': str(lower), 'physical_caps': [[p, str(c)] for p, c in CAPS],
            'full_profiles': len(finite_profiles), 'middle_profiles': len(middle),
            'reference_orbits': 44, 'reference_prefix_configurations': 24300,
            'single_split_roles': 5, 'role_reference_cases': len(all_results),
            'covered_representative_phase_cases': len(all_results) * 561,
            'price_vectors': [{k: str(v) if isinstance(v, F) else v for k, v in m.items() if k != 'loads'}
                              for m in models],
            'minimum_margin': minimum['margin'], 'strict_margin_floor': '1/6000',
            'late_reference_extension': {
                'agreement_depth': 4,
                'agreement_condition': 'Each original later residue matches one common c_q modulo q^min(4,e_iq) for every q in {7,11,13,17,19} other than the selected split prime; higher digits may vary arbitrarily by label. One fixed A/B selector per complete label controls all three coordinates3,5,p. Exponent zero is vacuous.',
                'initial_source_mass_upper': '3/8',
                'direct_nonworst_margin_own_source': str(nonworst_margin),
                'error_formula': '(3/8) * sum(C_q / q^4 for q != split_prime)',
                'minimum_margin': late_worst['late_reference_margin'],
                'worst_split_prime': late_worst['split_prime'],
                'strict_margin_floor': '1/10000'},
            'minimum': minimum, 'roles': role_results,
            'scope': 'Exact A6 upper comparison for all 44 inherited reference orbits and each single additional split prime 7,11,13,17,19, followed by the same-source depth-four late-reference error comparison. The same-source uniform lower, actual reference transport, geometric row validity, nonworst/deleted-root reductions and late-reference coupling are retained mathematical inputs. The original later residues need only share a common prefix modulo q^min(4,e_iq) at the other four old primes, with arbitrary higher digits per label. One fixed two-reference selector per complete numerical modulus controls the three coordinates3,5,p; comparison references share the other four full coordinates. Physical caps and full infinite overflow retained. No uniform fibre-survival threshold, unrestricted other separation pattern, optimizer or Lean claim.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input-dir', type=Path, default=ROOT)
    parser.add_argument('--source-lower', type=Path)
    parser.add_argument('--certificate', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(args.input_dir, args.source_lower, args.certificate)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    else:
        expected = json.loads(Path(__file__).with_suffix('.json').read_text())
        need(result == expected, 'retained single-split result mismatch')
    print(json.dumps({'single_split_roles': 5, 'role_reference_cases': 220,
                      'minimum_margin': result['minimum_margin'],
                      'minimum_margin_float': float(F(result['minimum_margin'])),
                      'strict_margin_floor': '1/6000',
                      'late_reference_minimum_margin': result['late_reference_extension']['minimum_margin'],
                      'late_reference_minimum_margin_float': float(F(result['late_reference_extension']['minimum_margin'])),
                      'late_reference_strict_margin_floor': '1/10000'}, indent=2))


if __name__ == '__main__':
    main()
