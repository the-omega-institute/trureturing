"""Exact same-source error bounds for finite-prefix later-residue templates.

Consumes the retained five-role source separation, without importing its
producer or recomputing geometric rows, profile weights or price bounds.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse
import hashlib
import json

ROOT = Path(__file__).resolve().parent
INPUT = 'mixed_single_split_source_bound.json'
INPUT_SHA256 = 'f305dd7b42346eb858fa780887146c2b82261d2721c76f417e12682c797a101f'
CAPS = ((7, F(3, 2)), (11, F(5, 3)), (13, F(3, 2)),
        (17, F(2)), (19, F(9, 5)))


def need(ok, message):
    if not ok:
        raise ValueError(message)


def verify(input_dir):
    raw = (Path(input_dir) / INPUT).read_bytes()
    need(hashlib.sha256(raw).hexdigest() == INPUT_SHA256,
         'pinned five-role source-bound result')
    source = json.loads(raw)
    need(tuple((p, F(c)) for p, c in source['physical_caps']) == CAPS,
         'physical caps remain attached to their primes')
    extension = source['late_reference_extension']
    initial_mass = F(extension['initial_source_mass_upper'])
    nonworst = F(extension['direct_nonworst_margin_own_source'])
    need(initial_mass == F(3, 8) and nonworst > 0
         and extension['agreement_depth'] == 4,
         'retained actual-source mass, nonworst separator and common depth')
    source_roles = source['roles']
    need(len(source_roles) == 5
         and [r['split_prime'] for r in source_roles] == [p for p, c in CAPS],
         'all five source roles exactly once in physical order')
    rows = []
    for role in source_roles:
        p = role['split_prime']
        cap = dict(CAPS)[p]
        worst_type_gap = F(role['minimum_margin'])
        separator = min(worst_type_gap, nonworst)
        need(separator == F(role['same_source_separator']),
             'retained worst/nonworst minimum on one source')
        common_error = initial_mass * sum((c / q ** 4 for q, c in CAPS if q != p), F())
        need(common_error == F(role['late_reference_error'])
             and separator - common_error == F(role['late_reference_margin']),
             'retained four-common-prefix comparison')
        ternary_error = F(2, 3 ** 11)
        quinary_error = F(2, 5 ** 7)
        split_error = initial_mass * 2 * cap / p ** 6
        additional_error = ternary_error + quinary_error + split_error
        total_error = common_error + additional_error
        remaining = separator - total_error
        need(remaining > F(1, 20000), 'strict finite-prefix source margin above 1/20000')
        rows.append({
            'split_prime': p,
            'split_prefix_depths': [[3, 11], [5, 7], [p, 6]],
            'common_prefix_depths': [[q, 4] for q, c in CAPS if q != p],
            'worst_type_source_gap': str(worst_type_gap),
            'same_source_separator': str(separator),
            'common_prefix_error': str(common_error),
            'ternary_prefix_error': str(ternary_error),
            'quinary_prefix_error': str(quinary_error),
            'split_prime_prefix_error': str(split_error),
            'additional_error': str(additional_error),
            'total_error': str(total_error),
            'remaining_margin': str(remaining),
            'remaining_margin_decimal': float(remaining),
        })
    worst = min(rows, key=lambda r: F(r['remaining_margin']))
    return {
        'schema': 'finite-prefix-template-source-v1',
        'inputs': {INPUT: INPUT_SHA256},
        'initial_source_mass_upper': str(initial_mass),
        'direct_nonworst_margin_own_source': str(nonworst),
        'physical_caps': [[p, str(c)] for p, c in CAPS],
        'strict_margin_floor': '1/20000',
        'role_count': len(rows),
        'worst_split_prime': worst['split_prime'],
        'minimum_remaining_margin': worst['remaining_margin'],
        'minimum_remaining_margin_decimal': worst['remaining_margin_decimal'],
        'roles': rows,
        'error_formula': '(3/8)*sum(C_q/q^4 for q in {7,11,13,17,19} except p) + 2/3^11 + 2/5^7 + (3/4)*C_p/p^6',
        'template_condition': 'For each complete original later numerical label, one fixed A/B selector simultaneously chooses the prescribed prefixes at 3,5,p, through min(v_q(d),h_q), where h_3=11,h_5=7,h_p=6. At every other q in {7,11,13,17,19}, its residue matches one common prefix through min(v_q(d),4). Exponent zero is vacuous. All deeper old-coordinate digits and both new-coordinate phases may vary arbitrarily by label; original full global reference paths are not required.',
        'scope': 'Exact scalar consequence of the retained same-source separators. The separate mathematical proof supplies one simultaneous per-label CRT repair, indicator equality outside fixed prefix cylinders, full joint (3,5) marginal domination by anchor Haar, and actual physical-prime full-history caps. The family has distinct odd numerical moduli with support in {3,5,7,11,13,17,19,23,29}. No uniform positive whole-fibre Haar density, unrestricted Erdos7, geometric recomputation, optimizer or Lean verification is claimed.',
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input-dir', type=Path, default=ROOT)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(args.input_dir)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    else:
        expected = json.loads(Path(__file__).with_suffix('.json').read_text())
        need(result == expected, 'retained finite-prefix source result mismatch')
    print(json.dumps({k: result[k] for k in (
        'role_count', 'worst_split_prime', 'minimum_remaining_margin',
        'minimum_remaining_margin_decimal', 'strict_margin_floor')}, indent=2))


if __name__ == '__main__':
    main()
