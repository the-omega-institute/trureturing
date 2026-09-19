#!/usr/bin/env python3
"""Exact support-vector witness for the inherited cellwise-barrier model.

Read-only by default; --output writes exact rational results. Reconstructs
profile44's complete source and numerator at control402. The all-vector
statement is proved in profile44, not inferred by sampling barrier values.
"""
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import argparse
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
PIN = 'a313d75be472e198c130084a2486da859cad086eb84f9f869c429236df1d89cc'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    base = Path(__file__).resolve().parents[1]
    path = base/'frontier/absorbed_barrier_boundary.py'
    require(sha256(path.read_bytes()).hexdigest() == PIN, 'Inherited source checker pin')
    spec = importlib.util.spec_from_file_location('cellwise_boundary_source', path)
    inherited = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(inherited)
    old = inherited.calculate(base)
    d, n, eta, s, D = old['source_data']
    omega = (F(1, 5), F(2, 5), F(0), F(0), F(0))
    # One point of each simplex summand of the complete cap support set.
    pieces = (
        tuple(v/20 for v in eta),
        tuple(eta[l]/20 if l >= 2 else F(0) for l in range(5)),
        tuple(eta[l]/20 if l == 1 else F(0) for l in range(5)),
        tuple(d[l]/90 if l == 0 else F(0) for l in range(5)),
        tuple(F(1, 360) if l == 1 else F(0) for l in range(5)),
    )
    remainder = tuple(sum(v[l] for v in pieces) for l in range(5))
    require(remainder == (F(1, 90), F(1, 72), F(1, 90), F(1, 90), F(1, 90)),
            'Exact point of the weighted-cap support set')
    mass = tuple((1-omega[l])*n[l]-remainder[l] for l in range(5))
    require(mass == (F(1, 45), F(13, 360), F(1, 360), F(2, 45), F(2, 45)),
            'Explicit surviving-cell vector')
    require(all(0 < mass[l] <= n[l] for l in range(5)) and sum(mass) == D == F(3, 20),
            'All cell boxes and the relaxed lower mass endpoint')
    complete_cap = max(d)/90+(sum(eta)+max(sum(eta[:2]), sum(eta[2:]))+max(eta))/20+F(1, 360)
    require(sum(remainder) == complete_cap == F(7, 120), 'Complete unweighted remainder attained')
    require(tuple(n[l]-mass[l] for l in range(5)) ==
            tuple(n[l]*omega[l]+remainder[l] for l in range(5)),
            'Identity cancels every vector barrier coefficient')
    upper = F(193, 231)*sum(mass)+old['m25']/22
    upper -= old['source_losses'][4]['constant_loss']/6+F(4, 33)*old['source_losses'][5]['constant_loss']
    require(upper == old['denominator_upper_at_D'], 'Same all-vector denominator ceiling')
    # The independently proved actual-source cut excludes this relaxed witness.
    actual_mass_lower = D+F(1, 225)
    require(actual_mass_lower == F(139, 900) > sum(mass), 'Actual source cut excludes the witness')
    result = {
        'schema': 'erdos7-cellwise-barrier-boundary-v1',
        'support_pieces': pieces, 'remainder_vector': remainder, 'survivor_vector': mass,
        'survivor_total': sum(mass), 'denominator_upper': upper,
        'combined_family_lower_bound': old['combined_family_lower_bound'],
        'actual_mass_lower_at_source_limit': actual_mass_lower,
        'input_sha256': {'frontier/absorbed_barrier_boundary.py': PIN},
        'scope': 'Inherited weighted cylinder-cap relaxation, fixed profile43 numerator and m25. Arbitrary finite nonnegative five-cell barriers and common shallow carriers. No actual-family lower bound; profile48 excludes this relaxed mass witness.'}
    rendered = json.dumps(inherited.encode(result), indent=2)+'\n'
    if args.output is not None:
        args.output.write_text(rendered)
    print('PASS: exact weighted-cap support witness, all barrier-coefficient identities and complete inherited source constants.')
    print('The comparison boundary is510.75294876651606...; it does not bind stronger actual-source or conditional-numerator models.')


if __name__ == '__main__':
    main()
