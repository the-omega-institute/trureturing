# SPDX-License-Identifier: Apache-2.0
"""Check a low-budget circle naming candidate against a capped-density program.

The grid optimum has an analytic dual certificate. Numerical values are floating
point; this program is not a Lean proof or interval-arithmetic certificate.
"""
import argparse
from fractions import Fraction
import json
import math


PERIOD = 2 * math.pi
BUDGETS = (Fraction(0), Fraction(1, 8), Fraction(1, 4), Fraction(1, 2),
           Fraction(3, 4), Fraction(7, 8), Fraction(99, 100))


def candidate(a):
    if a == 1:
        return 1.0
    return 2 - 4 * a * math.cos(math.pi * a / 2) / (math.pi * (1 - a * a))


def density_program(a, cells):
    """Exact rational mass allocation; floating point objective and ordering."""
    low, high = 1 / (1 + a), 1 / (1 - a)
    weights = [2 - 2 * math.cos(PERIOD * (i + 0.5) / cells) for i in range(cells)]
    density = [low] * cells
    remaining = Fraction(cells) - cells * low
    threshold = 0.0
    for i in sorted(range(cells), key=weights.__getitem__):
        if remaining == 0:
            break
        extra = min(high - low, remaining)
        density[i] += extra
        remaining -= extra
        threshold = weights[i]
    assert remaining == 0
    assert sum(density, Fraction(0)) == cells
    assert all(low <= value <= high for value in density)
    primal = math.fsum(w * float(rho) for w, rho in zip(weights, density)) / cells
    dual = threshold + math.fsum(
        min(float(low) * (w - threshold), float(high) * (w - threshold))
        for w in weights) / cells
    assert abs(primal - dual) <= 2e-12
    return primal, dual, low, high


def triangle_error(a, cells):
    """Actual periodic selector for m=2, sampled independently in input phase."""
    L = a / 2
    initial = math.pi * (1 - a) / 4
    def lift(t):
        return initial + L * min(t, PERIOD - t)
    assert abs(lift(0) - lift(PERIOD)) <= 1e-12
    # The periodic triangular lift is globally L-Lipschitz on the real line;
    # sample intrinsic circle distances, including points across the seam.
    for j in range(64):
        t = PERIOD * j / 64
        for k in range(64):
            u = PERIOD * k / 64
            delta = abs(t - u)
            intrinsic_input = min(delta, PERIOD - delta)
            output = abs(lift(t) - lift(u)) % PERIOD
            intrinsic_output = min(output, PERIOD - output)
            assert intrinsic_output <= L * intrinsic_input + 2e-12
    value = math.fsum(2 - 2 * math.cos(2 * lift(PERIOD * (i + .5) / cells)
                                      - PERIOD * (i + .5) / cells)
                      for i in range(cells)) / cells
    return value


def display(value):
    return format(float(value), '.10f')


def main():
    if not __debug__:
        raise SystemExit('Run without -O: verification assertions are required.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-cells', type=int, choices=(512, 2048, 8192), default=8192)
    args = parser.parse_args()
    rows = []
    for a in BUDGETS:
        exact_candidate = candidate(float(a))
        checks = []
        for cells in (512, 2048, 8192):
            if cells > args.max_cells:
                continue
            primal, dual, low, high = density_program(a, cells)
            actual = triangle_error(float(a), cells)
            # Midpoint surrogate error <= 2*pi/N for ANY mass-one feasible
            # density, since w(phi)=2-2cos(phi) has Lipschitz constant2.
            # This bound compares the density continuum problem to its grid;
            # it does not itself prove the reduction from all circle selectors.
            grid_bound = PERIOD / cells
            assert abs(primal - exact_candidate) <= grid_bound + 2e-12
            # Input-phase quadrature for this explicit competitor only.
            input_bound = (1 + float(a)) * PERIOD / cells
            assert abs(actual - exact_candidate) <= input_bound + 2e-12
            checks.append({'cells': cells, 'density_primal': display(primal),
                           'density_dual': display(dual),
                           'primal_dual_gap': display(abs(primal - dual)),
                           'density_grid_bound': display(grid_bound),
                           'triangle_input_quadrature': display(actual),
                           'triangle_quadrature_bound': display(input_bound),
                           'density_formula_difference': display(abs(primal - exact_candidate)),
                           'triangle_formula_difference': display(abs(actual - exact_candidate))})
        rows.append({'a': str(a), 'L': str(a / 2),
                     'density_low': str(low), 'density_high': str(high),
                     'candidate': display(exact_candidate),
                     'existing_winding_lower_bound': display(2 / (1 + float(a))),
                     'checks': checks})
    output = {'scope': {'cover_degree': 2,
                        'a': '2L', 'budget_domain': '0 <= L < 1/2',
                        'loss': 'normalized uniform mean squared complex chord error',
                        'method': 'capped-density finite program with independent dual, periodic triangle competitor',
                        'verification': 'exact rational mass constraints; floating point objective',
                        'continuum_selector_reduction': 'ordinary mathematical derivation, not Lean verified'},
              'rows': rows,
              'boundary': {'a_zero_candidate': display(candidate(0)),
                           'a_one_continuous_extension': display(candidate(1)),
                           'formal_low_budget_optimality': 'open'}}
    print(json.dumps(output, indent=2))


if __name__ == '__main__':
    main()
