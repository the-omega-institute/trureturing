#!/usr/bin/env python3
"""A retuned actual tree mixture with a strict universal 6.126102 ceiling.

The exact ceiling is 7797466329/1272826915. Arbitrary-coefficient APIs
evaluate row profiles, certify global simplex maxima by supergradients,
and construct actual probabilities from the existing full/pair witness
interface. The certified uniform coefficient interval is [3/5,46/73].

Default controls certify both endpoints of a complete finite early-word
case split, check the analytic identities used for every other height,
and reuse an actual witness family refuting a ceiling of six for the
chosen coefficient. Finite words alone do not prove an all-height bound;
that proof is in the accompanying report. No coefficient optimality or
default-target comparison is claimed. Only stdout is written.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse
import copy
import json
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import three_fifths_tree_common_law as previous

common = previous._common
ROWS = previous.ROWS
need = previous.require
LOW, HIGH = F(3, 5), F(46, 73)
PREFIX_DEPTH = 5
EARLY_INTERCEPT = F(211322621, 37209375)
EARLY_SLOPE = F(26817379, 37209375)
ALPHA = F(157821008, 254565383)
LIMIT = F(7797466329, 1272826915)


def coefficient(value):
    need(type(value) in (int, F) and 0 <= value <= 1, 'exact coefficient in [0,1] required')
    return F(value)


def row_cap(depth, beta, alpha):
    common._height(depth)
    alpha = coefficient(alpha)
    need(type(beta) in (int, F) and 0 <= beta <= 1, 'exact row mass in [0,1] required')
    return alpha*min(beta, F(1, 5**depth)) + F(2, 3)*(1-alpha)*(1-beta)/3**depth


def profile_bound(rows, beta, alpha):
    """The complete row-sensitive cap functional for arbitrary exact alpha."""
    weights = previous._weights(rows)
    previous._beta(beta)
    alpha = coefficient(alpha)
    pure = sum((F(2*j+1)*(alpha/5**j+(1-alpha)/3**j) for j in range(len(rows))), F())
    return pure + sum((weights[r][j]*row_cap(j, beta[r], alpha)
                       for r in ROWS for j in range(len(rows))), F())


def certify_profile_maximum(rows, beta, alpha, expected):
    """Check a global simplex optimum by one common supporting slope."""
    weights = previous._weights(rows)
    previous._beta(beta)
    alpha = coefficient(alpha)
    need(type(expected) in (int, F) and profile_bound(rows, beta, alpha) == expected,
         'incorrect claimed profile value')
    slopes = {}
    for r in ROWS:
        b = beta[r]
        penalty = F(2, 3)*(1-alpha)*sum((F(weights[r][j], 3**j) for j in range(len(rows))), F())
        left = alpha*sum(weights[r][j] for j in range(len(rows)) if b <= F(1, 5**j))-penalty
        right = alpha*sum(weights[r][j] for j in range(len(rows)) if b < F(1, 5**j))-penalty
        slopes[r] = {'left': left, 'right': right}
    lower = max(slopes[r]['right'] for r in ROWS if beta[r] < 1)
    upper = min(slopes[r]['left'] for r in ROWS if beta[r] > 0)
    need(lower <= upper, 'no common supergradient: proposed profile is not certified optimal')
    need(all((beta[r] == 1 or slopes[r]['right'] <= lower)
             and (beta[r] == 0 or lower <= slopes[r]['left']) for r in ROWS),
         'simplex boundary supergradient conditions')
    return {'rows': tuple(rows), 'coefficient': alpha, 'beta': dict(beta),
            'maximum': F(expected), 'supporting_slope': lower, 'coordinate_slopes': slopes}


def maximize_profile(rows, alpha):
    """Generate and independently check an exact concave simplex certificate.

Sort the marginal slopes of the four concave piecewise-linear coordinate
functions. Allocate total row mass one along these segments, then use
certify_profile_maximum to verify the resulting global optimum.
"""
    weights = previous._weights(rows)
    alpha = coefficient(alpha)
    breakpoints = sorted({F(0)} | {F(1, 5**j) for j in range(len(rows))})
    segments = []
    base = F()
    beta = {r: F() for r in ROWS}
    for r in ROWS:
        penalty = F(2, 3)*(1-alpha)*sum((F(weights[r][j], 3**j) for j in range(len(rows))), F())
        base += penalty
        for left, right in zip(breakpoints, breakpoints[1:]):
            slope = alpha*sum(weights[r][j] for j in range(len(rows)) if right <= F(1, 5**j))-penalty
            segments.append((slope, r, left, right))
    remaining, value = F(1), base
    for slope, r, left, right in sorted(segments, key=lambda item: (-item[0], item[1], item[2])):
        take = min(remaining, right-left)
        if take:
            need(beta[r] == left, 'marginal segments must preserve coordinate order')
            beta[r] += take
            value += slope*take
            remaining -= take
        if not remaining:
            break
    need(remaining == 0, 'simplex mass allocation incomplete')
    pure = sum((F(2*j+1)*(alpha/5**j+(1-alpha)/3**j) for j in range(len(rows))), F())
    return certify_profile_maximum(rows, beta, alpha, value+pure)


def early_words(depth):
    """All four-row words, modulo renaming, with first change at 1 or 2."""
    common._height(depth)
    need(depth >= 2, 'early-word depth must be at least two')
    words = [(1,)]
    for _ in range(depth):
        words = [word+(r,) for word in words for r in range(1, min(4, max(word)+1)+1)]
    return tuple(word for word in words if word[1] != word[0] or word[2] != word[0])


def early_prefix_certificates(depth, alpha):
    """Return a supergradient certificate for every word in a finite case split."""
    return tuple(maximize_profile(word, alpha) for word in early_words(depth))


def _geometric(z, first):
    return z**first/(1-z)


def _arithmetic(z, first):
    return z**first*(F(first)/(1-z)+z/(1-z)**2)


def nonconstant_tail(depth, alpha):
    """Infinite positive tail after depth, with at least one earlier row change."""
    common._height(depth)
    alpha = coefficient(alpha)
    need(alpha >= F(2, 5), 'tail maximum formula requires coefficient at least 2/5')
    first = depth+1
    full = 8*_arithmetic(F(1, 5), first)+2*_geometric(F(1, 5), first)
    pairs = (6*_arithmetic(F(1, 3), first)+F(5, 3)*_geometric(F(1, 3), first)
             -4*_arithmetic(F(1, 15), first)-F(2, 3)*_geometric(F(1, 15), first))
    return alpha*full+(1-alpha)*pairs


def aligned_profile(height, alpha):
    common._height(height)
    alpha = coefficient(alpha)
    s5 = sum((F(2*j+1, 5**j) for j in range(height+1)), F())
    s3 = sum((F(2*j+1, 3**j) for j in range(height+1)), F())
    return 4*alpha*s5+F(13, 5)*(1-alpha)*s3-F(12, 5)*alpha


def constant_limit(alpha):
    return F(39, 5)-F(27, 10)*coefficient(alpha)


def early_limit(alpha):
    return EARLY_INTERCEPT+EARLY_SLOPE*coefficient(alpha)


def certified_ceiling(alpha):
    """The report's all-height bound, only on its proved coefficient interval."""
    alpha = coefficient(alpha)
    need(LOW <= alpha <= HIGH, 'coefficient outside the proved uniform interval')
    return max(constant_limit(alpha), early_limit(alpha))


def make_law(height, source, alpha=ALPHA, components=None):
    """Construct one actual law at any exact coefficient, before any phases."""
    alpha = coefficient(alpha)
    if components is None:
        components = common.make_common_law(height, source)
    common.verify_common_law(height, source, components)
    nu = common._mixture(((alpha, components['mu']), (1-alpha, components['omega'])))
    return {'height': height, 'coefficient': alpha, 'components': components, 'nu': nu}


def verify_law(height, source, certificate):
    """Reuse actual component validation, then check the retuned law and caps."""
    source = common.validate_source(height, source)
    need(type(certificate) is dict and set(certificate) == {'height', 'coefficient', 'components', 'nu'}
         and type(certificate['height']) is int and certificate['height'] == height, 'retuned certificate schema')
    alpha = coefficient(certificate['coefficient'])
    components = certificate['components']
    common.verify_common_law(height, source, components)
    nu = certificate['nu']
    common._probability(nu, source, 'retuned law')
    need(nu == common._mixture(((alpha, components['mu']), (1-alpha, components['omega']))),
         'retuned law is not the claimed actual mixture')
    checks = []
    for j in range(height+1):
        pure, joint = common._prefixes(nu, j)
        pure_bound = alpha/5**j+(1-alpha)/3**j
        by_row = {r: row_cap(j, components['beta'][r], alpha) for r in ROWS}
        need(max(pure.values()) <= pure_bound and all(v <= by_row[r] for (r, _), v in joint.items()),
             'actual retuned pure/row prefix caps')
        checks.append({'depth': j, 'plain_max': max(pure.values()), 'plain_bound': pure_bound,
                       'row_bounds': by_row})
    result = {'height': height, 'coefficient': alpha, 'source_points': len(source),
              'law_support_points': len(nu), 'prefix_checks': checks,
              'scope': 'one actual probability and its common caps; no finite-target or coefficient-optimality claim'}
    if LOW <= alpha <= HIGH:
        result['strict_uniform_bound'] = certified_ceiling(alpha)
    return result


def analytic_controls():
    endpoints = []
    expected_prefix = {LOW: F(69206569, 11390625), HIGH: F(37571354, 6159375)}
    winner = (1, 2, 2, 2, 2, 2)
    beta = {1: F(4, 5), 2: F(1, 5), 3: F(0), 4: F(0)}
    for alpha in (LOW, HIGH):
        certificates = early_prefix_certificates(PREFIX_DEPTH, alpha)
        need(len(certificates) == 172 and len({c['rows'] for c in certificates}) == 172,
             'complete canonical depth-five early-word split')
        maximum = max(c['maximum'] for c in certificates)
        need(maximum == expected_prefix[alpha] == profile_bound(winner, beta, alpha),
             'endpoint global prefix maximum')
        tail = nonconstant_tail(PREFIX_DEPTH, alpha)
        need(maximum+tail == early_limit(alpha), 'endpoint affine early ceiling')
        endpoints.append({'coefficient': alpha, 'supergradient_certificates': len(certificates),
                          'prefix_maximum': maximum, 'attaining_prefix': winner, 'beta': beta,
                          'infinite_tail': tail, 'early_ceiling': maximum+tail})
    crossing = (F(39, 5)-EARLY_INTERCEPT)/(F(27, 10)+EARLY_SLOPE)
    need(crossing == ALPHA and LOW < ALPHA < HIGH
         and constant_limit(ALPHA) == early_limit(ALPHA) == LIMIT < previous.LIMIT,
         'intersection and strict improvement over report 404')
    # These endpoint inequalities bound all N>=2 analytically, using
    # S_N(1/3)>=23/9 and S_N(1/3)<=3, as proved in the report.
    need(3*HIGH-2*(1-HIGH)*F(23, 9) == 0 and 18*LOW-6 == F(24, 5) > 0,
         'uniform constant-word derivative signs')
    need(1+3*HIGH < LIMIT and 2+F(22, 5)*HIGH < LIMIT,
         'both short constant-word branches')
    # Exact identities at representative parameters supplement the all-height
    # algebra and the previously proved old first-change inequality.
    late_controls = []
    for h, last, alpha in ((3, 3, LOW), (3, 7, ALPHA), (4, 9, HIGH), (8, 12, ALPHA)):
        def caps(j, a):
            f, q = F(1, 5**j), F(1, 3**j)
            return a*f+F(2, 3)*(1-a)*(1-f)*q, row_cap(j, F(1, 5), a)
        def excess(a):
            u, v = caps(h, a)
            result = (6*h+3)*(u-v)-2*h*u
            for j in range(h+1, last+1):
                u, v = caps(j, a)
                result += (6*j+3)*(u-v)-2*u
            return result
        factor = F(5, 3)*(1-alpha)
        correction = (1-factor)*(F(2*h, 5**h)+2*sum((F(1, 5**j) for j in range(h+1, last+1)), F()))
        old = excess(F(2, 5))
        new = excess(alpha)
        need(old <= common.first_change_limit(h) < 0
             and new == factor*old-correction < 0, 'late-first-change affine identity')
        late_controls.append({'first_change': h, 'last_depth': last, 'coefficient': alpha,
                              'old_excess': old, 'new_excess': new})
    return {'endpoint_controls': endpoints, 'coefficient': ALPHA, 'strict_uniform_bound': LIMIT,
            'improvement_over_404': previous.LIMIT-LIMIT, 'gap_above_six': LIMIT-6,
            'late_change_identity_controls': late_controls,
            'scope': 'finite exact endpoint certificates plus analytic all-height case proof in report 426'}


def self_check():
    analytic = analytic_controls()
    actual = previous.sharpness_source(4)
    source = actual['source']
    certificate = make_law(4, source, ALPHA, actual['certificate']['components'])
    audit = verify_law(4, source, certificate)
    phases = actual['audit']['literal_phases']
    value = sum((mass*common._trees.literal_layout_cost(4, phases, p)
                 for p, mass in certificate['nu'].items()), F())
    need(value == aligned_profile(4, ALPHA) == F(961223193283, 159103364375) > 6,
         'actual permitted witnesses refute a ceiling of six for the retuned recipe')
    need(value < LIMIT == constant_limit(ALPHA), 'finite sharpness profile and limiting ceiling')
    # Retain compatibility with the old generic profile at exactly 3/5.
    for word, expected, masses in previous.EARLY_CERTIFICATES:
        rows = tuple(int(d)+1 for d in word)
        beta = dict(zip(ROWS, masses))
        need(profile_bound(rows, beta, LOW) == expected, 'existing profile interface compatibility')
    bad_law = copy.deepcopy(certificate)
    bad_law['nu'][next(iter(bad_law['nu']))] += 1
    nonoptimal = {1: F(1, 5), 2: F(4, 5), 3: F(0), 4: F(0)}
    bad_rows = (1, 2, 2, 2, 2, 2)
    malformed = [
        lambda: coefficient(0.6),
        lambda: coefficient(True),
        lambda: coefficient(F(6, 5)),
        lambda: profile_bound((1, 5), nonoptimal, ALPHA),
        lambda: profile_bound((1,), {1: 1}, ALPHA),
        lambda: early_words(1),
        lambda: certified_ceiling(F(1, 2)),
        lambda: nonconstant_tail(5, F(1, 3)),
        lambda: certify_profile_maximum(bad_rows, nonoptimal, ALPHA,
                                        profile_bound(bad_rows, nonoptimal, ALPHA)),
        lambda: certify_profile_maximum((1,), {1: F(1), 2: F(0), 3: F(0), 4: F(0)}, ALPHA, F(0)),
        lambda: verify_law(4, source, bad_law),
        lambda: make_law(1, {(1, 0)}),
    ]
    for operation in malformed:
        try:
            operation()
        except ValueError:
            continue
        raise ValueError('malformed or nonoptimal input was accepted')
    return {'analytic': analytic,
            'actual_above_six_boundary': {'height': 4, 'source_points': len(source),
                                         'actual_layout_expectation': value, 'gap_above_six': value-6,
                                         'literal_phases': phases,
                                         'strict_uniform_bound': audit['strict_uniform_bound'],
                                         'scope': 'these actual witness choices fail six; no source-minimax obstruction'},
            'malformed_controls': len(malformed)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--stdin', action='store_true', help='read exact height/source and optional coefficient from JSON')
    args = parser.parse_args()
    if args.stdin:
        payload = json.load(sys.stdin)
        need(type(payload) is dict and {'height', 'source'} <= set(payload)
             and set(payload) <= {'height', 'source', 'coefficient'}, 'JSON law fields')
        alpha = common._trees._json_exact(payload['coefficient'], 'coefficient') if 'coefficient' in payload else ALPHA
        certificate = make_law(payload['height'], payload['source'], alpha)
        result = {'certificate': certificate, 'audit': verify_law(payload['height'], payload['source'], certificate)}
    else:
        result = self_check()
    print(json.dumps(common._jsonable(result), indent=2))


if __name__ == '__main__':
    main()
