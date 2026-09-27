#!/usr/bin/env python3
"""Exact stopping boundary for all constant absorbed survival barriers.

Python3.9+ standard library. Default is read-only; --output writes exact JSON.
The result constrains the current full-cell-cost, fixed-numerator comparison
family. It is not a lower bound for actual congruence covering families.
"""
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from pathlib import Path
import argparse
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
CERTIFICATE41 = 'certificates/source_norms/moments-survival/survival_hinge_deficit.json'
CERTIFICATE43 = 'certificates/source_norms/moments-survival/full_absorbed_survival_hinges.json'
PINS = {
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    'verify_joint_frontier.py': '0b5cd35851d36f3af83aee19e02267cb05abc8bf07611a12083fca6f3d9bd765',
    'frontier/comparison-bounds/fixed_cost.py': '2df5ca217aced5823c6c9d88324737091b11318c9625f73503ca7cd35db8c21d',
    'frontier/source-budgets/shared_square_barrier.py': '6bc57d9b93bc583bbced72092f722a4369743013e0dd9eeea0703f01a3bf10a1',
    CERTIFICATE41: '1545539894d8b6390dad78918d2961ef6292935765886b3742aff61a12143af8',
    CERTIFICATE43: 'af6f87829b34fbb4a34eef2a2041f8912953a4b95b3c88571b00864ac27f4030',
}
ROOT = (0, 0, 1, 1, 1)
LAYOUTS = tuple(tuple(1+int(ROOT[l] == r)+int(l == j) for l in range(5))
                for r in range(2) for j in range(5))
CARRIER = (1, 2, 0, 0, 0)
CONTROL = 402


def require(condition, message):
    if not condition:
        raise ValueError(message)


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Duplicate JSON key: '+key)
        result[key] = value
    return result


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable source: '+str(path))
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def pack(terms):
    by_knot = {}
    for c, a in terms:
        by_knot[a] = by_knot.get(a, F(0))+c
    return tuple((c, a) for a, c in sorted(by_knot.items()) if c)


@lru_cache(None)
def cost(threshold, weight):
    """g_star=psi-omega*h_t, as a positive hinge measure with slope1-omega."""
    omega = F(weight, 5)
    pieces = [(F(29, 35)-omega, F(threshold))]
    pieces += [(F(36, 5*7**n), F(threshold, n)) for n in range(2, threshold+1)]
    pieces.append((F(6, 5*7**threshold), F(1)))
    result = pack(pieces)
    require(all(c >= 0 and a >= 1 for c, a in result), 'Positive hinge representation')
    require(sum(c for c, _ in result) == 1-omega, 'Cellwise affine slope from complete7 mass minus omega')
    return result


def value(pieces, v):
    return sum(c*max(F(v)-a, F(0)) for c, a in pieces)


def ceil_fraction(a):
    return -(-a.numerator//a.denominator)


@lru_cache(None)
def ternary_hinge(a, b):
    """Sum_{k>=0} 3^(-k-3) Delta (b+k-a)_+, in one rational formula."""
    if a <= b:
        return F(1, 18)
    distance = a-b
    integer = distance.numerator//distance.denominator
    fractional = distance-integer
    return F(1, 3**(integer+3))*(F(3, 2)-fractional)


def deep(pieces, b):
    return sum(c*ternary_hinge(a, b) for c, a in pieces)


@lru_cache(None)
def positive_centered_mixture(pieces):
    """Q=Sum_{n>=2} p5_n q_n, as a positive hinge measure; bar=Q-f/5."""
    terms = []
    for c, a in pieces:
        cutoff = max(2, ceil_fraction(a))
        terms += [(c*F(4, 5**n), a/n) for n in range(2, cutoff)]
        terms.append((c*F(1, 5**(cutoff-1)), F(1)))
    result = pack(terms)
    require(sum(c for c, _ in result) == sum(c for c, _ in pieces)/5, 'Complete positive5 mass with cellwise slope')
    return result


@lru_cache(None)
def scaled(pieces, n):
    return tuple((n*c, a/n) for c, a in pieces)


@lru_cache(None)
def values(threshold, weight):
    f = cost(threshold, weight)
    Q = positive_centered_mixture(f)
    return (tuple(value(f, b) for b in (1, 2, 3)),
            tuple(value(Q, b) for b in (1, 2, 3)),
            tuple(deep(f, b) for b in (1, 2, 3)),
            tuple(deep(Q, b) for b in (1, 2, 3)))


@lru_cache(None)
def scaled_values(threshold, weight, n):
    f = scaled(cost(threshold, weight), n)
    return tuple(value(f, b) for b in (1, 2, 3)), tuple(deep(f, b) for b in (1, 2, 3))


@lru_cache(None)
def positive_uncentered(threshold, carriers, eta):
    """p_n/n [(n-1) P_eta(f(n .)) + integral f(n)], plus its exact tail."""
    K = threshold
    total = F(0)
    for n in range(2, K):
        table = tuple(scaled_values(threshold, w, n) for w in carriers)
        choices = []
        for b in LAYOUTS:
            initial = sum(eta[l]*table[l][0][b[l]-1] for l in range(5))
            choices += [initial+table[l][1][b[l]-1] for l in range(5)]
        pure = max(choices)
        constant = sum(eta[l]*value(cost(threshold, carriers[l]), n) for l in range(5))
        total += F(4, n*5**n)*((n-1)*pure+constant)
    T0 = F(1, 5**(K-1))
    T1 = T0*(K+F(1, 4))
    slopes = tuple(sum(c for c, _ in cost(threshold, w)) for w in carriers)
    x = sum(eta[l]*slopes[l] for l in range(5))
    first = max(sum(eta[l]*slopes[l]*b[l] for l in range(5)) for b in LAYOUTS)+max(slopes)/18
    intercept = sum(eta[l]*sum(c*a for c, a in cost(threshold, carriers[l])) for l in range(5))
    # f_l(n v)=n*slope_l*v-A_l; exact uncentered n>=K sum.
    total += (T1-T0)*first+T0*(x-intercept)
    return total


def operator(threshold, carriers, dat):
    d, mass, eta, _, _ = dat
    table = tuple(values(threshold, w) for w in carriers)
    choices = []
    for b in LAYOUTS:
        initial = sum((mass[l]-eta[l]/5)*table[l][0][b[l]-1]
                      +eta[l]*table[l][1][b[l]-1] for l in range(5))
        # u_l=(d_l-1/5) f_l+Q_l; its positive hinge measure is convex.
        choices += [initial+(d[l]-F(1, 5))*table[l][2][b[l]-1]
                    +table[l][3][b[l]-1] for l in range(5)]
    return max(choices)+positive_uncentered(threshold, carriers, eta)



def inherited_square_margin(source, fixed, square, dat, G):
    """Reconstruct only control402's100 original square-source layouts."""
    d, n, eta, s, D = dat
    require(CONTROL not in square.SELECTED and square.SOURCE_NORM == G
            and square.BARRIER == 45, 'Control402 uses the unchanged inherited square row')
    pure = tuple(sum(w*x*x for w, x in zip(eta, b))+max(F(x+1, 9) for x in b)
                 for b in LAYOUTS)
    M = max(pure)
    base = tuple(sum((mass+w/4)*x*x for mass, w, x in zip(n, eta, b))
                 +max((a+F(1, 4))*F(x+1, 9) for a, x in zip(d, b)) for b in LAYOUTS)
    global35 = max(base)+F(5, 8)*M
    margins = []
    for bi, b in enumerate(LAYOUTS):
        k = tuple(G-x*x for x in b)
        for ci, c in enumerate(LAYOUTS):
            correction = tuple(F((2*x+1)*y) for x, y in zip(b, c))
            require(min(v-u for v, u in zip(k, correction)) >= 0, 'Original square floors')
            selected = base[bi]+F(9, 20)*pure[ci]+F(7, 40)*M
            selected -= F(4, 25)*square._distance(eta, b, c)
            margin = G*s-F(6, 5)*selected-F(7, 15)*global35
            margin -= fixed._cofactor_cap(dat, k, correction, 6)/5
            require(margin >= 0, 'Exact original retained source margin')
            margins.append(margin)
    require(len(margins) == 100, 'Complete ten-by-ten source layouts at402')
    old = min(margins)
    return old+(F(45)-G)*D, old


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'],
            'Certificate IO source SHA256')
    io = module('absorbed_boundary_io', base/'certificate_io.py')
    for name, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/name)).hexdigest() == pin,
                'Direct source or logical certificate SHA256: '+name)
    source = module('absorbed_boundary_source', base/'verify_joint_frontier.py')
    fixed = module('absorbed_boundary_fixed', base/'frontier/comparison-bounds/fixed_cost.py')
    square = module('absorbed_boundary_square', base/'frontier/source-budgets/shared_square_barrier.py')
    previous = json.loads(io.read_artifact_bytes(base/CERTIFICATE43), object_pairs_hook=unique)
    survival = json.loads(io.read_artifact_bytes(base/CERTIFICATE41), object_pairs_hook=unique)
    require(previous['schema'] == 'erdos7-full-absorbed-survival-hinges-v1'
            and survival['schema'] == 'erdos7-survival-hinge-deficit-v1', 'Published predecessor schemas')
    require(LAYOUTS == source.BASES and ROOT == source.ROOT, 'Same independent five-cell baseline domain')
    parameters = list(source.vertices())
    require(len(parameters) == 1296, 'Published source-parameter inventory')
    dat = source.data(parameters[CONTROL])
    d, n, eta, s, D = dat
    require((d, n, eta, s, D) == ((F(3, 4), F(3, 4), F(1, 4), F(1, 2), F(1, 2)),
        (F(1, 24), F(1, 12), F(1, 72), F(1, 18), F(1, 18)),
        (F(1, 18), F(1, 9), F(1, 9), F(1, 9), F(1, 9)), F(1, 4), F(3, 20)),
        'Exact control402 source data')
    roots = (sum(n[:2]), sum(n[2:]))
    require(roots[0]+n[1] == max(roots)+max(n) and CARRIER == (1, 2, 0, 0, 0),
            'Selected root0/cell1 carries the maximum raw shallow mass')
    full_row = previous['full_absorbed_hinges']['rows'][CONTROL]
    survival_row = survival['survival_hinge']['rows'][CONTROL]
    require(full_row['index'] == survival_row['index'] == CONTROL
            and [CONTROL, 'D'] in previous['maximizer_endpoints']['bound']
            and F(previous['q_effective']) == F(23, 42),
            'Published43 J target is attained at this D endpoint')
    m25 = F(survival_row['margin'])
    m4, m5 = (F(full_row[str(t)]['margin']) for t in (4, 5))
    delta43 = F(23, 42)*D+m25/22+m4/6+F(4, 33)*m5
    require(delta43 > 0 and m25 == F(68963, 441000), 'Inherited same-law survival denominator')
    numerator_J = (F(previous['bound'])-source.WHOLE_CONST)*delta43
    G = F(previous['source_G357'])
    require(G == F(102715, 2916) and F(previous['source_comparison_barrier']) == 45,
            'Fixed source norm and signed square comparison barrier')
    mg, old_mg = inherited_square_margin(source, fixed, square, dat, G)
    finite, tails = source.ap_product_distribution(((11, F(5, 3)), (13, F(12, 7))), 9)
    cG, A81 = F(previous['cG']), F(previous['A81'])
    require(cG == tails[2]+sum(k*k*finite[k] for k in (7, 8)), 'Complete unchanged AP square tail')
    raw81 = sum(prob*k*k*source.square357(F(81, k*k), dat) for k, prob in finite.items() if k < 7)
    numerator_T = A81*D+raw81-cG*mg
    numerator = numerator_J+numerator_T
    require(numerator_J > 0 and numerator_T > 0
            and numerator == F(235676572069506444982211913251473065480803,
                              6360462916399256045941092769236000000000),
            'Fixed combined numerator independently reconstructed from published inputs')
    losses = {}
    for threshold in (4, 5):
        scalar = operator(threshold, (0, 0, 0, 0, 0), dat)
        tag = ('seven_block', (('h', F(threshold)), 0))
        require(scalar == source.zero5_raw(tag, dat) == F(full_row[str(threshold)]['zero5_raw']),
                'Independent hinge-measure scalar reconstruction')
        positive7 = source.raw357(F(threshold), dat)-scalar
        require(positive7 == F(full_row[str(threshold)]['positive7_complement']),
                'Same complete positive7 source complement')
        starred = operator(threshold, CARRIER, dat)
        losses[threshold] = {'positive7': positive7, 'F_star': starred,
                             'constant_loss': positive7+starred}
    upper = F(193, 231)*D+m25/22-losses[4]['constant_loss']/6-F(4, 33)*losses[5]['constant_loss']
    require(upper == F(2025618599, 26741137500) > 0, 'Uniform all-barrier denominator upper bound')
    lower = source.WHOLE_CONST+numerator/upper
    require(lower == F(1208994069650187954348450703035483220540461139,
                       2367081918117057277892487238031745380160000) > 510 > 403,
            'Exact uniform stopping boundary is strictly above403')
    return {'schema': 'erdos7-absorbed-barrier-boundary-v1', 'control': CONTROL,
            'parameter': parameters[CONTROL], 'source_data': dat, 'selected_carrier': [0, 1],
            'm25': m25, 'delta43': delta43, 'source_margin_before45': old_mg,
            'source_margin_inherited45': mg, 'Raw81': raw81,
            'numerator_J': numerator_J, 'numerator_T81': numerator_T, 'numerator_combined': numerator,
            'source_losses': losses, 'denominator_upper_at_D': upper,
            'combined_family_lower_bound': lower, 'gap_above403': lower-403,
            'maximum_gain_over43_from_constant_barriers': F(previous['combined'])-lower,
            'source_layout_checks': 100, 'scalar_reconstruction_checks': 2,
            'input_sha256': PINS,
            'scope': 'For all finite constant C4,C5>=0, the current complete absorbed-margin and fixed-numerator bound expression has supremum at least this value, or its denominator is inadmissible. This is a restriction on the comparison family, not a lower bound on actual congruence families, not a continuous-optimality claim, and not an unrestricted Erdos7 proof.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = calculate(Path(__file__).resolve().parents[2])
    rendered = json.dumps(encode(result), indent=2)+'\n'
    if args.output is not None:
        args.output.write_text(rendered)
    print(rendered, end='')


if __name__ == '__main__':
    main()
