"""Retain the original three-five-event deficit in the actual survival hinge.

The independent test cost is (v-5/2)+ and its fixed signed barrier is 7/2.
All positive-five and ternary exponent tails remain complete. This returns
raw source margins; the consumer must use the same actual survivor mass.
"""
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256

THRESHOLD = F(5, 2)
BARRIER = F(7, 2)
Q = F(193, 231)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def reconstruct(source, linear, rows):
    tag = ('h', THRESHOLD)
    zero = ('seven_block', (tag, 0))
    bases = source.BASES
    psi = lambda v: source.zero5_cost(zero, v)
    values = tuple(source.zero5_cost(tag, v) for v in range(1, 5))
    require(values == (F(0), F(0), F(1, 2), F(3, 2)), 'Original survival-hinge cost')
    increments = tuple(values[j+1]-values[j] for j in range(3))
    require(BARRIER == max(values[j]+3*increments[j] for j in range(3)),
            'Global barrier pays every independent three-event floor')
    degree, a, z, cutoff = source.zero5_cost_metadata(zero)
    require((degree, a, z, cutoff) == (1, F(1), -F(1117, 490), 3)
            and psi(1) == 0 and psi(2) == F(33, 245),
            'Complete zero7 cost and affine tail')
    require(all(psi(v+1)-psi(v) >= source.zero5_cost(tag, v+1)-source.zero5_cost(tag, v)
                for v in range(1, cutoff+1)), 'Source increments pay the original event corrections')
    require(Q == F(919, 924)-BARRIER/22, 'Same actual AP survival coefficients')

    @lru_cache(None)
    def positive(eta):
        x = sum(eta)
        tails = tuple(4*t for t in source.geom(5, cutoff))
        first = tuple(source.affine(F(0), 'id', 1, b, eta, source.ONES) for b in bases)
        raw = {n: tuple(source.zero5_scaled_pure(zero, n, b, eta) for b in bases)
               for n in range(2, cutoff)}
        constant = sum(F(4, 5**n)*psi(n) for n in range(2, cutoff))+a*tails[1]+z*tails[0]
        values = tuple(sum(F(4, 5**n)*(raw[n][ci]-psi(n)*x
                           +(n-2)*(max(raw[n])-psi(n)*x))/n for n in range(2, cutoff))
                       +a*tails[0]*(first[ci]-x)
                       +a*(tails[1]-2*tails[0])*(max(first)-x)+constant*x
                       for ci in range(10))
        rebuilt = sum(F(4*(n-1), 5**n)*(max(raw[n])-psi(n)*x)/n for n in range(2, cutoff))
        rebuilt += a*(tails[1]-tails[0])*(max(first)-x)+constant*x
        require(tails[0] >= 0 and tails[1]-2*tails[0] >= 0
                and rebuilt == source.zero5_positive_with_constant(zero, eta)
                and max(values) <= rebuilt, 'Whole affine tail and retained-layout domination')
        return values

    parameters = list(source.vertices())
    require(len(rows) == len(parameters) == 1296 and len(bases) == 10,
            'Complete source parameter domain and original layout inventory')
    result, changes, digest = [], [], sha256()
    count = 0
    for index, (parameter, row) in enumerate(zip(parameters, rows)):
        dat = source.data(parameter)
        d, n, eta, s, D = dat
        require(row['index'] == index and (row['s'], row['D']) == (s, D),
                'Same actual forbidden-family parameter and source mass')
        common = source.zero7_raw(tag, dat)-source.zero5_raw(zero, dat)
        margins, labels = [], []
        for bi, b in enumerate(bases):
            k = tuple(BARRIER-source.zero5_cost(tag, v) for v in b)
            inc = tuple(source.zero5_cost(tag, v+1)-source.zero5_cost(tag, v) for v in b)
            base = common+sum(n[j]*psi(b[j])+eta[j]*source.zero5_centered_correction(zero, b[j])
                              for j in range(5))
            base += max(source.zero5_common_deep(zero, b[j], d[j]) for j in range(5))
            for ci, c in enumerate(bases):
                correction = tuple(F(v*t) for v, t in zip(inc, c))
                require(all(0 <= v <= t <= kk for v, t, kk in zip(inc, correction, k)),
                        'Independent original 5,15,45 event floor')
                margin = BARRIER*s-base-positive(eta)[ci]-linear.event_cap(dat, k, correction)/5
                require(isinstance(margin, F), 'Survival source margin is an exact rational')
                margins.append(margin)
                labels.append([bi, ci])
                digest.update(f'{index},{bi},{ci}:{margin}\n'.encode())
                count += 1
        margin = min(margins)
        raw = source.raw357(THRESHOLD, dat)
        updated = dict(row)
        updated['survival_hinge_margin'] = margin
        result.append(updated)
        changes.append({'index': index, 'margin': margin, 'previous_raw_bound': raw,
                        'D_numerator': BARRIER*D-margin,
                        'D_numerator_gain': raw-BARRIER*D+margin,
                        'minimizers': [label for label, value in zip(labels, margins) if value == margin]})
    require(count == 129600, 'Complete 1296 by 10 by 10 independent source comparisons')
    return result, {'threshold': THRESHOLD, 'barrier': BARRIER, 'survival_coefficient': Q,
                    'margin_checks': count, 'margin_sha256': digest.hexdigest(), 'rows': changes,
                    'scope': 'Raw signed survival-hinge margins with independent original labels and complete exponent tails. No pointwise substitution of D for the actual mass S; final signed target checks are required.'}
