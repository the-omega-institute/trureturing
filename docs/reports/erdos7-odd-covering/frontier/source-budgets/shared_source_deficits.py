"""Retain complete source-norm deficits on the same forbidden-family data.

Each original test has its own baseline minimum. Only the five source
parameter groups and actual survivor mass are shared. This evaluates the
ordinary signed inequalities, not a claim of actual-family attainment.
"""
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256

G = F(102715, 2916)
QD = F(919, 924)
CAPS = ((11, F(5, 3)), (13, F(12, 7)))
PAIRS = ((0, 0), (0, 1), (0, 2), (1, 0), (2, 0))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(key): encode(item) for key, item in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(item) for item in value]
    return value


def _distance(eta, b, c):
    delta = tuple(x-y for x, y in zip(b, c))
    return sum(w*v*v for w, v in zip(eta, delta)) - (
        max((0,)+delta)**2+max((0,)+tuple(-v for v in delta))**2)/F(18)


def aggregate(source, fixed, layout, ap, parent, previous, quadratic_inputs,
              ap_inputs, progress=None):
    specs, groups, quadratic = ap.inventory(source, fixed, ap_inputs)
    bases = source.BASES
    require(len(specs) == 46 and len(bases) == 10, 'Complete independent test inventories')
    require(F(previous['source_G357']) == G, 'Same actual source constant')
    require(quadratic_inputs['schema'] == 'erdos7-retained-quadratic-input-v1', 'Quadratic input schema')
    given = quadratic_inputs['constants']
    require([tuple(row['tuple']) for row in given] == list(PAIRS), 'Five quadratic tuple identities')
    constants = tuple(F(row['constant']) for row in given)
    require(constants == tuple(F(row['C']) for row in previous['norms']), 'Predecessor quadratic constants')
    psis = tuple(ap.psi_record(source, layout, pair) for pair in PAIRS)
    weights = {'R17': F(1), 'R19': source.P17, 'R5': source.EXTRA5}
    tail_weight = sum(weights[group['name']]*group['tail_coefficient'] for group in groups)
    linear_weights = tuple(weights[spec['name']] for spec in specs[:40])+(tail_weight,)
    require(len(linear_weights) == 41 and min(linear_weights) > 0, 'Complete positive linear weights')
    outside = quadratic['outside_active_first_moment']
    require(outside == F(parent['quadratic_cost']['outside_active_first_moment']) >= 0,
            'Complete quadratic tuple complement')
    require(F(previous['H16']) == quadratic['expectation']+sum(constants)+outside*(G-1),
            'Same full quadratic normalization')

    @lru_cache(None)
    def positive(ci, eta):
        zero, psi, _, _, _ = psis[ci]
        degree, a, z, cutoff = source.zero5_cost_metadata(zero)
        require(degree == 2 and cutoff >= 2, 'Complete quadratic tail entry')
        x = sum(eta)
        tails = tuple(4*t for t in source.geom(5, cutoff))
        squares = tuple(source.sq_value(F(0), b, eta, source.ONES) for b in bases)
        raw = {n: tuple(source.zero5_scaled_pure(zero, n, b, eta) for b in bases)
               for n in range(2, cutoff)}
        constant = sum(F(4, 5**n)*psi(n) for n in range(2, cutoff))+a*tails[2]+z*tails[0]
        result = tuple(sum(F(4, 5**n)*(raw[n][li]-psi(n)*x
                       +(n-2)*(max(raw[n])-psi(n)*x))/n for n in range(2, cutoff))
                       +a*tails[1]*(squares[li]-x)
                       +a*(tails[2]-2*tails[1])*(max(squares)-x)+constant*x for li in range(10))
        old = source.zero5_positive_with_constant(zero, eta)
        rebuilt = sum(F(4*(n-1), 5**n)*(max(raw[n])-psi(n)*x)/n for n in range(2, cutoff))
        rebuilt += a*(tails[2]-tails[1])*(max(squares)-x)+constant*x
        require(rebuilt == old and max(result) <= old, 'Whole positive tail and retained-source domination')
        return result

    digests = {'source': sha256(), 'quadratic': [sha256() for _ in range(5)], 'linear': sha256()}
    counts = {'source': 0, 'quadratic': 0, 'linear': 0}
    rows = []
    parameters = list(source.vertices())
    require(len(parameters) == 1296, 'Complete five-group continuous-domain vertices')
    for index, parameter in enumerate(parameters):
        dat = source.data(parameter)
        d, n, eta, s, D = dat
        require(min(d) >= F(1, 4) and min(n) >= 0 and 0 < D <= s, 'Source density and mass domain')
        pure = tuple(sum(w*x*x for w, x in zip(eta, b))+max(F(x+1, 9) for x in b) for b in bases)
        M = max(pure)
        base = tuple(sum((mass+w/4)*x*x for mass, w, x in zip(n, eta, b))
                     +max((a+F(1, 4))*F(x+1, 9) for a, x in zip(d, b)) for b in bases)
        global35 = max(base)+F(5, 8)*M
        source_margins = []
        for bi, b in enumerate(bases):
            k = tuple(G-x*x for x in b)
            for ci, c in enumerate(bases):
                correction = tuple(F((2*x+1)*y) for x, y in zip(b, c))
                require(min(v-u for v, u in zip(k, correction)) >= 0, 'Square floor')
                selected = base[bi]+F(9, 20)*pure[ci]+F(7, 40)*M-F(4, 25)*_distance(eta, b, c)
                margin = G*s-F(6, 5)*selected-F(7, 15)*global35-fixed._cofactor_cap(dat, k, correction, 6)/5
                require(isinstance(margin, F) and margin >= 0, 'Exact complete retained source margin')
                source_margins.append(margin)
                digests['source'].update(f'{index},{bi},{ci}:{margin}\n'.encode())
                counts['source'] += 1
        mg = min(source_margins)
        quadratic_margins = []
        for ci, (C, spec, psi_record) in enumerate(zip(constants, specs[41:], psis)):
            zero, psi, curve, _, _ = psi_record
            tag = spec['tag']
            common = source.zero7_raw(tag, dat)-source.zero5_raw(zero, dat)
            margins = []
            for bi, b in enumerate(bases):
                fb = tuple(source.zero5_cost(tag, v) for v in b)
                inc = tuple(source.zero5_cost(tag, v+1)-source.zero5_cost(tag, v) for v in b)
                k = tuple(C-v for v in fb)
                baseline = sum(n[j]*psi(b[j])+eta[j]*source.zero5_centered_correction(zero, b[j])
                               for j in range(5))
                baseline += max(source.zero5_common_deep(zero, b[j], d[j]) for j in range(5))
                for li, c in enumerate(bases):
                    correction = tuple(v*t for v, t in zip(inc, c))
                    require(min(v-u for v, u in zip(k, correction)) >= 0, 'Quadratic floor')
                    selected = common+baseline+positive(ci, eta)[li]-F(4, 25)*curve*_distance(eta, b, c)
                    margin = C*s-selected-fixed._cofactor_cap(dat, k, correction, 6)/5
                    require(isinstance(margin, F) and margin >= 0, 'Exact complete retained quadratic margin')
                    margins.append(margin)
                    digests['quadratic'][ci].update(f'{index},{bi},{li}:{margin}\n'.encode())
                    counts['quadratic'] += 1
            quadratic_margins.append(min(margins))
        linear_margins = []
        for ci, spec in enumerate(specs[:41]):
            tag, zero, C = spec['tag'], spec['zero'], spec['joint']
            common = source.zero7_raw(tag, dat)-source.zero5_raw(zero, dat)
            common += source.zero5_positive_with_constant(zero, eta)
            margins = []
            for bi, item in enumerate(spec['layouts']):
                b = item['baseline']
                k, inc = item['joint']
                selected = common+sum(n[j]*item['psi'][j]+eta[j]*item['correction'][j] for j in range(5))
                selected += max(source.zero5_common_deep(zero, b[j], d[j]) for j in range(5))
                margin = C*s-selected-fixed._cofactor_cap(dat, k, inc, 5)/5
                require(isinstance(margin, F) and margin >= 0, 'Exact complete original linear margin')
                margins.append(margin)
                digests['linear'].update(f'{index},{ci},{bi}:{margin}\n'.encode())
                counts['linear'] += 1
            linear_margins.append(min(margins))
        delta = QD*D-source.raw357(F(4), dat)/6-F(4, 33)*source.raw357(F(5), dat)
        delta -= source.raw357(F(5, 2), dat)/22
        require(delta > 0, 'Actual AP survival lower mass')
        rows.append({'index': index, 's': s, 'D': D, 'Delta': delta, 'source_margin': mg,
                     'quadratic_margins': quadratic_margins,
                     'Mquad': sum(quadratic_margins)+outside*mg,
                     'M41': sum(w*m for w, m in zip(linear_weights, linear_margins))})
        if progress is not None:
            progress(index+1, len(parameters))
    require(counts == {'source': 129600, 'quadratic': 648000, 'linear': 531360}, 'All source-direction domains')
    quad_digests = [value.hexdigest() for value in digests['quadratic']]
    require(quad_digests == [row['margin_sha256'] for row in previous['norms']],
            'Every quadratic margin matches the published predecessor')
    return rows, {'margin_checks': counts, 'source_margin_sha256': digests['source'].hexdigest(),
                  'quadratic_margin_sha256': quad_digests,
                  'linear_margin_sha256': digests['linear'].hexdigest(),
                  'linear_tail_weight': tail_weight, 'quadratic_tail_weight': outside}
