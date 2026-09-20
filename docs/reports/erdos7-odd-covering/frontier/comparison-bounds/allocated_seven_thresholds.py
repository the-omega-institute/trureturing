"""Complete original-seven threshold costs and common-carrier consumer.

Allocations depend on the full forbidden root, never on source vertices.
Partial carriers maximize the entire positive+zero source expression over
compatible full completions. All exponent tails use exact geometric sums.
The universal comparison and interpolation are ordinary proof inputs.
"""
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from itertools import product

CARRIERS = tuple(product((-1, 0, 1), (-1, 0, 1, 2, 3, 4)))
FULL = tuple(product((0, 1), range(5)))
ALLOCATIONS = {4: {0: (F(2), F(1)), 1: (F(2), F(1))},
               5: {0: (F(2), F(1), F(1)), 1: (F(5, 2), F(1), F(1))}}
CREDITS = {4: F(4, 253125), 5: F(4, 1265625)}
CAPS, Q = ((11, F(5, 3)), (13, F(12, 7))), F(23, 42)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def hinge(threshold, value):
    return max(F(value)-threshold, F(0))


class AllocatedCost:
    def __init__(self, source, threshold, allocation, block, weights):
        self.source, self.t = source, F(threshold)
        self.taus, self.block, self.weights = tuple(allocation), block, tuple(weights)
        require(len(self.taus) == threshold-2 and 0 <= block < threshold-1
                and len(weights) == 5 and all(w in (0, 1, 2) for w in weights),
                'Complete finite threshold and shallow weight domains')
        require(all(1 <= tau <= threshold-n+1 for n, tau in enumerate(self.taus, 2)),
                'Every allocated threshold at least one and sums to the hinge threshold')
        self.cut = threshold+1
        self.tag = ('seven_block', (('h', self.t), block))
        degree, self.slope, _, _ = source.zero5_cost_metadata(self.tag)
        require(degree == 1, 'Original block has an affine tail')
        self.tail0, self.tail1 = (4*z for z in source.geom(5, self.cut)[:2])
        for l in range(5):
            require(self.g(l, 1) == 0, 'Every cost vanishes at one')
            require(all(self.g(l, v) >= 0 and self.g(l, v+1) >= self.g(l, v)
                        and self.g(l, v+2)-2*self.g(l, v+1)+self.g(l, v) >= 0
                        for v in range(1, self.cut+2)), 'Increasing convex integer costs')
        self.gs = {(l, b): self.g(l, b) for l in range(5) for b in (1, 2, 3)}
        self.bs = {(l, b): self.bar(l, b) for l in range(5) for b in (1, 2, 3)}
        self.dg = {(l, b): self.deep(lambda v: self.g(l, v), b, self.cut, self.slope)
                   for l in range(5) for b in (1, 2, 3)}
        self.db = {(l, b): self.deep(lambda v: self.bar(l, v), b, self.cut, F(0))
                   for l in range(5) for b in (1, 2, 3)}
        self.qtables = {
            n: ({(l, b): self.q(n, l, b) for l in range(5) for b in (1, 2, 3)},
                {(l, b): self.deep(lambda v: self.q(n, l, v), b,
                                  source.ceilq(F(self.cut, n)), self.slope)
                 for l in range(5) for b in (1, 2, 3)}) for n in range(2, self.cut)}

    @lru_cache(None)
    def g(self, l, v):
        value = self.source.zero5_cost(self.tag, v)
        if self.block == 0:
            value -= F(self.weights[l], 5)*min(F(1), hinge(self.t, v))
        for n, tau in enumerate(self.taus, 2):
            if n > self.block:
                target = tau if self.block == 0 else (self.t-tau)/(n-1)
                value += F(36, 5*7**n)*(hinge(target, v)-hinge(self.t/n, v))
        return value

    @lru_cache(None)
    def q(self, n, l, v):
        return (self.g(l, n*v)-self.g(l, n))/n

    @lru_cache(None)
    def bar(self, l, v):
        return sum(F(4, 5**n)*self.q(n, l, v) for n in range(2, self.cut)) + (
            self.tail0*self.slope*(v-1)-self.g(l, v)/5)

    def deep(self, fn, b, cut, slope):
        entry = max(0, cut-b)
        value = sum(F(1, 3**(k+3))*(fn(b+k+1)-fn(b+k)) for k in range(entry))
        require(fn(b+entry+1)-fn(b+entry) == fn(b+entry+2)-fn(b+entry+1) == slope,
                'Analytic affine entrance agrees with complete deep tail')
        return value+slope*self.source.geom(3, entry+3)[0]

    @lru_cache(None)
    def positive(self, eta):
        value = F(0)
        for n in range(2, self.cut):
            initial, deep = self.qtables[n]
            pure = max(sum(eta[l]*initial[l, b[l]] for l in range(5))
                       +max(deep[l, b[l]] for l in range(5)) for b in self.source.BASES)
            value += F(4, 5**n)*(sum(eta[l]*self.g(l, n) for l in range(5))+(n-1)*pure)
        affine = max(sum(eta[l]*(b[l]-1) for l in range(5))+F(1, 18)
                     for b in self.source.BASES)
        intercept = [self.g(l, self.cut)-self.slope*self.cut for l in range(5)]
        return value+self.tail1*self.slope*sum(eta) + (
            self.tail0*sum(eta[l]*intercept[l] for l in range(5))
            +(self.tail1-self.tail0)*self.slope*affine)

    def value(self, dat):
        d, n, eta, _, _ = dat
        return max(sum(n[l]*self.gs[l, b[l]]+eta[l]*self.bs[l, b[l]] for l in range(5))
                   +max(d[l]*self.dg[l, b[l]]+self.db[l, b[l]] for l in range(5))
                   for b in self.source.BASES)+self.positive(eta)


def reconstruct(source, previous46, rows39, progress=None):
    parameters = list(source.vertices())
    inherited = [r for first in previous46['joint_survival']['row_blocks']
                 for second in first for r in second]
    require(len(parameters) == len(inherited) == len(rows39) == 1296
            and [r['index'] for r in inherited] == list(range(1296)), 'Complete source domain')
    oldzero, newzero, oldpositive, newpositive = {}, {}, {}, {}
    for t in (4, 5):
        equal = tuple(F(t, n) for n in range(2, t))
        for c in FULL:
            weights = tuple(int(source.ROOT[l] == c[0])+int(l == c[1]) for l in range(5))
            oldzero[t, c] = AllocatedCost(source, t, equal, 0, weights)
            newzero[t, c] = AllocatedCost(source, t, ALLOCATIONS[t][c[0]], 0, weights)
        for e in range(1, t-1):
            oldpositive[t, e] = AllocatedCost(source, t, equal, e, (0,)*5)
            for root in (0, 1):
                newpositive[t, root, e] = AllocatedCost(source, t, ALLOCATIONS[t][root], e, (0,)*5)
    result, digest, recovered = [], sha256(), 0
    minima, maxima, local = {4: None, 5: None}, {4: None, 5: None}, []
    for index, parameter in enumerate(parameters):
        dat = source.data(parameter)
        d, n, eta, s, D = dat
        require((F(rows39[index]['s']), F(rows39[index]['D'])) == (s, D), 'Same raw source')
        w = tuple(9*x for x in eta)
        rest = (max(d)/18+(sum(w)+max(sum(w[:2]), sum(w[2:]))+max(w))/36+F(1, 72))/5
        oldcap, newcap = {}, {}
        for t in (4, 5):
            positive = source.raw357(F(t), dat)-source.zero5_raw(oldzero[t, (0, 0)].tag, dat)
            diff = {r: sum(newpositive[t, r, e].value(dat)-oldpositive[t, e].value(dat)
                           for e in range(1, t-1)) for r in (0, 1)}
            oldcap[t], newcap[t] = {}, {}
            for c in FULL:
                h = ((sum(n[:2]) if c[0] == 0 else sum(n[2:]))+n[c[1]])/5
                oldcap[t][c] = positive+h+oldzero[t, c].value(dat)
                newcap[t][c] = positive+diff[c[0]]+h+newzero[t, c].value(dat)
        conditional = []
        for j, c in enumerate(CARRIERS):
            old = inherited[index]['conditional'][j]
            require(tuple(old['carrier']) == c, 'Same common-carrier order')
            completions = tuple(f for f in FULL if all(x == -1 or x == y for x, y in zip(c, f)))
            margins, gains = {}, {}
            for t in (4, 5):
                rebuilt = s-rest-max(oldcap[t][f] for f in completions)+CREDITS[t]
                require(rebuilt == F(old['m'+str(t)]), 'Every old full/partial margin exactly recovered')
                recovered += 1
                margins[t] = s-rest-max(newcap[t][f] for f in completions)+CREDITS[t]
                gains[t] = margins[t]-rebuilt
                minima[t] = gains[t] if minima[t] is None else min(minima[t], gains[t])
                maxima[t] = gains[t] if maxima[t] is None else max(maxima[t], gains[t])
            mass = F(old['D_c'])
            hpartial = ((sum(n[:2]) if c[0] == 0 else sum(n[2:]) if c[0] == 1 else F(0))
                        +(n[c[1]] if c[1] >= 0 else F(0)))/5
            require(mass == s-rest-hpartial and D <= mass <= s, 'Original partial actual-mass bounds')
            m25 = F(old['m25'])
            M = margins[4]/6+F(4, 33)*margins[5]+m25/22
            require(F(old['M']) == F(old['m4'])/6+F(4, 33)*F(old['m5'])+m25/22,
                    'Inherited common three-hinge survival sum')
            item = {'carrier': c, 'D_c': mass, 'm4': margins[4], 'm5': margins[5],
                    'm25': m25, 'M': M, 'old_M': F(old['M'])}
            conditional.append(item)
            digest.update(f'{index},{c}:{mass},{margins[4]},{margins[5]},{M}\n'.encode())
            if (index, c) in ((398, (1, 1)), (402, (0, 1)), (404, (0, 1)), (406, (0, 1))):
                local.append({'index': index, 'carrier': c, 'gain4': gains[4], 'gain5': gains[5]})
        result.append(dict(rows39[index], conditional=conditional))
        if progress is not None:
            progress(index+1, len(parameters))
    require(recovered == 46656 and CREDITS[4]/6+F(4, 33)*CREDITS[5] == F(14, 4640625),
            'All old margins and unchanged complete conditional credit')
    return result, {'allocations_by_full_root': ALLOCATIONS, 'credits': CREDITS,
                    'old_margin_checks': recovered, 'carriers_per_vertex': 18,
                    'conditional_margin_sha256': digest.hexdigest(), 'minimum_gains': minima,
                    'maximum_gains': maxima, 'control_gains': local,
                    'partial_rule': 'Maximum entire positive+zero+carrier source cost over compatible full completions.'}


def consume(source, core, kc, previous47, previous49, pure, rows):
    old47 = [r for a in previous47['six_linear']['row_blocks'] for b in a for r in b]
    refined = {r['index']: r for b in previous49['frontier']['row_blocks'] for r in b}
    H16, H41, A81, cG = (F(previous49[k]) for k in ('H16', 'H41', 'A81', 'cG'))
    H = source.AC*H16+H41
    keys = ('bound', 'Gamma13', 'T13_81', 'combined')
    slopes = dict(zip(keys, (H, H16, A81, H+A81)))
    offsets = dict(zip(keys, (source.WHOLE_CONST, F(16), F(0), source.WHOLE_CONST)))
    targets = {mode: {k: None for k in keys} for mode in ('old', 'new')}
    choices = {k: [] for k in keys}
    rho, rhochoices, prepared = {'old': None, 'new': None}, [], []
    finite, tails = source.ap_product_distribution(CAPS, 9)
    require(cG == tails[2]+sum(v*v*finite[v] for v in (7, 8)), 'Complete square-tail coefficient')
    parameters = list(source.vertices())
    for row in rows:
        i, s = row['index'], row['s']
        dat = source.data(parameters[i])
        raw81 = sum(prob*v*v*source.square357(F(81, v*v), dat) for v, prob in finite.items() if v < 7)
        for j, cond in enumerate(row['conditional']):
            c, low, M = cond['carrier'], cond['D_c'], cond['M']
            ml = F((refined[i] if i in refined else old47[i])['conditional_M41'][j])
            mq = F(refined[i]['conditional_Mquad'][j]) if i in refined else row['Mquad']
            mg = row['source_margin']
            corr = {'bound': source.AC*mq+ml, 'Gamma13': mq, 'T13_81': cG*mg-raw81,
                    'combined': source.AC*mq+ml+cG*mg-raw81}
            prepared.append((i, c, low, s, M, corr))
            for endpoint, X in (('D_c', low), ('s', s)):
                label = (i, c, endpoint)
                for mode, margin in (('old', cond['old_M']), ('new', M)):
                    denominator = Q*X+margin
                    require(denominator > 0, 'Positive endpoint denominator')
                    value = denominator/X
                    if rho[mode] is None or value < rho[mode]:
                        rho[mode] = value
                        if mode == 'new':
                            rhochoices = [label]
                    elif mode == 'new' and value == rho[mode]:
                        rhochoices.append(label)
                    for k in keys:
                        numerator = slopes[k]*X-corr[k]
                        require(numerator > 0, 'Positive complete numerator')
                        value = offsets[k]+numerator/denominator
                        if targets[mode][k] is None or value > targets[mode][k]:
                            targets[mode][k] = value
                            if mode == 'new':
                                choices[k] = [label]
                        elif mode == 'new' and value == targets[mode][k]:
                            choices[k].append(label)
    require(all(targets['old'][k] == F(previous49[k]) for k in keys)
            and rho['old'] == F(previous49['rho']), 'All published49 targets recovered')
    current = targets['new']
    coefficients = {k: Q*(current[k]-offsets[k])-slopes[k] for k in keys} | {'rho': Q-rho['new']}
    minima, digest, count = {k: None for k in coefficients}, sha256(), 0
    for i, c, low, s, M, corr in prepared:
        for endpoint, X in (('D_c', low), ('s', s)):
            for k, a in coefficients.items():
                margin = a*X+M if k == 'rho' else a*X+(current[k]-offsets[k])*M+corr[k]
                require(margin >= 0, 'Every signed fixed-target endpoint inequality')
                count += 1
                minima[k] = margin if minima[k] is None else min(minima[k], margin)
                digest.update(f'{i},{c},{endpoint},{k}:{margin}\n'.encode())
    branches, fullrho = core.fallbacks(source, CAPS, F(previous49['source_G357']),
                                      {k: current[k] for k in keys if k != 'combined'}, rho['new'])
    require(fullrho == rho['new'] and len(branches) == 8, 'All eight fallback branches')
    for branch in branches:
        branch['combined_bound'] = branch['bound']+branch['T13_81']
        require(branch['combined_bound'] < current['combined'], 'Every fallback combined target')
    inputs, errors = core.core_errors(kc, pure['source_inputs'], current['Gamma13'], rho['new'],
                                     current['T13_81'], current['bound'])
    for error in errors:
        error['combined_gap'] = current['combined']+error['total']-403
    require(count == 233280 and len(errors) == 2, 'Complete endpoint and core inventory')
    require(all(current[k] < F(previous49[k]) for k in keys) and rho['new'] > rho['old'],
            'All four upper targets improve and survival lower bound increases')
    return {**current, 'rho': rho['new'], 'H16': H16, 'H41': H41, 'A81': A81, 'cG': cG,
            'q_effective': Q, 'source_G357': F(previous49['source_G357']),
            'coefficients': coefficients, 'minimum_margins': minima,
            'selected_mass_endpoints': {k: 'D_c' if a >= 0 else 's' for k, a in coefficients.items()},
            'controllers': choices | {'rho': rhochoices}, 'old49_targets': targets['old'],
            'gain_from49': {k: F(previous49[k])-current[k] for k in keys},
            'source_inputs': inputs, 'fallbacks': branches, 'core_errors': errors,
            'consumer_endpoint_checks': count, 'consumer_margin_sha256': digest.hexdigest(),
            'scope': 'Fixed full-root allocations; complete source39 reconstruction, all old46 margins, pinned47/49 numerator bounds, two signed mass endpoints, eight fallbacks and two complete cores. No actual-family exclusion or unrestricted Erdos7 resolution.'}
