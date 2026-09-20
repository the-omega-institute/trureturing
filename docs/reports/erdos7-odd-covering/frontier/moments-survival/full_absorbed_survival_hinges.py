"""Exact full cell-cost source/deletion margins for the two survival hinges.

The cell-cost operator keeps the shallow mixed-seven carrier constants
inside the same maximization as their absorbed costs. All original-five
and ternary exponent tails are completed by exact geometric formulas.
The arithmetic uses the ordinary source-law proof; it is not a Lean proof.
"""
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256

THRESHOLDS = (4, 5)
BARRIER = F(1)
SOURCE_HINGE_WEIGHT = F(29, 35)


def require(condition, message):
    if not condition:
        raise ValueError(message)


class CellCost:
    def __init__(self, source, threshold, barrier):
        self.source = source
        self.t, self.C = F(threshold), F(barrier)
        require(self.C >= 0, 'Nonnegative barrier')
        self.tag = ('seven_block', (('h', self.t), 0))
        degree, slope, constant, source_cutoff = self.source.zero5_cost_metadata(self.tag)
        require(degree == 1 and slope == 1, 'Complete zero7 cost has unit affine tail')
        self.offset = -constant
        self.cut = max(source_cutoff, self.source.ceilq(self.t+self.C))
        self.tail0, self.tail1 = (4*v for v in self.source.geom(5, self.cut)[:2])
        require(sum(F(4, 5**n) for n in range(2, self.cut))+self.tail0 == F(1, 5),
                'Complete positive5 probability mass cancels the centered-cost linear tail')
        self.tail_identity_checks = 1
        self.gs, self.bs, self.dg, self.db = {}, {}, {}, {}
        self.qs, self.dq = {}, {}
        for weight in (0, 1, 2):
            require(all(self.g(weight, v) == v-self.offset-F(weight, 5)*self.C
                        for v in (self.cut, self.cut+1)),
                    'Cell-cost affine tail agrees with the source metadata and clipped barrier')
            self.tail_identity_checks += 1
            for v in range(1, self.cut+3):
                require(self.g(weight, v) >= 0, 'Cell cost nonnegative')
                require(self.g(weight, v+2)-2*self.g(weight, v+1)+self.g(weight,v) >= 0,
                     'Cell cost discrete convexity through affine entrance')
            for b in (1, 2, 3):
                self.gs[weight,b] = self.g(weight,b)
                self.bs[weight,b] = self.bar(weight,b)
                self.dg[weight,b] = self.deep(lambda v: self.g(weight,v), b, self.cut, F(1))
                self.db[weight,b] = self.deep(lambda v: self.bar(weight,v), b, self.cut, F(0))
                for n in range(2, self.cut):
                    self.qs[n,weight,b] = self.q(n,weight,b)
                    self.dq[n,weight,b] = self.deep(lambda v: self.q(n,weight,v), b,
                                                   self.source.ceilq(F(self.cut,n)), F(1))
        for weight in (0,1,2):
            for n in (self.cut,self.cut+1):
                for v in (1,2,3):
                    require(self.q(n,weight,v) == v-1, 'Positive5 complete tail equals v-1')
                    self.tail_identity_checks += 1

    @lru_cache(None)
    def g(self,weight,v):
        return self.source.zero5_cost(self.tag,v)-F(weight,5)*min(self.C,max(F(v)-self.t,F(0)))
    @lru_cache(None)
    def q(self,n,weight,v):
        return (self.g(weight,n*v)-self.g(weight,n))/n
    @lru_cache(None)
    def bar(self,weight,v):
        return sum(F(4,5**n)*self.q(n,weight,v) for n in range(2,self.cut))+self.tail0*(v-1)-self.g(weight,v)/5
    def deep(self,fn,b,cut,slope):
        entry=max(0,cut-b)
        total=sum(F(1,3**(k+3))*(fn(b+k+1)-fn(b+k)) for k in range(entry))
        require(fn(b+entry+1)-fn(b+entry)==fn(b+entry+2)-fn(b+entry+1)==slope,
             'Exact affine deep-tail entrance')
        self.tail_identity_checks += 1
        return total+slope*self.source.geom(3,entry+3)[0]
    @lru_cache(None)
    def positive(self,weights,eta):
        answer=F(0)
        for n in range(2,self.cut):
            pure=max(sum(eta[l]*self.qs[n,weights[l],b[l]] for l in range(5))
                     +max(self.dq[n,weights[l],b[l]] for l in range(5)) for b in self.source.BASES)
            answer+=F(4,5**n)*(sum(eta[l]*self.g(weights[l],n) for l in range(5))+(n-1)*pure)
        pure_affine=max(sum(eta[l]*(b[l]-1) for l in range(5))+F(1,18) for b in self.source.BASES)
        answer+=self.tail1*sum(eta)-self.tail0*sum(eta[l]*(self.offset+F(weights[l],5)*self.C)
                                               for l in range(5))+(self.tail1-self.tail0)*pure_affine
        return answer
    def operator(self,weights,dat):
        d,n,eta,_,_=dat
        values=tuple(sum(n[l]*self.gs[weights[l],b[l]]+eta[l]*self.bs[weights[l],b[l]] for l in range(5))
                     +max(d[l]*self.dg[weights[l],b[l]]+self.db[weights[l],b[l]] for l in range(5))
                     for b in self.source.BASES)
        return max(values)+self.positive(weights,eta),tuple(i for i,v in enumerate(values) if v==max(values))
    def margin(self,dat):
        d,n,eta,s,D=dat
        w=tuple(9*x for x in eta)
        roots=(sum(n[:2]),sum(n[2:]))
        Trest=(max(d)/18+(sum(w)+max(sum(w[:2]),sum(w[2:]))+max(w))/36+F(1,72))/5
        require(D==s-(max(roots)+max(n))/5-Trest,'Same raw survivor mass decomposition')
        unweighted,_=self.operator((0,)*5,dat)
        require(unweighted==self.source.zero5_raw(self.tag,dat),'Omega0 exactly reconstructs original complete zero5_raw')
        raw=self.source.raw357(self.t,dat)
        positive7=raw-unweighted
        values=[]
        for r in (0,1):
            for j in range(5):
                weights=tuple(int(self.source.ROOT[l]==r)+int(l==j) for l in range(5))
                value,baselines=self.operator(weights,dat)
                values.append((self.C*(roots[r]+n[j])/5+value,r,j,baselines))
        largest=max(v[0] for v in values)
        margin=self.C*s-positive7-self.C*Trest-largest
        return margin,[(r,j,b) for v,r,j,b in values if v==largest],raw,unweighted


def reconstruct(source, rows):
    parameters = list(source.vertices())
    require(len(parameters) == len(rows) == 1296 and len(source.BASES) == 10
            and [row['index'] for row in rows] == list(range(1296)),
            'Complete ordered source parameters and independent shallow baselines')
    require(SOURCE_HINGE_WEIGHT-F(2, 5) == F(3, 7) > 0,
            'Cell-cost convexity leaves a positive h_t coefficient')
    costs = {t: CellCost(source, t, BARRIER) for t in THRESHOLDS}
    output, changes = [], []
    digest = sha256()
    gains = {t: [] for t in THRESHOLDS}
    omega_checks = domination_checks = 0
    for index, (parameter, row) in enumerate(zip(parameters, rows)):
        dat = source.data(parameter)
        d, n, eta, s, D = dat
        require((F(row['s']), F(row['D'])) == (s, D) and min(d) >= F(1, 4)
                and min(n) >= 0 and min(eta) > 0 and 0 < D <= s,
                'Same raw source mass and convex combined deep-cost premises')
        updated, record = dict(row), {'index': index}
        for t in THRESHOLDS:
            margin, controllers, raw, zero = costs[t].margin(dat)
            omega_checks += 1
            old_margin = F(row['absorbed_hinge_'+str(t)+'_margin'])
            epsilon = F(row['absorbed_hinge_'+str(t)+'_epsilon'])
            require(epsilon >= 0 and old_margin == D-raw+epsilon,
                    'Predecessor epsilon margin uses the same complete source')
            gain = margin-old_margin
            require(isinstance(margin, F) and gain > 0,
                    'Full absorbed margin strictly improves every certified vertex lower bound')
            domination_checks += 1
            gains[t].append(gain)
            updated['full_absorbed_hinge_'+str(t)+'_margin'] = margin
            updated['full_absorbed_hinge_'+str(t)+'_gain'] = gain
            record[str(t)] = {'margin': margin, 'previous_lower': old_margin,
                              'gain': gain, 'zero5_raw': zero,
                              'positive7_complement': raw-zero,
                              'maximizing_carriers_and_baselines': controllers}
            digest.update(f'{index},{t}:{margin},{gain}\n'.encode())
        output.append(updated)
        changes.append(record)
    require(omega_checks == domination_checks == 2592,
            'Both hinges at all1296 vertices checked for exact reconstruction and strict improvement')
    require(min(gains[4]) == F(1, 9375) and min(gains[5]) == F(1, 56250),
            'Exact observed minimum improvements over the epsilon lower bounds')
    return output, {'thresholds': list(THRESHOLDS), 'barriers': [BARRIER, BARRIER],
                    'source_hinge_weight': SOURCE_HINGE_WEIGHT,
                    'minimum_absorbed_hinge_coefficient': F(3, 7),
                    'omega0_scalar_reconstruction_checks': omega_checks,
                    'strict_margin_domination_checks': domination_checks,
                    'carrier_operator_evaluations': 25920,
                    'tail_identity_checks': sum(cost.tail_identity_checks for cost in costs.values()),
                    'gains': {t: {'minimum': min(values), 'maximum': max(values),
                                  'strictly_positive_vertices': sum(v > 0 for v in values)}
                              for t, values in gains.items()},
                    'rows': changes, 'full_margin_sha256': digest.hexdigest(),
                    'tail_rule': 'For v at or above ceil(t+C), g_l(v)=v-a_t-omega_l*C. Thus q_n,l(v)=v-1 for n at or above that cutoff, bar_g has constant tail, and every remaining sum is an exact geometric zeroth or first moment.',
                    'vertex_table_semantics': 'These are exact values of the globally defined separately concave full absorbed margin with C=1. Predecessor epsilon values remain only lower bounds.',
                    'scope': 'General CellCost accepts a nonnegative rational C, but this certificate evaluates only C=1 for h4 and h5. Independent original labels and complete tails are preserved; ordinary source-law proof plus exact arithmetic, no unrestricted endpoint.'}
