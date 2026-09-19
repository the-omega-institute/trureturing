"""Common18 forbidden carriers for three independent survival tests.

Original test layouts remain independent inside each carrier envelope. A
conditional27/81 credit is added on the same shallow-carrier mixture. The
ordinary mixture and credit proofs are inputs; this module checks exact
finite arithmetic, complete tails, signed endpoints and old scalar bounds.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from hashlib import sha256
import json

CARRIERS = tuple(product((-1, 0, 1), (-1, 0, 1, 2, 3, 4)))
FULL = tuple(product((0, 1), range(5)))
ROOT = (0, 0, 1, 1, 1)
BASES = tuple(tuple(1+int(ROOT[l] == r)+int(l == j) for l in range(5))
              for r in range(2) for j in range(5))
T25, C25 = F(5, 2), F(7, 2)
TAG = ('h', T25)
ZERO = ('seven_block', (TAG, 0))
Q = F(23, 42)
CREDIT4, CREDIT5 = F(4, 253125), F(4, 1265625)
CREDIT = F(14, 4640625)
CAPS = ((11, F(5, 3)), (13, F(12, 7)))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def shallow(r, j, values):
    return (sum(values[:2]) if r == 0 else sum(values[2:]) if r == 1 else F(0)) + (
        values[j] if j >= 0 else F(0))


class SurvivalOperator:
 def __init__(self, source, linear, full, previous41, previous43):
  self.source, self.linear = source, linear
  self.previous41, self.previous43 = previous41, previous43
  self.parameters = list(source.vertices())
  self.costs = {t: full.CellCost(source, t, F(1)) for t in (4, 5)}
  require(len(self.parameters) == 1296 and source.BASES == BASES and source.ROOT == ROOT
          and len(CARRIERS) == 18 and len(FULL) == 10, 'Complete independent source/carrier domains')

 @lru_cache(None)
 def positive25(self,eta):
  degree,a,z,cut=self.source.zero5_cost_metadata(ZERO);require((degree,a,z,cut)==(1,F(1),-F(1117,490),3),'Exact h25 affine source metadata')
  x=sum(eta);tails=tuple(4*t for t in self.source.geom(5,cut))
  first=tuple(self.source.affine(F(0),'id',1,b,eta,self.source.ONES) for b in BASES)
  raw={n:tuple(self.source.zero5_scaled_pure(ZERO,n,b,eta) for b in BASES) for n in range(2,cut)}
  psi=lambda v:self.source.zero5_cost(ZERO,v)
  constant=sum(F(4,5**n)*psi(n) for n in range(2,cut))+a*tails[1]+z*tails[0]
  values=tuple(sum(F(4,5**n)*(raw[n][ci]-psi(n)*x+(n-2)*(max(raw[n])-psi(n)*x))/n for n in range(2,cut))+a*tails[0]*(first[ci]-x)+a*(tails[1]-2*tails[0])*(max(first)-x)+constant*x for ci in range(10))
  rebuilt=sum(F(4*(n-1),5**n)*(max(raw[n])-psi(n)*x)/n for n in range(2,cut))+a*(tails[1]-tails[0])*(max(first)-x)+constant*x
  require(rebuilt==self.source.zero5_positive_with_constant(ZERO,eta) and max(values)<=rebuilt,'Independent positive5 layouts and full affine tail')
  return values


 def conditional25(self,dat):
  d,n,eta,s,D=dat;common=self.source.raw357(T25,dat)-self.source.zero5_raw(ZERO,dat)
  vals={c:None for c in CARRIERS};layouts={c:[] for c in CARRIERS};old=None
  for bi,b in enumerate(BASES):
   k=tuple(C25-self.source.zero5_cost(TAG,v) for v in b)
   inc=tuple(self.source.zero5_cost(TAG,v+1)-self.source.zero5_cost(TAG,v) for v in b)
   baseline=sum(n[l]*self.source.zero5_cost(ZERO,b[l])+eta[l]*self.source.zero5_centered_correction(ZERO,b[l]) for l in range(5))+max(self.source.zero5_common_deep(ZERO,b[l],d[l]) for l in range(5))
   for ci,c5 in enumerate(BASES):
    correction=tuple(v*t for v,t in zip(inc,c5))
    require(all(0<=u<=v<=w for u,v,w in zip(inc,correction,k)),'h25 independent three-event floor')
    signed=tuple(k[l]*n[l]-correction[l]*eta[l]/5 for l in range(5))
    deep=tuple(k[l]*d[l]-correction[l]/5 for l in range(5));kw=tuple(9*eta[l]*k[l] for l in range(5))
    require(all(x>=v/20>=0 for x,v in zip(deep,k)),'Nonnegative full deep cofactor remainder')
    rest=F(13,243)*max(deep)+F(1,486)*max(k[l]*d[l] for l in range(5))+(sum(kw)+max(sum(kw[:2]),sum(kw[2:]))+max(kw))/36+max(k)/72
    cap=self.linear.event_cap(dat,k,correction)
    require(cap==max(F(0),sum(signed[:2]),sum(signed[2:]))+max((F(0),)+signed)+rest,'Full source cap reconstructed before shallow maximization')
    U=common+baseline+self.positive25(eta)[ci]
    candidate=U+cap/5;old=candidate if old is None else max(old,candidate)
    for c in CARRIERS:
     v=U+(shallow(*c,signed)+rest)/5
     if vals[c] is None or v>vals[c]:vals[c]=v;layouts[c]=[(bi,ci)]
     elif v==vals[c]:layouts[c].append((bi,ci))
  require(max(vals.values())==old,'Conditioned h25 independently recovers original18-carrier maximum')
  return {c:C25*s-v for c,v in vals.items()},vals,common,layouts


 def row(self,index):
  dat=self.source.data(self.parameters[index]);d,n,eta,s,D=dat;w=tuple(9*x for x in eta)
  rest=(max(d)/18+(sum(w)+max(sum(w[:2]),sum(w[2:]))+max(w))/36+F(1,72))/5
  h={c:shallow(*c,n)/5 for c in CARRIERS};Dc={c:s-rest-h[c] for c in CARRIERS}
  require(min(Dc.values())==D and all(D<=v<=s for v in Dc.values()),'Exact same-carrier raw-mass lower bounds')
  m25,Q25,common25,layouts25=self.conditional25(dat)
  old25=F(self.previous41['survival_hinge']['rows'][index]['margin'])
  require(min(m25.values())==old25,'h25 old independent margin exactly reproduced')
  margins={F(5,2):m25};H={}
  for t in (4,5):
   zero=self.source.zero5_raw(self.costs[t].tag,dat);scalar,_=self.costs[t].operator((0,)*5,dat)
   require(scalar==zero,'Unweighted full cell operator reconstructs scalar source')
   P=self.source.raw357(F(t),dat)-zero
   full_H={}
   for c in FULL:
    r,j=c;weights=tuple(int(self.source.ROOT[l]==r)+int(l==j) for l in range(5))
    ff,_=self.costs[t].operator(weights,dat);full_H[c]=h[c]+ff
   H[t]={c:max(v for cf,v in full_H.items() if all(x==-1 or x==y for x,y in zip(c,cf))) for c in CARRIERS}
   margins[t]={c:s-P-rest-H[t][c] for c in CARRIERS}
   require(min(margins[t].values())==F(self.previous43['full_absorbed_hinges']['rows'][index][str(t)]['margin']),'Full/partial completion preserves old full-cell hinge margin')
  M={c:m25[c]/22+margins[4][c]/6+F(4,33)*margins[5][c] for c in CARRIERS}
  separate=old25/22+min(margins[4].values())/6+F(4,33)*min(margins[5].values())
  joint=min(M.values());gain=joint-separate
  require(gain>=0,'Common-carrier survival cannot weaken separate maxima')
  result={'index':index,'s':s,'D':D,'separate_M':separate,'joint_M':joint,'survival_gain':gain,
          'joint_controllers':[c for c in CARRIERS if M[c]==joint],
          'conditional':[{'carrier':c,'D_c':Dc[c],'m25':m25[c],'m4':margins[4][c],'m5':margins[5][c],'M':M[c]} for c in CARRIERS]}
  if index==398:
   A=(0,1);B=(1,1)
   require(max(Q25.values())-common25==F(14888537,23814000) and max(Q25.values())-Q25[A]==F(136597,11907000),'Pro h25 source value and incompatible-carrier loss')
   require(max(H[4].values())==F(1449983,7717500) and max(H[4].values())-H[4][B]==F(80039,694575000),'Pro full h4 source value and carrier loss')
   require(max(H[5].values())==F(60659909,405168750) and max(H[5].values())-H[5][B]==F(4571,5062500),'Pro full h5 source value and carrier loss')
   require(min(max(Q25.values())-v for c,v in Q25.items() if c!=B)==F(1,150),'All17 other carriers have the exact stated h25 loss gap')
   require(gain==F(29487793,229209750000) and result['joint_controllers']==[B],'Pro exact strict joint gain and unique worst carrier')
   result['pro_comparisons']=True
  return result


def reconstruct(source, linear, full, previous41, previous43, rows):
    require(len(rows) == 1296 and [r['index'] for r in rows] == list(range(1296)),
            'Complete ordered inherited source rows')
    require(CREDIT == CREDIT4/6+F(4, 33)*CREDIT5
            and CREDIT4 == F(1, 5**4)*(F(1, 27)+F(1, 81))/5
            and CREDIT5 == F(1, 5**5)*(F(1, 27)+F(1, 81))/5,
            'Exact same-carrier27/81 raw survival credit')
    op = SurvivalOperator(source, linear, full, previous41, previous43)
    result, records, gains = [], [], []
    digest = sha256()
    for index, old in enumerate(rows):
        row = op.row(index)
        require((old['s'], old['D']) == (row['s'], row['D']), 'Same actual raw source interval')
        row['joint_M_before_credit'] = row['joint_M']
        row['joint_M'] += CREDIT
        for conditional in row['conditional']:
            conditional['m4'] += CREDIT4
            conditional['m5'] += CREDIT5
            conditional['M'] += CREDIT
            require(conditional['M'] == conditional['m25']/22+conditional['m4']/6
                    +F(4, 33)*conditional['m5'], 'Credited conditional hinge sum')
        require(min(c['M'] for c in row['conditional']) == row['joint_M'],
                'Uniform conditional credit commutes with finite minimum')
        gain = row['survival_gain']
        if index in (398, 410, 422, 616, 628, 640):
            require(gain == F(29487793, 229209750000), 'Exact six-control carrier incompatibility gain')
        if index in (402, 404, 406, 414, 416, 418, 426, 428, 430,
                     618, 620, 622, 630, 632, 634, 642, 644, 646):
            require(gain == 0, 'Aligned18-control survival carrier maxima')
        gains.append(gain)
        for c in row['conditional']:
            digest.update(f"{index},{c['carrier']}:{c['D_c']},{c['m25']},{c['m4']},{c['m5']},{c['M']}\n".encode())
        records.append({'index': index, 'carrier_gain': gain,
                        'joint_controllers': row['joint_controllers'],
                        'conditional': row['conditional']})
        updated = dict(old)
        updated.update(row)
        result.append(updated)
    require(sum(g > 0 for g in gains) == 401 and min(gains) == 0
            and max(gains) == F(114544267, 297123750000), 'Complete observed carrier-gain inventory')
    return result, {'carriers': CARRIERS, 'hinge_credits': {4: CREDIT4, 5: CREDIT5},
                    'raw_denominator_credit': CREDIT, 'q_effective': Q,
                    'source_vertices': 1296, 'conditional_rows': 23328,
                    'h25_original_layout_checks': 129600,
                    'inherited_hinge_margin_checks': 3888, 'scalar_reconstruction_checks': 2592,
                    'positive_carrier_gain_vertices': 401, 'zero_carrier_gain_vertices': 895,
                    'minimum_carrier_gain': min(gains), 'maximum_carrier_gain': max(gains),
                    'rows': records, 'conditional_margin_sha256': digest.hexdigest(),
                    'scope': 'Common forbidden-carrier mixture with independent original test layouts. Partial carriers use full completion only for absorbed h4/h5. Credit holds conditionally before the same shallow mixture; no46-numerator joint aggregation.'}


def consume(source, core, kc, encode, previous43, pure, rows):
    require(len(rows) == 1296 and [r['index'] for r in rows] == list(range(1296))
            and F(previous43['q_effective']) == Q, 'Same charged source law and full domain')
    H16, H41, A81, cG = (F(previous43[k]) for k in ('H16', 'H41', 'A81', 'cG'))
    H = source.AC*H16+H41
    keys = ('bound', 'Gamma13', 'T13_81', 'combined')
    slopes = {'bound': H, 'Gamma13': H16, 'T13_81': A81, 'combined': H+A81}
    offsets = {'bound': source.WHOLE_CONST, 'Gamma13': F(16),
               'T13_81': F(0), 'combined': source.WHOLE_CONST}
    finite, tails = source.ap_product_distribution(CAPS, 9)
    require(cG == tails[2]+sum(k*k*finite[k] for k in (7, 8)), 'Complete unchanged AP square-tail coefficient')
    targets = {k: None for k in keys}
    old_targets = dict(targets)
    rho = old_rho = None
    choices = {k: [] for k in keys+('rho',)}
    corrections = []
    denominator_checks = 0
    parameters = list(source.vertices())
    for row in rows:
        dat = source.data(parameters[row['index']])
        D, s = row['D'], row['s']
        require((s, D) == dat[3:], 'Same raw source parameter')
        raw81 = sum(prob*n*n*source.square357(F(81, n*n), dat)
                    for n, prob in finite.items() if n < 7)
        mg, Mq, Ml = (F(row[k]) for k in ('source_margin', 'Mquad', 'M41'))
        corr = {'bound': source.AC*Mq+Ml, 'Gamma13': Mq, 'T13_81': cG*mg-raw81,
                'combined': source.AC*Mq+Ml+cG*mg-raw81}
        corrections.append(corr)
        for X in (D, s):
            old_delta = Q*X+row['separate_M']
            require(old_delta > 0, 'Positive independently reconstructed43 denominator')
            for k in keys:
                value = offsets[k]+(slopes[k]*X-corr[k])/old_delta
                old_targets[k] = value if old_targets[k] is None else max(old_targets[k], value)
            value = old_delta/X
            old_rho = value if old_rho is None else min(old_rho, value)
        for conditional in row['conditional']:
            E, M = conditional['D_c'], conditional['M']
            require(D <= E <= s, 'Same-carrier mass bound lies in the old interval')
            for endpoint, X in (('D_c', E), ('s', s)):
                denominator = Q*X+M
                require(denominator > 0, 'Positive common-carrier denominator at both endpoints')
                denominator_checks += 1
                for k in keys:
                    numerator = slopes[k]*X-corr[k]
                    require(numerator > 0, 'Positive unchanged numerator comparison')
                    value = offsets[k]+numerator/denominator
                    label = [row['index'], conditional['carrier'], endpoint]
                    if targets[k] is None or value > targets[k]:
                        targets[k], choices[k] = value, [label]
                    elif value == targets[k]:
                        choices[k].append(label)
                value = denominator/X
                label = [row['index'], conditional['carrier'], endpoint]
                if rho is None or value < rho:
                    rho, choices['rho'] = value, [label]
                elif value == rho:
                    choices['rho'].append(label)
    require(all(old_targets[k] == F(previous43[k]) for k in keys)
            and old_rho == F(previous43['rho']), 'All five published43 independent targets reconstructed')
    coefficients = {k: Q*(targets[k]-offsets[k])-slopes[k] for k in keys}
    coefficients['rho'] = Q-rho
    selected = {k: 'D_c' if a >= 0 else 's' for k, a in coefficients.items()}
    minima = {k: None for k in coefficients}
    digest = sha256()
    count = endpoint_count = 0
    for row, corr in zip(rows, corrections):
        for conditional in row['conditional']:
            for endpoint, X in (('D_c', conditional['D_c']), ('s', row['s'])):
                M = conditional['M']
                for k in coefficients:
                    margin = (Q-rho)*X+M if k == 'rho' else (
                        coefficients[k]*X+(targets[k]-offsets[k])*M+corr[k])
                    require(margin >= 0, 'Exact common-mixture fixed-target endpoint inequality')
                    endpoint_count += 1
                    if endpoint == selected[k]:
                        minima[k] = margin if minima[k] is None else min(minima[k], margin)
                        digest.update(f"{row['index']},{conditional['carrier']},{k},{endpoint}:{margin}\n".encode())
                        count += 1
    branches, full_rho = core.fallbacks(source, CAPS, F(previous43['source_G357']),
        {k: targets[k] for k in keys if k != 'combined'}, rho)
    require(full_rho == rho and len(branches) == 8, 'All fallback survival and cost targets')
    for branch in branches:
        branch['combined_bound'] = branch['bound']+branch['T13_81']
        branch['combined_margin'] = targets['combined']-branch['combined_bound']
        require(branch['combined_margin'] > 0, 'Every complete fallback combined bound')
    inputs, errors = core.core_errors(kc, pure['source_inputs'], targets['Gamma13'], rho,
                                     targets['T13_81'], targets['bound'])
    gain = targets['bound']+targets['T13_81']-targets['combined']
    require(gain >= 0, 'Common-law sum no worse than separate target sum')
    for error in errors:
        error['combined_gap'] = targets['combined']+error['total']-403
        require(error['combined_gap'] == error['gap']-gain, 'Same complete-core interface')
    require(count == 116640 and endpoint_count == 233280 and denominator_checks == 46656
            and len(errors) == 2, 'Complete source/carrier/target and core inventory')
    require(all(targets[k] < F(previous43[k]) for k in keys) and rho > F(previous43['rho']),
            'All four cost targets and survival strictly improve43')
    return {**targets, 'rho': rho, 'q_effective': Q,
            'H16': H16, 'H41': H41, 'cG': cG, 'A81': A81,
            'source_G357': F(previous43['source_G357']),
            'source_comparison_barrier': F(previous43['source_comparison_barrier']),
            'coefficients': coefficients, 'selected_mass_endpoints': selected,
            'minimum_margins': minima, 'combined_target_gain': gain,
            'controllers': choices, 'maximizers': {k: sorted({v[0] for v in choices[k]}) for k in keys},
            'rho_minimizers': sorted({v[0] for v in choices['rho']}),
            'source_inputs': inputs, 'fallbacks': branches, 'core_errors': errors,
            'consumer_vertex_checks': 1296, 'consumer_carrier_checks': 23328,
            'consumer_denominator_checks': denominator_checks,
            'consumer_target_margin_checks': count, 'consumer_endpoint_margin_checks': endpoint_count,
            'fallback_checks': 8, 'complete_core_checks': 2,
            'consumer_margin_sha256': digest.hexdigest(),
            'scope': 'One common18-carrier mixture controls all three survival margins and the actual source-mass lower bound. Original test layouts stay independent. The conditional27/81 credit is included; numerator comparisons are inherited separately. Ordinary proof plus exact arithmetic, no unrestricted Erdos7 endpoint.'}
