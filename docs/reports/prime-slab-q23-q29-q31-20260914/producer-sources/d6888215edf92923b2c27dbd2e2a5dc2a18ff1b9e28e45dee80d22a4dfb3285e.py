"""Independent outward Arb evaluation of every active GPU-returned raw row.

All budgets are logs of exact positive rationals. Cubing endpoint products
settles distance branches; comparing rational ratios settles nearest ties.
Knapsack clipping uses exact rational budgets, with all six orders retained.
"""

from fractions import Fraction as F
import itertools
import math

from flint import arb, ctx


def logq(q):
    q = F(q)
    return (arb(q.numerator)/arb(q.denominator)).log()


def distance_ratio(q0, q1, c, d):
    """delta=log(returned ratio)/3. Equality of ratios is exact, not overlap."""
    def ratio(z):
        z3 = F(z)**3
        return q0/z3 if z3 < q0 else z3/q1 if z3 > q1 else F(1)
    rc, rd = ratio(c), ratio(d)
    return min(rc,rd), rc == rd


def evaluate(C, D, q0, q1):
    q0, q1 = F(q0), F(q1)
    if not (0 < q0 <= q1 and len(C) == len(D) == 3 and
            all(1 < c < d for c,d in zip(C,D)) and q1 >= math.prod(C)):
        raise ValueError('outside positive feasible-mixture domain')
    c, d = [logq(z) for z in C], [logq(z) for z in D]
    h = [logq(F(di,ci)) for ci,di in zip(C,D)]
    ratios = [distance_ratio(q0,q1,ci,di) for ci,di in zip(C,D)]
    deltas = [logq(r)/3 for r,_ in ratios]
    V = sum(x*x for x in deltas)
    rho = (V/6).sqrt()
    mu, ell = logq(q1)/3, logq(min(C))
    L, H = mu-rho, mu+2*rho
    if not (L > 0 and H > 0):
        raise ArithmeticError('positive envelope support not enclosed at this precision')
    def f(x):
        return (-(-x).exp()).log1p()
    fc, fd = list(map(f,c)), list(map(f,d))
    mixtures, weights = [], []
    for order in itertools.permutations(range(3)):
        budget = q1/F(math.prod(C))
        y = [None]*3
        for i in order:
            step = F(D[i],C[i])
            y[i] = arb(0) if budget <= 1 else arb(1) if budget >= step else logq(budget)/h[i]
            budget /= step
        mixtures.append(sum((1-y[i])*fc[i]+y[i]*fd[i] for i in range(3)))
        weights.append(y)
    dual = mixtures[0]
    for value in mixtures[1:]:
        dual = dual.max(value)  # Arb encloses max; uncertain order retains both bounds.
    psi = f(H)+2*f(L)
    return dict(G=dual-psi, D=dual, Psi=psi, rho=rho, V0=V, L=L, H=H, ell=ell,
                M0=logq(q0), M1=logq(q1), mixtures=mixtures, weights=weights,
                nearest_ties=[i for i,(_,tie) in enumerate(ratios) if tie],
                distance_ratios=[str(r) for r,_ in ratios])


def sign(value):
    if not value.is_finite(): return 'unresolved'
    if value < 0: return 'negative'
    if value > 0: return 'positive'
    if value.upper() <= 0: return 'nonpositive'
    if value.lower() >= 0: return 'nonnegative'
    return 'unresolved'


def enclosure(value):
    """Exact rational endpoints of the outward ball, not rounded display decimals."""
    if not value.is_finite(): return None
    return [str(value.lower().fmpq()), str(value.upper().fmpq())]


def certify_row(audit, precisions):
    if not audit['active']:
        return dict(outcome='inactive', refinements=[], sign_disagreement=False)
    result = dict(outcome='unresolved', refinements=[], sign_disagreement=False)
    for precision in precisions:
        with ctx.workprec(precision):
            try:
                values = evaluate(audit['C'],audit['D'],F(audit['q0']),F(audit['q1']))
                outcome = sign(values['G'])
                bounds = {k:enclosure(v) for k,v in values.items() if isinstance(v,arb)}
                item = dict(precision=precision, outcome=outcome, bounds=bounds,
                            nearest_ties=values.get('nearest_ties',[]),
                            distance_ratios=values.get('distance_ratios',[]),
                            mixtures=[enclosure(x) for x in values.get('mixtures',[])],
                            weights=[[enclosure(x) for x in y] for y in values.get('weights',[])])
            except (ArithmeticError,ValueError) as error:
                outcome = 'unresolved'
                item = dict(precision=precision,outcome=outcome,error=str(error))
            result['refinements'].append(item)
            result['outcome'] = outcome
            if outcome != 'unresolved': break
    result['sign_disagreement'] = (
        (audit['proposed'] == 'negative' and result['outcome'] in ('positive','nonnegative')) or
        (audit['proposed'] == 'positive' and result['outcome'] in ('negative','nonpositive')))
    return result
