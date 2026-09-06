"""Exact finite function regressions for the prime/Mellin identities.

Positive rational multiplicative coordinates make all cutoffs exact. Logarithms
are represented by their prime-factor exponent vectors. Coefficients are exact
Gaussian-rational radical expressions, so no floating tolerance is used.
These finite checks supplement source review; they are not a Lean proof.
"""
from __future__ import annotations
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import platform
import sympy as s

@lru_cache(None)
def log_form(q):
    q = s.Rational(q)
    if q <= 0:
        raise ValueError('Log arguments must be positive.')
    out = {int(p): int(e) for p,e in s.factorint(q.p).items()}
    for p,e in s.factorint(q.q).items():out[int(p)] = out.get(int(p),0)-int(e)
    return {p:s.Integer(e) for p,e in out.items() if e}

@lru_cache(None)
def mangoldt_form(n: int, drop_powers: bool = False):
    if n <= 1:return {}
    f = s.factorint(n)
    if len(f) != 1:return {}
    p,e = next(iter(f.items()))
    if drop_powers and e > 1:return {}
    return {int(p): s.Integer(1)}

def scaled_add(target: dict, source: dict, factor):
    if factor == 0:return
    for p, c in source.items():target[p] = target.get(p,s.Integer(0))+factor*c

def equal(a: dict, b: dict) -> bool:
    return all(s.simplify(a.get(p,0)-b.get(p,0)) == 0 for p in a.keys()|b.keys())

def check_case(lam, M, u, coeff, mutation=None):
    lam,u = s.Rational(lam),s.Rational(u)
    def inside(t):return 1/lam <= t <= lam
    @lru_cache(None)
    def h(t):
        return s.Integer(0) if t > lam else sum(A*t**(2*j) for j,A in enumerate(coeff))
    @lru_cache(None)
    def p(t):
        return s.Integer(0) if not inside(t) else 4*s.sqrt(t)*sum(h(m*t) for m in range(1,M+1))
    @lru_cache(None)
    def even(t):return (p(t)+p(1/t))/2
    @lru_cache(None)
    def odd(t):return (p(t)-p(1/t))/2
    def q(t):
        out={}
        if inside(t):
            for m in range(1,M+1):scaled_add(out,log_form(m*t),4*s.sqrt(t)*h(m*t))
        return out
    def forward(f,t):
        out={}
        if inside(t):
            for n in range(1,M+1):
                denominator = n if mutation == 'wrong_half_density' else s.sqrt(n)
                scaled_add(out,mangoldt_form(n, mutation=='drop_prime_powers'),f(n*t)/denominator)
        return out
    def full(f,t):
        out={}
        if inside(t):
            for n in range(1,M+1):
                scaled_add(out,mangoldt_form(n),(f(n*t)+f(t/n))/s.sqrt(n))
        return out
    rhs=q(u)
    scaled_add(rhs,log_form(u),-p(u))
    forward_ok=equal(forward(p,u),rhs)
    rhs_even=q(u)
    scaled_add(rhs_even,q(1/u),1)
    if mutation != 'drop_odd_correction':
        scaled_add(rhs_even,log_form(u),-2*odd(u))
        scaled_add(rhs_even,forward(odd,u),-1)
        scaled_add(rhs_even,forward(odd,1/u),-1)
    return forward_ok, equal(full(even,u),rhs_even)

def run():
    cases=0
    seeds=[(s.Integer(1),), (1+s.I,s.Rational(-2,3)+s.I/5),
           (s.Rational(1,7),-2+s.I,s.Rational(3,5)-s.I/11)]
    for lam in (s.Rational(3,2),s.Integer(2),s.Rational(5,2),s.Integer(3),s.Integer(4)):
        capacity=int(s.ceiling(lam**2))
        points={1/lam,lam,s.Integer(1),1/lam**2,lam**2,
                (1+lam)/2,2/(1+lam),lam/2,2/lam}
        for M in (capacity,capacity+2):
            for u in sorted(points):
                for seed in seeds:
                    answer=check_case(lam,M,u,seed)
                    if answer != (True,True):
                        raise AssertionError((lam,M,u,seed,answer))
                    cases+=1
    witnesses={}
    for mutation in ('wrong_half_density','drop_prime_powers','drop_odd_correction'):
        result=check_case(s.Integer(4),16,s.Rational(1,4),(s.Integer(1),s.I),mutation)
        if (result[1] if mutation=='drop_odd_correction' else result[0]):
            raise AssertionError(f'Mutation survived: {mutation}')
        witnesses[mutation]={'lambda':'4','M':16,'u':'1/4','rejected':True}
    bad=check_case(s.Integer(3),2,s.Rational(1,3),(s.Integer(1),))
    if bad[0]:raise AssertionError('Insufficient-cutoff mutation survived.')
    witnesses['insufficient_cutoff']={'lambda':'3','M':2,'u':'1/3','rejected':True}
    return {'exact_function_cases':cases,'identities_per_case':2,
            'arithmetic':'Exact rational support tests, symbolic prime-log vectors and Gaussian-rational radicals; no floating tolerance.',
            'mutation_witnesses':witnesses,
            'python':platform.python_version(),'sympy':s.__version__,
            'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'status':'All finite exact regressions and four specified mutation rejections passed.',
            'scope':'Development checks of the actual finite formulas, not Lean parsing, kernel acceptance or an all-scale spectral certificate.'}

if __name__=='__main__':
    result=run()
    path=Path(__file__).with_name('mellin_prime_intertwining_regression.json')
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
