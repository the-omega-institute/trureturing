#!/usr/bin/env python3
"""Finite checks of the p-flat extension of Harrington--Sun--Wong Thm 3.2.

Primary source: https://arxiv.org/pdf/2104.00602v1, pp. 7--8.
The paper states square-free input; the same construction only needs p^2
not to divide any input modulus. Fixtures below permit EVEN cofactors and
are NOT witnesses to the unknown all-odd premise. Standard library only.
"""
from fractions import Fraction as F
from math import gcd, isqrt, lcm
import json


def require(ok, message):
    if not ok:
        raise ValueError(message)


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def period(classes):
    return lcm(*(m for _, m in classes))


def load(classes, x):
    return sum((x - a) % m == 0 for a, m in classes)


def mass(classes):
    return sum((F(1, m) for _, m in classes), F(0))


def crt(a, m, b, n):
    require(gcd(m, n) == 1, 'CRT factors are not coprime')
    return (a + m * (((b-a) * pow(m, -1, n)) % n)) % (m*n)


def p_flat_construct(classes, p, q, *, allow_even=False, max_period=200000):
    """Construct and exhaustively verify an output within ``max_period``.

    The two pure-p residues may be any distinct digits. The returned
    normalization preserves original label indices and all input moduli.
    ``allow_even`` is for transport fixtures, never an odd-cover certificate.
    """
    require(prime(p) and p % 2 == 1, 'p must be an odd prime')
    require(prime(q) and q % 2 == 1, 'q must be an odd prime')
    require(all(m > 1 for _, m in classes), 'all input moduli must be nonunit')
    classes = [(a % m, m) for a, m in classes]
    require(allow_even or all(m % 2 for _, m in classes), 'even input forbidden')
    require(all(m % (p*p) for _, m in classes), 'input is not p-flat')
    pure = [i for i, (_, m) in enumerate(classes) if m == p]
    pure_digits = sorted({classes[i][0] for i in pure})
    require(len(pure) == 2 and len(pure_digits) == 2,
            'require exactly two distinct pure-p classes')
    other_moduli = [m for _, m in classes if m != p]
    require(len(set(other_moduli)) == len(other_moduli),
            'duplicate non-p modulus / residual cofactor label')
    require(all(m % q for _, m in classes) and q != p,
            'q is not fresh for the original input')
    in_period = period(classes)
    require(in_period <= max_period, 'input period exceeds finite-check cap')
    require(all(load(classes, x) >= 1 for x in range(in_period)),
            'input does not cover its complete period')
    original = list(classes)
    branch_order = pure_digits + [i for i in range(p) if i not in pure_digits]
    permutation = {old: new for new, old in enumerate(branch_order)}
    classes = [(a, m) if m % p else
               (crt(permutation[a % p], p, a % (m//p), m//p), m)
               for a, m in classes]
    p_free_period = in_period // p
    for x in range(in_period):
        y = crt(permutation[x % p], p, x % p_free_period, p_free_period)
        require(all(((x-a) % m == 0) == ((y-c) % n == 0)
                    for (a, m), (c, n) in zip(original, classes)),
                'root permutation failed original-label transport')
    deleted = [i for i, (a, m) in enumerate(classes)
               if m != p and m % p == 0 and a % p in (0, 1)]
    retained = [(i, a, m) for i, (a, m) in enumerate(classes)
                if i not in deleted and m != p and m % p]
    mixed = [(i, a, m//p) for i, (a, m) in enumerate(classes)
             if i not in deleted and m != p and m % p == 0]
    require(len({b for _, _, b in mixed}) == len(mixed),
            'duplicate residual cofactor label')
    output = []
    provenance = []
    original_to_output = {str(i): [] for i in range(len(classes))}

    def emit(a, m, role, original=None, height=None):
        j = len(output)
        output.append((a % m, m))
        provenance.append(dict(output=j, role=role, original=original,
                               height=height))
        if original is not None:
            original_to_output[str(original)].append(j)

    pure_one = next(i for i in pure if classes[i][0] == 1)
    for a in range(q-1):
        emit(p**a, p**(a+1), 'pure-p power branch', pure_one, a+1)
    for i in range(q):
        emit(crt(0, p**i, i, q), p**i*q, 'new-q closing class', None, i)
    for i, a, m in retained:
        emit(a, m, 'unchanged p-free original', i)
    for i, a, b in mixed:
        for h in range(q-1):
            emit(crt((a % p)*p**h, p**(h+1), a % b, b),
                 p**(h+1)*b, 'transported mixed original', i, h+1)
    require(len({m for _, m in output}) == len(output), 'output modulus collision')
    require(all(m > 1 for _, m in output), 'output has a unit modulus')
    require(allow_even or all(m % 2 for _, m in output), 'output is not odd')
    out_period = period(output)
    require(out_period <= max_period, 'output period exceeds finite-check cap')
    R = lcm(*(m for _, _, m in retained), *(b for _, _, b in mixed))
    require(out_period == p**(q-1)*q*R, 'incorrect prime-support/height formula')
    # Verify actual coverage and the same-witness argument. Handle zero first.
    for x in range(out_period):
        if x % (p**(q-1)) == 0:
            i = x % q
            require(x % (p**i) == 0, 'closing divisibility failed')
            require((x-crt(0, p**i, i, q)) % (p**i*q) == 0,
                    'new-q closing class misses its actual witness')
        else:
            h = 0
            while x % (p**(h+1)) == 0:
                h += 1
            xi = (x // p**h) % p
            if xi == 1:
                require((x-p**h) % (p**(h+1)) == 0, 'pure branch mismatch')
            else:
                witness = crt(xi, p, x % R, R)
                # R is p-free, so this is an actual original CRT input point.
                active = [i for i, (a,m) in enumerate(classes)
                          if (witness-a) % m == 0]
                require(active, 'restricted original cover failed')
                eligible = [i for i in active if i not in pure+deleted]
                require(eligible, 'no original label available on nonpure branch')
                require(any(any((x-output[j][0]) % output[j][1] == 0
                                    for j in original_to_output[str(i)])
                            for i in eligible), 'original/output label map failed')
        require(load(output, x) >= 1, 'output uncovered point')
    A = sum((F(1,m) for _,_,m in retained), F(0))
    B = sum((F(1,b) for _,_,b in mixed), F(0))
    expected = (A + (1+B)*(1-F(1,p**(q-1)))/(p-1)
                + F(p,q*(p-1))*(1-F(1,p**q)))
    require(mass(output) == expected, 'reciprocal mass identity failed')
    reduced_mass = mass(classes)-sum((F(1,classes[i][1]) for i in deleted),F(0))
    require(reduced_mass == F(2,p)+A+B/p, 'reduced input identity failed')
    return dict(input=original, normalized_input=classes,
                root_permutation=permutation, output=output, p=p, q=q,
                fixture_scope='even cofactors allowed; not an odd-cover witness'
                              if allow_even else 'all odd p-flat premise',
                input_period=in_period, output_period=out_period,
                checked_period_points=in_period+out_period,
                deleted_original_labels=deleted,
                original_to_output=original_to_output, provenance=provenance,
                A=str(A), B=str(B), input_excess=str(mass(classes)-1),
                reduced_input_excess=str(reduced_mass-1),
                output_excess=str(expected-1), output_lcm=out_period,
                zero_covered=load(output,0)>=1)


def expect_rejection(classes, p, q, reason, **kwargs):
    try:
        p_flat_construct(classes,p,q,**kwargs)
    except ValueError as e:
        require(reason in str(e), f'wrong rejection: {e}')
        return str(e)
    raise ValueError('invalid fixture unexpectedly admitted')


def main():
    seed=[(0,3),(1,3),(0,2),(5,6)]
    high=[(0,3),(1,3),(0,2),(1,4),(11,12)]
    results=[p_flat_construct(seed,3,5,allow_even=True),
             p_flat_construct(high,3,5,allow_even=True),
             p_flat_construct(high,3,7,allow_even=True),
             p_flat_construct(seed+[(0,21)],3,5,allow_even=True),
             p_flat_construct([(a+1,m) for a,m in high],3,5,allow_even=True)]
    bad=[expect_rejection(seed+[(0,9)],3,5,'not p-flat',allow_even=True),
         expect_rejection(seed+[(2,6)],3,5,'duplicate',allow_even=True),
         expect_rejection(seed+[(0,15)],3,5,'not fresh',allow_even=True),
         expect_rejection([(0,3),(1,3),(0,2)],3,5,'does not cover',allow_even=True),
         expect_rejection(seed,3,5,'even input forbidden'),
         expect_rejection([(0,3),(0,3),(0,2),(5,6)],3,5,
                          'two distinct pure-p',allow_even=True),
         expect_rejection(seed,3,5,'output period exceeds',
                          allow_even=True,max_period=10)]
    print(json.dumps(dict(source='HSW arXiv:2104.00602v1 Thm 3.2 pp7-8',
                          p_flat_extension='ordinary verification; no Lean claim',
                          success=True,fixtures=results,rejections=bad,
                          total_checked_period_points=sum(x['checked_period_points']
                                                          for x in results)),
                     sort_keys=True,indent=2))

if __name__ == '__main__':
    main()
