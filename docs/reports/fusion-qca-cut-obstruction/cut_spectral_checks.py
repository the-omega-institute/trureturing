#!/usr/bin/env python3
"""Exact finite diagnostics for the spectral cut-obstruction manuscript.

Standard library only. These checks do not verify a fusion-category realization,
DHR finite order, von Neumann algebras, FDQC exclusion, or Lean elaboration.
"""
from fractions import Fraction as Q
from itertools import product, permutations
from math import prod
from collections import Counter
import json


def eye(d):
    return tuple(tuple(int(i == j) for j in range(d)) for i in range(d))


def mul(a, b):
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in range(len(b)))
                       for j in range(len(b[0]))) for i in range(len(a)))


def power(a, n):
    if n < 0:
        raise ValueError('negative exponent')
    out = eye(len(a))
    while n:
        if n % 2:
            out = mul(out, a)
        a = mul(a, a)
        n //= 2
    return out


def rank(a):
    a = [list(map(Q, row)) for row in a]
    r = 0
    for c in range(len(a[0])):
        p = next((i for i in range(r, len(a)) if a[i][c]), None)
        if p is None:
            continue
        a[r], a[p] = a[p], a[r]
        v = a[r][c]
        a[r] = [x / v for x in a[r]]
        for i in range(len(a)):
            if i != r:
                v = a[i][c]
                a[i] = [x - v*y for x, y in zip(a[i], a[r])]
        r += 1
        if r == len(a):
            break
    return r


def primitive(a):
    b = eye(len(a))
    for p in range(1, (len(a)-1)**2 + 2):
        b = mul(b, a)
        if all(x > 0 for row in b for x in row):
            return p
    return None


def lincomb(coeffs, matrices):
    d = len(matrices[0])
    return tuple(tuple(sum(c*a[i][j] for c, a in zip(coeffs, matrices))
                       for j in range(d)) for i in range(d))


def moments(a, nmax):
    b, v = mul(a, a), eye(len(a))
    ds = [1]
    for _ in range(nmax):
        v = mul(v, b)
        ds.append(v[0][0])
    return ds


def check(condition, label, context=None):
    if not condition:
        raise AssertionError((label, context))


def profile(ds, k, sigma, n, lower, upper):
    shifted = [0]*len(k)
    for i, j in enumerate(sigma):
        shifted[j] = upper[i]
    lengths = [n + k[j] + shifted[j] - lower[j] for j in range(len(k))]
    check(min(lengths) >= 1, 'positive window', lengths)
    return prod(ds[t] for t in lengths)


def recover(ds, table, n, m):
    f00 = table[0][0]
    sigma, k = [], [None]*m
    for i in range(m):
        matches = []
        for j in range(m):
            z = f00*table[j+1][i+1] - table[j+1][0]*table[0][i+1]
            check(z <= 0, 'mixed defect sign')
            if z < 0:
                matches.append(j)
        check(len(matches) == 1, 'one destination per source')
        j = matches[0]
        sigma.append(j)
        ratio = Q(table[0][i+1], f00)
        hits = [t for t in range(1, len(ds)-1) if Q(ds[t+1], ds[t]) == ratio]
        check(len(hits) == 1, 'ratio determines cut position')
        k[j] = hits[0]-n
    check(sorted(sigma) == list(range(m)), 'permutation')
    return tuple(k), tuple(sigma)


def run():
    count = Counter()
    fib = (eye(2), ((0,1),(1,1)))
    z2 = (eye(2), ((0,1),(1,0)))
    s3 = (eye(3), ((0,1,0),(1,0,0),(0,0,1)), ((0,0,1),(0,0,1),(1,1,1)))
    fixtures = [('Fib', fib, None), ('RepZ2', z2, (1,1)), ('RepS3', s3, (1,1,2))]
    accepted = Counter()
    for name, basis, dims in fixtures:
        # Verify the regular-representation multiplication law from the unit column.
        for a in basis:
            for b in basis:
                ab = mul(a, b)
                c = tuple(row[0] for row in ab)
                check(ab == lincomb(c, basis), 'based-ring regular representation', name)
                count['regular_representation_products'] += 1
        for coeff in product(range(4), repeat=len(basis)):
            a = lincomb(coeff, basis)
            if primitive(a) is None:
                continue
            accepted[name] += 1
            d = moments(a, 20)
            chi = d[1]*d[3]-d[2]**2
            rk = rank(a)
            check(chi >= 0 and ((chi == 0) == (rk == 1)), 'rank dichotomy', (name, coeff))
            is_regular = dims is not None and coeff[0] > 0 and all(
                coeff[i] == coeff[0]*dims[i] for i in range(len(coeff)))
            check((rk == 1) == is_regular, 'regular object characterization', (name, coeff))
            count['three_moment_rank_and_regular_tests'] += 1
            for step in range(1, 5):
                for n in range(step+1, 17):
                    delta = d[n+step]*d[n-step]-d[n]**2
                    check(delta >= 0 and ((delta == 0) == (rk == 1)), 'all tested offsets', (name, coeff, n, step))
                    count['offset_signs'] += 1
            for block in (2,3,4):
                ab = power(a, block)
                db = moments(ab, 3)
                check(rank(ab) == rk, 'blocking rank')
                check((db[1]*db[3]-db[2]**2 == 0) == (chi == 0), 'blocking certificate')
                count['blocking_tests'] += 1
    # The complete squared-gap identity for finite measures, with an atom at zero.
    for lambdas in ((-3,-1,0,2), (-2,2,0), (0,1,3,5), (-1,0,1)):
        mus = tuple(Q(x*x) for x in lambdas)
        weights = tuple(Q(i+1, sum(range(1,len(mus)+1))) for i in range(len(mus)))
        for step in range(1,5):
            for n in range(step+1,13):
                moment = lambda t: sum(c*u**t for c,u in zip(weights,mus))
                lhs = moment(n+step)*moment(n-step)-moment(n)**2
                rhs = sum(weights[i]*weights[j]*(mus[i]*mus[j])**(n-step)*(mus[i]**step-mus[j]**step)**2
                          for i in range(len(mus)) for j in range(i+1,len(mus)))
                check(lhs == rhs, 'spectral gap expansion')
                count['spectral_measure_identities'] += 1
    df, ds = moments(fib[1],30), moments(s3[2],30)
    for n in range(1,25):
        check(ds[n] == (4**n+2)//6, 'S3 closed form')
        count['S3_moments'] += 1
    for step in range(1,7):
        for n in range(step+1,24):
            check(ds[n+step]*ds[n-step]-ds[n]**2 == Q(4**(n-step)*(4**step-1)**2,18), 'S3 defect formula')
            count['S3_offset_formula'] += 1
    # Polarized cut table recovers shifts AND permutations, including equal shifts.
    recoveries = {}
    for name, d in [('Fib',df), ('RepS3',ds)]:
        subtotal = 0
        for m in (2,3):
            zero = (0,)*m
            probes = [zero]+[tuple(int(i==j) for i in range(m)) for j in range(m)]
            for sigma in permutations(range(m)):
                for k in product(range(-2,3), repeat=m):
                    for n in (4,8):
                        table = [[profile(d,k,sigma,n,s,t) for t in probes] for s in probes]
                        check(recover(d,table,n,m) == (k,sigma), 'polarized reconstruction', (name,m,k,sigma,n))
                        subtotal += 1
        recoveries[name] = subtotal
        count['polarized_reconstructions'] += subtotal
    # Negative controls: both conditions of the fusion-ring theorem matter.
    imprimitive = ((0,1),(1,0))
    di = moments(imprimitive,3)
    check(rank(imprimitive)==2 and di[1]*di[3]-di[2]**2==0 and primitive(imprimitive) is None, 'period-two exclusion')
    not_regular_rep = ((2,2,2),(2,3,1),(2,1,3))
    dn = moments(not_regular_rep,3)
    check(primitive(not_regular_rep)==1 and rank(not_regular_rep)==2 and dn[1]*dn[3]-dn[2]**2==0, 'root not spectrally faithful')
    count['hypothesis_negative_controls'] += 2
    # An unpolarized Fib table cannot distinguish directions; regular data cannot recover.
    check(df[7]*df[5] == df[5]*df[7], 'direction ambiguity')
    regular_d = moments(lincomb((1,1),z2),15)
    check(all(regular_d[t+1]*regular_d[t-1]==regular_d[t]**2 for t in range(2,14)), 'regular blindness')
    count['diagnostic_negative_controls'] += 2
    sample_k, sample_sigma, sample_n = (1,-1),(1,0),4
    probes = [(0,0),(1,0),(0,1)]
    sample_table = [[profile(df,sample_k,sample_sigma,sample_n,s,t) for t in probes] for s in probes]
    return {'status':'passed', 'arithmetic':'exact integers and Fraction',
            'counts':dict(sorted(count.items())), 'accepted_fusion_objects':dict(accepted),
            'polarized_by_model':recoveries,
            'sample':{'model':'Fib','n':sample_n,'k':sample_k,'sigma':sample_sigma,'table':sample_table,
                      'recovered':recover(df,sample_table,sample_n,2)},
            'negative_primitive_matrix':{'matrix':not_regular_rep,'moments_1_3':dn[1:4],'rank':rank(not_regular_rep)},
            'scope':'Finite diagnostics only. No category construction, DHR/FDQC proof, Lean compilation, CI or independent review.'}


if __name__ == '__main__':
    print(json.dumps(run(), ensure_ascii=False, indent=2))
