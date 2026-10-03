#!/usr/bin/env python3
"""Exact ordinary certificates for a fixed leaf-core/full-inventory LP.

No LP optimality or unrestricted Erdos7 claim. All fields describe actual
selected congruences, one product source and fixed decreasing Boolean cores.
"""
import argparse
from fractions import Fraction as F
from functools import lru_cache
from math import comb, factorial, isqrt, prod
from pathlib import Path
import json

LEAVES = (4, 7, 2, 5, 8)
HEAD = (5, 7, 11, 13, 17, 19, 23)
CHECKS = 0


def need(ok, label):
    global CHECKS
    CHECKS += 1
    if not ok:
        raise ValueError(label)


def pairs_unique(items):
    obj = {}
    for key, value in items:
        if key in obj:
            raise ValueError('duplicate JSON key '+key)
        obj[key] = value
    return obj


def read(path):
    return json.loads(path.read_text(), object_pairs_hook=pairs_unique)


def a4(p):
    t = F(1, p-1)
    return 15*t+50*t*t+60*t**3+24*t**4


def tail_allowances():
    delta, r, ell, B = F(2,7), 21, 7, 3000
    C = F(27,256)/(delta**3*(1-delta))
    need(B >= 286 and ell >= 4 and 3**ell <= B and 4*ell >= r,
         'complete analytic tail premises')
    need(all(F(x)/(1-delta) <= comb(r,i) for i,x in enumerate((15,50,60,24),1)),
         'complete quartic growth polynomial')
    series = sum((F(factorial(r),factorial(r-j)*(3*ell)**j) for j in range(r+1)),F(0))
    analytic = C/3*F(99,97)**r*F(B,(B-1)**4)*series
    primes = [p for p in range(1601,3001) if all(p%d for d in range(2,isqrt(p)+1))]
    total = analytic
    scale = 10**30
    for p in reversed(primes):
        raw = C/F((p-1)**4)+(1+a4(p)/(1-delta))*total
        total = F(-((-raw.numerator*scale)//raw.denominator),scale)
        need(F(0) <= total-raw < F(1,scale), 'finite bridge rounds upward')
    need(len(primes) == 179 and total == F(4301685063112470380207,10**30),
         'source-independent Report804 allowance')
    return {'3000':analytic,'1600':total}


def core_polynomials(cores, n):
    need(len(cores) == 5, 'five fixed leaf cores')
    out = []
    size = 1 << n
    for allowed in cores:
        need(allowed == sorted(set(allowed)) and all(type(x) is int and 0 <= x < size for x in allowed),
             'literal finite Boolean core')
        table = [int(mask in allowed) for mask in range(size)]
        need(all(not table[mask] or table[mask^(1<<i)]
                 for mask in range(size) for i in range(n) if mask>>i&1),
             'decreasing core under every one-bit removal')
        coefficients = table[:]
        for i in range(n):
            for mask in range(size):
                if mask>>i&1:
                    coefficients[mask] -= coefficients[mask^(1<<i)]
        out.append(coefficients)
    return out


def responses(polys, t):
    n, size = len(t), 1<<len(t)
    monomial = [F(1)]*size
    for mask in range(1,size):
        bit = mask & -mask
        monomial[mask] = monomial[mask^bit]*t[bit.bit_length()-1]
    result = []
    for poly in polys:
        subtotal = [poly[s]*monomial[s] for s in range(size)]
        for i in range(n):
            for mask in range(size):
                if mask>>i&1:
                    subtotal[mask] += subtotal[mask^(1<<i)]
        row = [subtotal[(size-1)^D] for D in range(size)]
        need(all(F(0) <= v <= 1 for v in row), 'actual Boolean response probabilities')
        result.append(row)
    return result


def inventory(primes, selected):
    size = 1<<len(primes)
    beta = [prod((F(1,q-2) for i,q in enumerate(primes) if D>>i&1),start=F(1))
            for D in range(size)]
    rem = [[beta[D] if D and (h or D.bit_count()>1) else F(0)
            for D in range(size)] for h in range(3)]
    records = []
    need(len(selected) == len({m for m,a in selected}), 'distinct actual numerical moduli')
    for m, residue in selected:
        need(type(m) is int and type(residue) is int and m>1 and 0<=residue<m and m%2,
             'odd nonunit original and literal phase')
        h, cofactor = 0, m
        while cofactor%3 == 0:
            h, cofactor = h+1, cofactor//3
        support, leftover = 0, cofactor
        for i,q in enumerate(primes):
            if leftover%q == 0:
                support |= 1<<i
                while leftover%q == 0:
                    leftover //= q
        need(leftover == 1 and cofactor>1 and h<=2 and (h or support.bit_count()>=2),
             'original selected from the declared shallow mixed inventory')
        cost = prod((F(q-1,q-2) for i,q in enumerate(primes) if support>>i&1),start=F(1))/cofactor
        rem[h][support] -= cost
        records.append((m,residue,h,support,cost))
    need(all(x>=0 for row in rem for x in row), 'complete residual inventories nonnegative')
    return beta, rem, records


def forced_zero_leaves(primes, references, cores, records):
    forced, witnesses = set(), []
    for m,residue,h,D,cost in records:
        hit = sum(1<<i for i,q in enumerate(primes) if D>>i&1 and residue%q == references[i])
        for leaf,value in enumerate(LEAVES):
            if value%3**h == residue%3**h and hit in cores[leaf]:
                forced.add(leaf)
                witnesses.append(dict(modulus=m,leaf_index=leaf,leaf=value,fixed_hit_mask=hit))
    return sorted(forced), witnesses


def source_value(w, A, beta, rem):
    rows = []
    for D in range(len(beta)):
        weighted = [w[l]*A[l][D] for l in range(5)]
        F0 = sum(weighted,F(0))
        root = max(sum(weighted[:2],F(0)),sum(weighted[2:],F(0)))
        leaf = max(weighted)
        rows.append((F0,root,leaf))
    mass = rows[0][0]
    high = sum((beta[D]*rows[D][2]/2 for D in range(len(beta))),F(0))
    shallow = sum((rem[h][D]*rows[D][h] for D in range(len(beta)) for h in range(3)),F(0))
    # Every root/leaf epigraph is represented at its exact minimum.
    need(all(rows[D][1] >= sum((w[l]*A[l][D] for l in root),F(0))
             for D in range(len(beta)) for root in ((0,1),(2,3,4))), 'LP root epigraph rows')
    need(all(rows[D][2] >= w[l]*A[l][D] for D in range(len(beta)) for l in range(5)),
         'LP leaf epigraph rows')
    return dict(core=str(mass),high_loss=str(high),shallow_loss=str(shallow),
                lower_bound=str(mass-high-shallow))


def hinge_coefficients(primes,h):
    @lru_cache(None)
    def pmf(k,n):
        if k == 0:
            return F(n==1)
        q = primes[k-1]
        C = F(q-1,q-2)
        def tail(e):
            return F(1) if e==0 else C/q**e
        return sum(((tail(d-1)-tail(d))*pmf(k-1,n//d)
                    for d in range(1,n+1) if n%d==0),F(0))
    mean = prod((1+F(1,q-2) for q in primes),start=F(1))
    H0, Hr, Hv = mean-h, mean, 3*mean/2
    for n in range(1,h):
        p1 = pmf(len(primes),n)
        p2 = pmf(len(primes),n//2) if n%2==0 else F(0)
        pv = sum((F(2,3**(d-2))*pmf(len(primes),n//d)
                  for d in range(3,n+1) if n%d==0),F(0))
        H0 += (h-n)*p1
        Hr += (h-n)*(p2-p1)
        Hv += (h-n)*(pv-p2)
    need(H0>=0 and Hr>=0 and Hv>=0, 'nonnegative affine complete-hinge coefficients')
    return H0,Hr,Hv


def fixed_case(case,tails):
    primes = tuple(case['primes'])
    need(primes in ((5,),HEAD), 'declared example head')
    n, size = len(primes), 1<<len(primes)
    w = tuple(map(F,case['weights']))
    need(len(w)==5 and all(x>=0 for x in w) and sum(w)==1, 'one fixed normalized source law')
    references = case['references']
    need(len(references)==n and all(type(c) is int and 0<=c<q for c,q in zip(references,primes)),
         'one common first-digit reference per coordinate')
    cores = case['cores']
    polys = core_polynomials(cores,n)
    beta,rem,records = inventory(primes,case['selected'])
    forced,witnesses = forced_zero_leaves(primes,references,cores,records)
    need(all(w[l]==0 for l in forced), 'actual selected-cylinder nullity weight constraints')
    u = tuple(F(q-1,q*(q-2)) for q in primes)
    vertices = []
    for mask in range(size):
        t = tuple(u[i] if mask>>i&1 else F(0) for i in range(n))
        vertices.append(dict(mask=mask,**source_value(w,responses(polys,t),beta,rem)))
    worst = min(range(size),key=lambda i:F(vertices[i]['lower_bound']))
    alpha_box = F(vertices[worst]['lower_bound'])
    # These controls support, but do not substitute for, the general concavity proof.
    midpoint = tuple(x/2 for x in u)
    center = F(source_value(w,responses(polys,midpoint),beta,rem)['lower_bound'])
    for i in range(n):
        low,high = list(midpoint),list(midpoint)
        low[i],high[i] = F(0),u[i]
        L = F(source_value(w,responses(polys,low),beta,rem)['lower_bound'])
        U = F(source_value(w,responses(polys,high),beta,rem)['lower_bound'])
        need(2*center>=L+U, 'fixed-weight separate concavity midpoint')
    haar = source_value(w,responses(polys,tuple(F(1,q) for q in primes)),beta,rem)
    r,v = max(sum(w[:2],F(0)),sum(w[2:],F(0))),max(w)
    h = case['threshold']
    need(type(h) is int and 0<=h<28, 'fixed integer complete-hinge threshold')
    H0,Hr,Hv = hinge_coefficients(primes,h)
    hinge = H0+Hr*r+Hv*v
    Kq = prod((1+F(q-1,q-2)*a4(q) for q in primes),start=F(1))*(1+F(28,27)*a4(29))
    Kbase = Kq*(1+15*r+216*v)
    continuation = []
    for source_name,alpha in (('full_box',alpha_box),('actual_haar',F(haar['lower_bound']))):
        for cutoff,T in tails.items():
            gate = (28-h)*alpha-hinge-27*Kbase*T
            record = dict(source=source_name,cutoff=int(cutoff),gate=str(gate),gate_decimal=float(gate))
            if alpha>0:
                reserve = gate/(27*alpha)
                direct = (28-h-hinge/alpha)/27-Kbase*T/alpha
                need(reserve==direct, 'LP margin equals same-source distorted reserve times27alpha')
                record.update(reserve=str(reserve),reserve_decimal=float(reserve))
            continuation.append(record)
    return dict(name=case['name'],forced_zero_leaves=forced,nullity_witnesses=witnesses,
                weights=list(map(str,w)),vertices=vertices,worst_vertex=worst,
                alpha_box=str(alpha_box),haar=haar,r=str(r),v=str(v),threshold=h,
                hinge_coefficients=list(map(str,(H0,Hr,Hv))),hinge=str(hinge),
                fourth_product_without_ternary=str(Kq),fourth_product=str(Kbase),
                continuation=continuation)


def literal_small_example(case):
    need(case['primes']==[5] and case['references']==[0], 'small actual carrier')
    w = tuple(map(F,case['weights']))
    originals = [(3,0),(9,1)] + [tuple(x) for x in case['selected']]
    need(originals==[(3,0),(9,1),(15,10),(45,20)], 'same fixed four actual originals')
    retained, survivor, root_constant = F(0),F(0),F(0)
    survivors = []
    for x in range(45):
        if x%9 not in LEAVES:
            continue
        leaf = LEAVES.index(x%9)
        atom = w[leaf]/5
        hit = int(x%5==0)
        in_core = hit in case['cores'][leaf]
        alive = all(x%m!=a for m,a in originals)
        need(not in_core or alive, 'literal selected core is supported on actual survivor')
        if in_core:
            retained += atom
        if alive:
            survivor += atom
            survivors.append(x)
        if not hit:
            root_constant += atom
    need(retained==survivor==F(22,25), 'exact leaf-dependent survivor mass22/25')
    need(root_constant==F(4,5) and retained-root_constant==F(2,25), 'root-constant loss2/25')
    # Deliberately dropping the 45-to-leaf2 incidence imposes weight2=0.
    forgotten = [[0],[0],[0,1],[0,1],[0,1]]
    _,_,records = inventory((5,),case['selected'])
    forced,witnesses = forced_zero_leaves((5,),(0,),forgotten,records)
    need(forced==[2] and w[2]>0, 'LP must retain the actual selected45 nullity constraint')
    return dict(originals=[list(pair) for pair in originals],period=45,survivors=survivors,
                leaf_core_mass=str(retained),root_constant_max_mass=str(root_constant),
                strict_gain=str(retained-root_constant),forgotten_incidence_forced_zero=forced,
                forgotten_incidence_witnesses=witnesses)


def deeper_prefix_control():
    rows=[]
    for hole in (1,6):
        allowed=[x for x in range(25) if x!=hole]
        hit=F(sum(x%5==0 for x in allowed),len(allowed))
        selected=F(2,5)*F(int(1 in allowed),len(allowed))
        rows.append(dict(pure_original=[25,hole],first_hit=str(hit),
                         selected_original=[75,1],selected_mass=str(selected)))
    need(rows[0]['first_hit']==rows[1]['first_hit']=='5/24', 'same observed first-hit probability')
    need(rows[0]['selected_mass']=='0' and rows[1]['selected_mass']=='1/60',
         'different actual selected leakage at the same first-hit reading')
    return rows


def calculate(cert):
    global CHECKS
    CHECKS = 0
    need(cert['schema']=='leaf-core-linear-bridge-v1','certificate schema')
    need(cert['leaves']==list(LEAVES),'one common normalized ternary carrier')
    need(len(cert['cases'])==2,'two fixed examples, no weight optimization')
    tails = tail_allowances()
    rows = [fixed_case(case,tails) for case in cert['cases']]
    actual = literal_small_example(cert['cases'][0])
    need(F(rows[0]['alpha_box'])==F(49,75),'toy complete-inventory box source')
    need(F(rows[1]['haar']['lower_bound'])==F(102428997125209,2365431391323000),
         'seven-prime same-law root-conflict source')
    need(any(x['source']=='actual_haar' and x['cutoff']==1600 and F(x['reserve'])>F(3,25)
             for x in rows[1]['continuation']), 'fixed conflicting-phase family retains more than3/25')
    witness = cert['cases'][1]['uncovered_integer']
    need(witness%3!=0 and witness%9!=1 and all(witness%m!=a for m,a in cert['cases'][1]['selected']),
         'one actual integer avoids the full fixed25-original conflict example')
    hidden=deeper_prefix_control()
    return dict(schema='leaf-core-linear-bridge-result-v1',check_count=CHECKS,
                scope='Ordinary fixed-core LP reduction and exact primal evaluations. No LP optimum, no universal existence of a positive source, and no Lean or unrestricted Erdos7 conclusion.',
                tail_methods={'3000':'Report734 HM15, B=3000 ell=7 delta=2/7 growth=21',
                              '1600':'Report804 complete179-prime finite bridge to the full analytic tail above3000'},
                tail_allowances={k:str(v) for k,v in tails.items()},cases=rows,literal_small_example=actual,
                same_first_hit_different_deep_leakage=hidden)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate',type=Path,required=True)
    group=parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--result',type=Path)
    group.add_argument('--write-result',type=Path)
    args=parser.parse_args()
    try:
        result=calculate(read(args.certificate))
        if args.write_result:
            args.write_result.write_text(json.dumps(result,indent=2,allow_nan=False)+'\n')
        else:
            need(read(args.result)==result,'exact retained result replay')
        print(json.dumps(dict(check_count=result['check_count'],
                              leaf_core_mass=result['literal_small_example']['leaf_core_mass'],
                              root_constant_max_mass=result['literal_small_example']['root_constant_max_mass'],
                              sources=[dict(name=x['name'],alpha_box=x['alpha_box'],
                                            alpha_haar=x['haar']['lower_bound'],
                                            tail_reserves=[{k:y[k] for k in ('source','cutoff','reserve_decimal')}
                                                           for y in x['continuation']])
                                       for x in result['cases']]),indent=2))
    except (ValueError,KeyError,TypeError,IndexError,ZeroDivisionError,OSError) as exc:
        parser.exit(1,'REJECTED: '+str(exc)+'\n')


if __name__=='__main__':
    main()
