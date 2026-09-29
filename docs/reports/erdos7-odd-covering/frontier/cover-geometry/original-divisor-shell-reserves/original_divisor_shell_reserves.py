#!/usr/bin/env python3
"""Exact literal-period controls for original-class shell reserves.

The full family and same-cover reserve inequality are proved in the Lettl--Sun
library note. These even-cover controls do not resolve odd noncoverage."""
from fractions import Fraction as F
from math import gcd, lcm
import json
from pathlib import Path


def require(value, message):
    if not value:
        raise ValueError(message)


def factors(n):
    out = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        out[n] = 1
    return out


def cylinder(a, m, L):
    # Bit i is the actual residue i, not an abstract phase.
    return sum(1 << i for i in range(a % m, L, m))


def build(p, q, b):
    require(factors(p) == {p:1} and factors(q) == {q:1} and p > 2 and q > 2,
            'distinct odd prime parameter types')
    A, B, C = p - 1, q - b, b
    require(p != q and 2 <= b <= min(A, q // 2), 'parameter domain')
    h = max(A, B) - 1
    out = []
    for j in range(1, h + 1):
        out.append((f'D{j}', 2 ** (j - 1), 2 ** j))
    for name, prime, N in [('P', p, A), ('Q', q, B)]:
        for i in range(1, N + 1):
            power = 2 ** (i - 1)
            a = power * (i * pow(power, -1, prime) % prime)
            out.append((f'{name}{i}', a, power * prime))
    for k in range(1, C + 1):
        gamma = 0 if k == 1 else B + k - 1
        base = p * (gamma * pow(p, -1, q) % q)
        power = 2 ** (k - 1)
        a = power * (base * pow(power, -1, p * q) % (p * q))
        out.append((f'T{k}', a, power * p * q))
    return out, 2 ** h * p * q, h


def inspect(classes, L):
    require(lcm(*(m for _, _, m in classes)) == L, 'exact period')
    moduli = [m for _, _, m in classes]
    require(len(set(moduli)) == len(moduli), 'distinct moduli')
    require(all(m > 1 for m in moduli), 'nonunit moduli')
    for m in moduli:
        require(all(d in moduli for d in range(2, m + 1) if m % d == 0),
                f'divisor closure {m}')
    masks = {name: cylinder(a, m, L) for name, a, m in classes}
    covered = overlap = 0
    for mask in masks.values():
        overlap |= covered & mask
        covered |= mask
    require(covered == (1 << L) - 1, 'whole coverage')
    private = {name: mask & ~overlap for name, mask in masks.items()}
    require(all(private.values()), 'irredundancy')
    mass = {name: F(mask.bit_count(), L) for name, mask in private.items()}
    data = {name: (a, m) for name, a, m in classes}
    columns = {}
    containing = {}
    entries = {}
    for s, a, m in classes:
        disjoint = 0
        for p, e in factors(m).items():
            d = m // p ** e
            for r in range(e):
                c = (s, p, r)
                n, nn = d * p ** r, d * p ** (r + 1)
                mask = cylinder(a, n, L) & ~cylinder(a, nn, L)
                alpha, cap = F(1, p ** (e - r - 1)), F(p - 1, m)
                require(not (disjoint & mask), f'supplier shell disjointness {c}')
                require(not (masks[s] & mask), f'self exclusion {c}')
                disjoint |= mask
                require(alpha * F(mask.bit_count(), L) == cap, f'capacity {c}')
                columns[c] = (mask, alpha, cap)
                containing[c] = set()
                for t, at, mt in classes:
                    entry = alpha * F((private[t] & mask).bit_count(), L)
                    entries[t, c] = entry
                    literal = not (masks[t] & ~mask)
                    arith = mt % nn == 0 and (at - a) % n == 0 and (at - a) % nn != 0
                    require(literal == arith, f'general containment criterion {t} {c}')
                    if literal:
                        containing[c].add(t)
                        require(mt % p == 0, 'full containment cannot capture zero p row')
                    if mt % m == 0 and t != s:
                        defect = m // gcd(m, at - a)
                        require(defect > 1, 'divisor irredundancy defect')
                        require(literal == (defect == p ** (e - r)),
                                'divisor defect iff')
                total = sum(entries[t, c] for t in data)
                total += alpha * F((overlap & mask).bit_count(), L)
                require(total == cap, f'complete column {c}')
    rows = [(t, p) for t, _, m in classes for p in factors(m)]
    for t, p in rows:
        service = sum(v for (tt, c), v in entries.items() if tt == t and c[1] == p)
        demand = mass[t] * factors(data[t][1])[p] * (p - 1)
        require(service >= demand, f'integrated Lettl-Sun demand {(t,p)}')
    return dict(classes=classes, L=L, masks=masks, private=private, mass=mass,
                columns=columns, containing=containing, entries=entries, rows=rows)


def cut(state, rows):
    rows = set(rows)
    target = {t for t, p in rows}
    U = sum(state['mass'][t] for t in target)
    record = {}
    total_old = total_new = F(0)
    for s, _, _ in state['classes']:
        bound = U - (state['mass'][s] if s in target else 0)
        old = new = actual = F(0)
        active = []
        for c, (mask, alpha, cap) in state['columns'].items():
            if c[0] != s:
                continue
            chosen = {t for t, p in rows if p == c[1]}
            service = sum(state['entries'][t, c] for t in chosen)
            if not service:
                continue
            forced = state['containing'][c] - chosen
            reserve = alpha * sum(state['mass'][t] for t in forced)
            require(service <= cap - reserve, 'refined column')
            old += cap
            new += cap - reserve
            actual += service
            active.append(dict(column=list(c), capacity=str(cap), reserve=str(reserve),
                               omitted_whole_classes=sorted(forced), service=str(service)))
        require(actual <= min(bound, new), 'refined supplier minimum')
        reserve = old-new
        gain = max(F(0), reserve-max(F(0), old-bound))
        require(gain == min(bound,old)-min(bound,new), 'exact effective reserve after minimum masking')
        total_old += min(bound, old)
        total_new += min(bound, new)
        record[s] = dict(target=str(bound), old=str(old), refined=str(new),
                         old_min=str(min(bound, old)), refined_min=str(min(bound, new)),
                         actual=str(actual), active=active)
    data = {t: m for t, _, m in state['classes']}
    demand = sum(state['mass'][t] * factors(data[t])[p] * (p-1) for t, p in rows)
    require(demand <= total_new <= total_old, 'global refined cut')
    return dict(rows=sorted(rows), demand=str(demand), old=str(total_old),
                refined=str(total_new), suppliers=record)


def run():
    outputs = []
    for p,q,b in [(3,5,2),(3,7,2),(3,11,2),(5,3,1),(5,7,2),(5,7,3),
                  (5,11,2),(5,11,3),(5,11,4),(7,3,1),(7,5,2),(7,11,5),
                  (11,3,1),(11,5,2),(11,7,3)]:
        if b < 2:
            continue
        classes, L, h = build(p,q,b)
        st = inspect(classes, L)
        for k in range(1,b+1):
            t = f'T{k}'
            require(st['private'][t].bit_count() == 1, 'singleton child private region')
            for name, prime in [('P',p),('Q',q)]:
                parent = f'{name}{k}'
                require(t in st['containing'][parent,prime,0], 'actual parent reserve')
            if k>=2:
                require(t in st['containing'][f'D{k-1}',2,k-2], 'grandparent reserve')
        require(len(classes) == 1+h+(p-1)+(q-1), 'global Simpson equality')
        controls = [st['rows']]
        controls += [[r] for r in st['rows']]
        controls += [[r for r in st['rows'] if r[1] == prime] for prime in (2,p,q)]
        for chosen in controls:
            cut(st, chosen)
        out=dict(p=p,q=q,b=b,h=h,L=L,classes=[list(c) for c in classes],
                 private_counts={t:m.bit_count() for t,m in st['private'].items()},
                 columns=len(st['columns']), cut_controls=len(controls))
        if (p,q,b)==(3,5,2):
            supplied=[3,18,4,20,36,12,48,0,24]
            require(all(st['private'][t] & (1<<x) for (t,_,_),x in zip(classes,supplied)),
                    'Nyx supplied private witnesses')
            out['private_residues']={t:[x for x in range(L) if mask>>x&1]
                                     for t,mask in st['private'].items()}
        if (p,q,b)==(5,11,4):
            out['selected_cut']=cut(st,[('D1',2),('Q5',11),('Q6',11),('Q7',11)])
            out['selected_singletons']={t:(mask & -mask).bit_length()-1
                for t,mask in st['private'].items() if t in ['Q5','Q6','Q7','T4']}
        outputs.append(out)
    require(len(outputs) == 12, 'twelve bounded whole-cover controls')
    strict = next(x['selected_cut'] for x in outputs if 'selected_cut' in x)
    supplier = strict['suppliers']['Q4']
    require(F(supplier['old_min']) == F(440,3520) and F(supplier['refined_min']) == F(439,3520),
            'strict original supplier consumer')
    require(F(strict['old']) == F(973,440) and F(strict['refined']) == F(3887,1760)
            and F(strict['demand']) == F(639,1760), 'complete selected-row demand and strict gain')
    return dict(scope='Ordinary exact finite controls; no Lean or unrestricted odd-cover claim.',
                cases=outputs)


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    result = run()
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(cases=len(result['cases']), periods=[c['L'] for c in result['cases']])))


if __name__ == '__main__':
    main()
