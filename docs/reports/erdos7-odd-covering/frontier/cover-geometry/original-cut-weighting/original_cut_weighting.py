#!/usr/bin/env python3
"""Exact original-label cut counts, source-preserving weights and noncovers.

Default: current prime7, heights1,2,3,29, plus the two-group bias example
at height5. Uses only the Python3.9+ standard library, exact integers and
Fractions. Safe under python3 -I -S -O from any working directory.
No external modules or certificate files are read or written. These are
finite checks of specified actual distinct-odd-modulus noncovers, not a
whole-cover theorem, a uniform-family bound, or a Lean verification.
"""
import argparse
from fractions import Fraction as F
from itertools import product
from math import prod
import sys

sys.dont_write_bytecode = True


def require(ok, message):
    if not ok:
        raise ValueError(message)


def crt(pairs):
    value, modulus = 0, 1
    for residue, factor in pairs:
        value += modulus * ((residue-value) * pow(modulus, -1, factor) % factor)
        modulus *= factor
    return value % modulus


def is_prime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d*d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def make_family(p, height, second_copy=False):
    require(is_prime(p) and p >= 7, 'Current prime must be at least7; old primes are3 and5')
    require(height >= 1, 'Current height must be positive')
    main = (p, 0) + tuple(range(2, p))
    labels = []
    for e in range(1, height+1):
        digits = range(p) if e == height else range(1, p)
        for digit in digits:
            j = main[digit]
            labels.append((j, p-j, 0, e, digit*p**(e-1)))
        if e < height:
            labels.append((1, p-1, 0, e, p**(e-1)))
    if second_copy:
        for digit, j in enumerate(main):
            labels.append((j+1, p-j+1, 1, 1, digit))
    out = []
    for a, b, center, e, residue in labels:
        old = 3**a * 5**b
        d = old*p**e
        r = crt(((center, old), (residue, p**e)))
        require(d > 1 and d % 2 == 1 and r % old == center % old
                and r % (p**e) == residue,
                'Literal legal odd original CRT class')
        out.append(dict(a=a, b=b, center=center, e=e, y=residue, d=d, r=r))
    require(len(out) == p*(height+int(second_copy)), 'Exact original-label inventory')
    require(len({c['d'] for c in out}) == len(out), 'All original (d,e) slots unique')
    return out


def cut_tree(labels, p):
    nodes = {(0, 0): []}
    for i, c in enumerate(labels):
        nodes.setdefault((c['e'], c['y']), []).append(i)
        for depth in range(c['e']):
            parent = c['y'] % (p**depth)
            nodes.setdefault((depth, parent), [])
            for digit in range(p):
                nodes.setdefault((depth+1, parent+digit*p**depth), [])
    return nodes


def cut_count_and_weighting(labels, nodes, p, x3, x5):
    """One old row: exact count, normalized cut mass, and label-selection flow."""
    count = {}
    active_labels = {}
    norm = {}
    for depth, residue in sorted(nodes, reverse=True):
        active = [i for i in nodes[depth, residue]
                  if x3 % (3**labels[i]['a']) == labels[i]['center'] % (3**labels[i]['a'])
                  and x5 % (5**labels[i]['b']) == labels[i]['center'] % (5**labels[i]['b'])]
        active_labels[depth, residue] = active
        children = [(depth+1, residue+digit*p**depth) for digit in range(p)]
        continuation = prod(count[w] for w in children) if all(w in count for w in children) else 0
        W = len(active)+continuation
        count[depth, residue] = W
        require(W <= 2**len(labels), 'Every labelled cut is a subset of the original inventory')
        if W:
            continuing_norm = prod(norm[w] for w in children) if continuation else F(0)
            norm[depth, residue] = F(len(active), W)+F(continuation, W)*continuing_norm
            require(norm[depth, residue] == 1, 'Uniform conditional cut kernel has total mass one')
        else:
            norm[depth, residue] = F(0)
    Wroot = count[0, 0]
    # Missing certificates use a failure symbol. Keeping this branch preserves
    # the old measure instead of silently conditioning it on full fibre coverage.
    require(norm[0, 0]+int(Wroot == 0) == 1, 'The old point marginal is preserved')
    reach = {(0, 0): F(int(Wroot > 0))}
    selected = [F(0) for _ in labels]
    for depth, residue in sorted(nodes):
        probability = reach.get((depth, residue), F(0))
        if not probability:
            continue
        W = count[depth, residue]
        require(W > 0, 'No positive transition to an empty certificate family')
        for i in active_labels[depth, residue]:
            selected[i] = probability/W
        children = [(depth+1, residue+digit*p**depth) for digit in range(p)]
        continuation = prod(count[w] for w in children) if all(w in count for w in children) else 0
        if continuation:
            for child in children:
                reach[child] = probability*F(continuation, W)
    require(all(0 <= q <= 1 for q in selected), 'Actual original-label selection probabilities')
    require(sum((q/F(p**c['e']) for q,c in zip(selected,labels)), F(0)) == int(Wroot > 0),
            'Exact expected Kraft budget of the source-preserving cut kernel')
    return Wroot, norm[0, 0]


def axis_partition(prime, targets):
    branches = {(depth, residue % (prime**depth))
                for exponent, residue in targets for depth in range(exponent)}
    def walk(depth, residue):
        if (depth, residue) not in branches:
            return [(residue, F(1, prime**depth))]
        out = []
        for digit in range(prime):
            out += walk(depth+1, residue+digit*prime**depth)
        return out
    out = walk(0, 0)
    require(sum(w for _, w in out) == 1, 'Full old-axis partition')
    for i,(residue,weight) in enumerate(out):
        require(weight.numerator == 1, 'A literal Haar prefix-cylinder weight')
        modulus = weight.denominator
        for other,other_weight in out[i+1:]:
            require((residue-other) % min(modulus,other_weight.denominator) != 0,
                    'Old partition cylinders are pairwise disjoint')
        for exponent,target in targets:
            require(prime**exponent <= modulus or (residue-target) % modulus != 0,
                    'Every original old-coordinate condition is constant on each atom')
    return out


def verify(p, height, second_copy=False):
    labels = make_family(p, height, second_copy)
    nodes = cut_tree(labels,p)
    old_height = p+int(second_copy)
    for i, c in enumerate(labels):
        # Exact valuations about the class center isolate its antichain cofactor.
        # Different centers are already disjoint in an old prime coordinate.
        x3 = c['center']+(3**c['a'] if c['a'] < old_height else 0)
        x5 = c['center']+(5**c['b'] if c['b'] < old_height else 0)
        x = crt(((x3, 3**old_height), (x5, 5**old_height), (c['y'], p**height)))
        hits = [j for j, other in enumerate(labels) if x % other['d'] == other['r']]
        require(hits == [i], 'Every original class has a direct private integer')
    require(all(1 % c['d'] != c['r'] for c in labels) if not second_copy else
            all(2 % c['d'] != c['r'] for c in labels), 'Explicit uncovered integer')
    p3 = axis_partition(3, {(c['a'], c['center'] % (3**c['a'])) for c in labels})
    p5 = axis_partition(5, {(c['b'], c['center'] % (5**c['b'])) for c in labels})
    covered, unnormalized = F(0), F(0)
    first_mass, second_mass = F(0), F(0)
    first_preserved_mass = F(0)
    for (x3,w3),(x5,w5) in product(p3,p5):
        w = w3*w5
        W, conditional_mass = cut_count_and_weighting(labels,nodes,p,x3,x5)
        in_first = x3 % 3**p == 0 and x5 % 5**p == 0
        in_second = second_copy and x3 % 3**(p+1) == 1 and x5 % 5**(p+1) == 1
        expected = 2**(height-1)*in_first + int(in_second)
        require(W == expected, 'Exact full-cut count on every old-observation atom')
        covered += w*(W>0)
        unnormalized += w*W
        first_mass += w*in_first
        second_mass += w*in_second
        first_preserved_mass += w*in_first*conditional_mass
    require(first_mass == F(1,15**p), 'First full-fibre event has height-independent mass')
    require(second_mass == (F(1,15**(p+1)) if second_copy else F(0)), 'Second full-fibre event')
    require(covered == first_mass+second_mass and unnormalized == 2**(height-1)*first_mass+second_mass,
            'Old Haar mass versus certificate counting mass')
    if second_copy:
        original_first = first_mass/covered
        counting_first = (2**(height-1)*first_mass)/unnormalized
        require(original_first == F(15,16), 'Uniform covered-old support original marginal')
        require(counting_first == F(15*2**(height-1),15*2**(height-1)+1), 'Exact counting-induced old bias')
        require(first_preserved_mass/covered == original_first, 'Pointwise1/W preserves the chosen old source')
    else:
        require(unnormalized/covered == 2**(height-1), 'Exponential full-cut multiplicity')
    print('PASS',dict(p=p,H=height,second_copy=second_copy,labels=len(labels),
          private_membership_checks=len(labels)**2,old_atoms=len(p3)*len(p5),
          full_fibre_mass=str(covered),cut_count_mass=str(unnormalized)))
    if second_copy:
        print('PASS old marginal:',str(original_first),'preserved by1/W;',
              'unweighted counting gives',str(counting_first))


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--current-prime',type=int,default=7,help='Current prime>=7 (default7)')
    parser.add_argument('--heights',type=int,nargs='+',default=[1,2,3,29],
                        help='Positive single-group current heights (default1 2 3 29)')
    parser.add_argument('--bias-height',type=int,default=5,help='Positive two-group height (default5)')
    args = parser.parse_args()
    for height in args.heights:
        verify(args.current_prime,height)
    verify(args.current_prime,args.bias_height,True)
    print('PASS finite exact checks; all constructed original families are noncovers; no Lean result')


if __name__ == '__main__':
    main()
