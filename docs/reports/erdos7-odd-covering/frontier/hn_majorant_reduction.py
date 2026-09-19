#!/usr/bin/env python3
"""Exact HN presentation-dependence example coupled to the actual 339 head.

Standard library only. Replays the existing 339 producer and compares its
canonical artifact before adjoining the current/future original classes.
"""
import argparse
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
import importlib.util
import json
from math import gcd, prod
from pathlib import Path
import sys
sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/hn_majorant_reduction.json'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Readable source module')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def crt(pairs):
    a, d = 0, 1
    for b, m in pairs:
        if m == 1:
            continue
        require(gcd(d, m) == 1, 'Pairwise coprime CRT factors')
        a += d * (((b-a) * pow(d, -1, m)) % m)
        d *= m
    return a, d


def check_conflict_shearer(residual):
    rows = [(int(a) % int(m), int(m)) for a, m in residual]
    require(len(rows) == 21 and len(set(rows)) == 21,
            'Exactly the actual 21 distinct atomic residual events')
    zero = [i for i, row in enumerate(rows) if row == (0, 13)]
    pure = [i for i, (a, m) in enumerate(rows) if m == 13 and a != 0]
    mixed = [i for i, (a, m) in enumerate(rows) if m == 221]
    require(len(zero) == 1 and len(pure) == 11 and len(mixed) == 9,
            'Actual residual event inventory')
    require({rows[i][0] for i in pure} == set(range(1, 12)),
            'Literal nonzero residues modulo 13')
    require(all(rows[i][0] % 13 == 0 for i in mixed)
            and {rows[i][0] % 17 for i in mixed} == set(range(9)),
            'Literal mixed CRT residues are q=0 and r=0,...,8')
    zero = zero[0]
    adj = [0] * len(rows)
    pair_checks = 0
    for i, (a, m) in enumerate(rows):
        for j in range(i + 1, len(rows)):
            b, n = rows[j]
            conflict = (a - b) % gcd(m, n) != 0
            expected = not ((i == zero and j in mixed)
                            or (j == zero and i in mixed))
            require(conflict == expected, 'Conflict graph reconstructed from literal CRT residues')
            if conflict:
                adj[i] |= 1 << j
                adj[j] |= 1 << i
            pair_checks += 1

    @lru_cache(None)
    def polynomial(mask):
        if not mask:
            return F(1)
        bit = mask & -mask
        i = bit.bit_length() - 1
        rest = mask ^ bit
        return polynomial(rest) - F(1, rows[i][1]) * polynomial(rest & ~adj[i])

    # Pair checks above prove symmetry within each of the two cliques.
    # Every induced subgraph has exactly one of these 12*2*10 types.
    patterns = []
    for k in range(12):
        for delta in range(2):
            for r in range(10):
                chosen = pure[:k] + ([zero] if delta else []) + mixed[:r]
                mask = sum(1 << i for i in chosen)
                direct = polynomial(mask)
                formula = (1 - F(delta, 13)) * (1 - F(r, 221)) - F(k, 13)
                require(direct == formula and direct > 0,
                        'Every induced type has its exact positive independence polynomial')
                patterns.append(direct)
    full = polynomial((1 << len(rows)) - 1)
    require(len(patterns) == 240 and min(patterns) == full == F(113, 2873),
            'Uniform minimum over all induced subgraphs')
    survivors = [z for z in range(11 * 221)
                 if all(z % m != a for a, m in rows)]
    require(F(len(survivors), 11 * 221) == F(1, 13) >= full,
            'Actual residual Haar avoidance dominates its Shearer lower bound')
    for b in range(11):
        neighbors = [i for i, (a, m) in enumerate(rows)
                     if (b - a) % gcd(11, m) != 0]
        require(not neighbors, 'Each remaining current digit has no conflicting future event')
        actual = F(sum(z % 11 == b for z in survivors), len(survivors))
        cap = F(1, 11) * polynomial((1 << len(rows)) - 1) / full
        require(actual == cap == F(1, 11), 'Exact conditional Haar digit and Shearer query cap')
    return dict(vertices=len(rows), literal_crt_pair_checks=pair_checks,
                edges=sum(bin(a).count('1') for a in adj) // 2,
                induced_types=len(patterns), minimum_induced_polynomial=str(full),
                exact_future_hole='1/13', conditional_current_leaf_cap='1/11',
                residual_period_checks=11 * 221,
                scope='Conditional original Haar law; no universal feasibility claim')


def calculate(base):
    head_program = base/'frontier/irredundant_whole_j_finite_source.py'
    head_proof = base/'profile-notes/339-irredundant-source-seven-labels-bound-the-actual-surplus.md'
    head_artifact = base/'certificates/source_norms/irredundant_whole_j_finite_source.json'
    producer = module('hn_majorant_actual_head', head_program)
    io, head = producer.calculate(base, head_proof, 12)
    artifact_bytes = io.read_artifact_bytes(head_artifact)
    stored = json.loads(artifact_bytes, object_pairs_hook=io._unique)
    require(head == stored, 'Actual 339 source replay agrees with the complete canonical certificate')
    require(head['original_label_count'] == 204, 'Exactly the existing 204 original head labels')
    require(F(head['mass']['delta']) < F(1,4000), 'Actual source high-qJ condition')
    require(F(head['mass']['rho']) < F(head['mass']['same_delta_339_upper']) < F(7,100),
            'Actual source remains in the nonempty low-rho region')
    p, q, r, height, depth = 11, 13, 17, 12, 11
    future = []
    for e in range(11):
        a, d = crt([(0,p**e),(e+1,q)])
        future.append(dict(kind='pure-future',depth=e,residue=a,modulus=d,
                           q_residue=e+1,r_residue=None))
    a,d = crt([(0,p**11),(0,q)])
    future.append(dict(kind='pure-future',depth=11,residue=a,modulus=d,
                       q_residue=0,r_residue=None))
    for e in range(9):
        a,d = crt([(0,p**e),(0,q),(e,r)])
        future.append(dict(kind='mixed-future',depth=e,residue=a,modulus=d,
                           q_residue=0,r_residue=e))
    require(len(future) == 21, 'Exactly 21 future original labels')
    current = dict(kind='current',residue=1,modulus=p**height)
    originals = [dict(kind='head',residue=c['residue'],modulus=c['modulus'])
                 for c in head['original_forbidden_classes']] + [current] + future
    require(len(originals) == len(set(c['modulus'] for c in originals)) == 226,
            'All 226 original moduli remain distinct')
    require(all(c['modulus']>1 and c['modulus']%2 for c in originals), 'Odd nontrivial moduli')
    contained_pairs = []
    for i,c in enumerate(originals):
        for j,d in enumerate(originals):
            if i != j and c['modulus']%d['modulus']==0 and (c['residue']-d['residue'])%d['modulus']==0:
                contained_pairs.append((i,j))
    require(not contained_pairs, 'No full original class containment')
    old_period = 105**12
    old_uncovered = head['uncovered_integer']
    private = []
    for target,c in enumerate(originals):
        if target < 204:
            old = head['private_integer_witnesses'][target]['private_integer']
            xp,xq,xr = 2,12,16
        elif target == 204:
            old = old_uncovered
            xp,xq,xr = 1,12,16
        else:
            old = old_uncovered
            f = future[target-205]
            if f['kind']=='pure-future':
                xp = 0
                xq,xr = f['q_residue'],16
            else:
                e = f['depth']
                xp = 2 if e==0 else p**e
                xq,xr = 0,f['r_residue']
        witness,period = crt([(old,old_period),(xp,p**height),(xq,q),(xr,r)])
        members = [j for j,other in enumerate(originals)
                   if witness%other['modulus']==other['residue']]
        require(members == [target], 'Private witness checked against every original class')
        private.append(str(witness))
    uncovered,_ = crt([(old_uncovered,old_period),(2,p**height),(12,q),(16,r)])
    require(all(uncovered%c['modulus'] != c['residue'] for c in originals), 'Actual noncover witness')
    # At J=0 mod p^11 every original p-condition of a future class holds.
    # Use remaining p digit and the actual q/r prime coordinates as CRT axes.
    residual = []
    grouped = {}
    label_containments = []
    for k,f in enumerate(future):
        m = f['modulus']//(p**f['depth'])
        a = f['residue']%m
        residual.append((a,m))
        grouped.setdefault(m,set()).add(a)
        majorant_residue = f['residue']%q
        require(0<=majorant_residue<=11, 'Every future class contained in its q-majorant')
        require(f['modulus']%q==0, 'Majorant divisibility certificate')
        label_containments.append(dict(original_future_index=k,
             majorant_modulus=q,majorant_residue=majorant_residue,
             modulus_quotient=f['modulus']//q))
    require(grouped[q] == set(range(12)) and len(grouped[q*r])==9,
            'Literal residual events have the prescribed cardinalities')
    for a in grouped[q*r]:
        require(a%q==0 and a%r in range(9), 'Every residual mixed event is contained in q=0')
    union_checks = 0
    for last_p in range(p):
        actual_p = last_p*p**depth
        for xq in range(q):
            for xr in range(r):
                word,_ = crt([(actual_p,p**height),(xq,q),(xr,r)])
                actual = any(word%f['modulus']==f['residue'] for f in future)
                reduced = xq in range(12)
                require(actual == reduced, 'Conditional exact-union reduction')
                union_checks += 1
    # Necessary inequalities for the literal two-modulus HN presentation:
    # xi_q >= q-1; hence xi_r >= 9/(r-9), while the q constraint
    # simultaneously forces xi_r < (r-9)/9. Their separation is exact.
    lower_r,strict_upper_r = F(9,8),F(8,9)
    require(lower_r > strict_upper_r, 'Rational certificate separates necessary HN bounds')
    majorant_weight = F(12)
    require(F(12,13)*(1+majorant_weight)==majorant_weight,
            'Reduced HN q constraint is an equality')
    # All majorants have no p part, so the empty p test has xi_p=0.
    result = dict(
        schema='hn-conditional-majorant-v1',
        head=dict(certificate_sha256=sha256(artifact_bytes).hexdigest(),
                  source_program_sha256=sha256(io.read_artifact_bytes(head_program)).hexdigest(),
                  original_count=204,period=str(old_period),mass=head['mass'],
                  replay='Exact existing producer output equals canonical 339 artifact'),
        current_prime=p,current_height=height,prefix_depth=depth,prefix=0,
        future_count=21,original_count=len(originals),period=str(period),
        original_classes=[dict(c,private_integer=private[i]) for i,c in enumerate(originals)],
        uncovered_integer=str(uncovered),
        private_witness_modular_checks=len(originals)**2,
        ordered_containment_checks=len(originals)*(len(originals)-1),
        original_containments=contained_pairs,
        residual_classes=residual,
        conflict_shearer=check_conflict_shearer(residual),
        grouped_residues={str(m):sorted(values) for m,values in grouped.items()},
        exact_union_checks=union_checks,
        conditional_hn_infeasibility=dict(
            reason='Necessary lower and strict upper bounds on xi_17 are inconsistent',
            xi_13_lower='12',xi_17_lower=str(lower_r),xi_17_strict_upper=str(strict_upper_r),
            lower_minus_upper=str(lower_r-strict_upper_r)),
        global_future_majorant=dict(modulus=13,residues=list(range(12)),
            labelwise_containment_certificates=label_containments,
            hn_weights={'11':'0','13':'12'},total_cost_B='12',
            relative_hole_lower='exp(-12)',
            current_conditional_leaf_cap='1/11',
            exact_hole_on_chosen_prefix='1/13',
            scope='Global union majorant; exact union after conditioning on J=0 mod 11^11'),
        measure_scope='All new moduli end at 11,13,or17 and have no 3/5/7 factor. The actual head labels, full 3/5/7 heights, head source, and every same-chain measure before prime11 are unchanged. No equality of distinct physical/source laws is asserted.',
        conclusion_scope='Presentation-dependent HN false negative and its certified repair on an actual irredundant noncover. No unrestricted uniform budget or whole-cover counterexample.')
    return result


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[1])
    mode=parser.add_mutually_exclusive_group()
    mode.add_argument('--write',action='store_true')
    mode.add_argument('--check',action='store_true')
    args=parser.parse_args()
    io=module('hn_majorant_certificate_io',args.base.resolve()/'certificate_io.py')
    value=calculate(args.base.resolve())
    canonical=json.loads(json.dumps(value))
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE,json.dumps(canonical,indent=2)+'\n')
    else:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE),object_pairs_hook=io._unique)==canonical,
                'Stored certificate equals exact recomputation')
    print('PASS',value['original_count'],'original classes;',value['private_witness_modular_checks'],
          'private modular checks;',value['exact_union_checks'],'conditional union checks; actual339 replay exact')


if __name__=='__main__':
    main()
