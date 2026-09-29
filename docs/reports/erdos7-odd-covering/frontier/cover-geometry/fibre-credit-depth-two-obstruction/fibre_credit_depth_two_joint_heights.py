#!/usr/bin/env python3
"""Exact all-height extensions from one source and its shallow cylinder responses."""
import argparse
import importlib.util
from fractions import Fraction as F
from itertools import product
from math import prod
from pathlib import Path
import hashlib
import json


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def mul(values):
    return prod(values, start=F(1))


def prefix_certificate(api, name, pairs):
    """All height costs from the SAME conditional source's 192 shallow screens."""
    _, cells, _, _ = api.conditional_data(name, pairs)
    source = sum((api.W[u[0]]*h[0]/24 for u,h in cells.items()), F(0))
    deep, complete, first = F(0), F(0), F(0)
    screens = []
    for T in range(16):
        outside_first = mul(F(1,q-1) for i,q in enumerate(api.BIG) if T>>i&1)
        outside_lift = mul(F(q,q-1) for i,q in enumerate(api.BIG) if T>>i&1)
        for j, ports in enumerate(((tuple(range(5)),), api.ROOTS, tuple((l,) for l in range(5)))):
            matrices = [[[sum((api.W[l]*cells.get((l,r,s),(F(0),)*16)[T]
                               for l in port), F(0)) for s in range(1,7)]
                         for r in range(1,5)] for port in ports]
            caps = (
                max(sum((v for row in a for v in row),F(0)) for a in matrices)/24,
                max(sum(a[i],F(0)) for a in matrices for i in range(4))/24,
                max(sum((a[i][k] for i in range(4)),F(0)) for a in matrices for k in range(6))/24,
                max(v for a in matrices for row in a for v in row)/24)
            for headmask, cap in enumerate(caps):
                cap *= outside_first
                lift = outside_lift*(F(5,4) if headmask&1 else 1)*(F(7,6) if headmask&2 else 1)
                need(cap>=0 and lift>=1, 'nonnegative actual-source cap and complete lift fee')
                deep += (lift-1)*cap
                complete += lift*cap
                first += cap
                screens.append((j,headmask,T,cap,lift))
                if (j,headmask,T)==(0,0,0):
                    need(cap==source, 'unit screen equals same source mass')
    need(len(screens)==192, 'every shallow label including unit appears once')
    query, shallow = complete-source, first-source
    need(query==shallow+deep, 'same-source first/deep all-query decomposition')
    return source,deep,query,shallow,screens


def calculate():
    src = Path(__file__).resolve().with_name('fibre_credit_depth_two_joint_fixtures.json')
    spec = importlib.util.spec_from_file_location('joint_fixture', src.with_suffix('.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    fixture = json.loads(src.read_text())
    need(fixture == json.loads(json.dumps(module.calculate())),
         'retained actual fixture agrees with reconstructed same-source responses')
    primes = (5, 7, 11, 13, 17, 19)
    shallow_labels = {
        3**j * prod(q**e for q, e in zip(primes, es))
        for j in range(3) for es in product(range(2), repeat=6)
    } - {1}
    need(len(shallow_labels) == 191, 'complete distinct shallow inventory')
    first = tuple(F(1, q-1) for q in primes)
    tail = tuple(F(1, (q-1)**2) for q in primes)
    full = tuple(F(q, (q-1)**2) for q in primes)
    need(all(a+b == c for a, b, c in zip(first, tail, full)), 'full geometric height sums')
    # The difference includes precisely exponent vectors with some e_q >= 2.
    # The independent three-category expansion verifies that subtraction.
    deep_coeff = mul(1+x for x in full) - mul(1+x for x in first)
    expanded = F(0)
    for es in product(range(3), repeat=6):
        if 2 not in es:
            continue
        expanded += mul(F(1) if e == 0 else first[i] if e == 1 else tail[i]
                        for i, e in enumerate(es))
    need(deep_coeff == expanded, 'complete deep support enumeration')
    ternary_caps = (F(1), F(1, 2), F(1, 4))
    tau = sum(ternary_caps) * deep_coeff
    d0 = F(9, 4) * mul(F(q, q-1) for q in primes)
    need(tau == F(34396590319, 101921587200), 'exact full tail')
    need(d0 == F(323323, 73728), 'base Haar density cap')
    q_out = (1+F(1, 21))*(1+F(1, 27))-1
    s_out = F(1, 21)+F(1, 27)
    c_out = F(22, 21)*F(28, 27)
    target = (1+s_out)/q_out-1
    need((q_out, s_out, c_out, target) ==
         (F(49, 567), F(48, 567), F(616, 567), F(566, 49)),
         '23/29 actual pure continuation constants')
    rows = []
    for case in fixture['cases']:
        payload = case['actual_originals']
        need({r['m'] for r in payload} == shallow_labels and len(payload) == 191,
             'each fixed phase family uses the complete shallow inventory once')
        digest = hashlib.sha256(json.dumps(payload, separators=(',', ':')).encode()).hexdigest()
        need(digest == case['original_phase_sha256'], 'literal same-family phase digest')
        need(all(0 <= r['a'] < r['m'] for r in payload), 'canonical actual residues')
        source, query = F(case['S']), F(case['K'])
        alpha = source-tau
        gap = target*alpha-query
        mass = (1+s_out-q_out)*alpha-q_out*query
        density = mass/(d0*c_out)
        need(mass == q_out*gap and density == 49*gap/(616*d0), 'unnormalized density cancellation')
        positive = gap > 0
        if case['layout'] == 'aligned':
            need(alpha > 0 and positive, 'all-height aligned continuation')
        else:
            need(not positive, 'spread examples have no positive all-height certificate here')
        head_rows = next(pairs for name,pairs,_ in module.HEAD_LAYOUTS if name==case['head_layout'])
        prefix_source, source_tail, source_query, shallow_query, screens = prefix_certificate(module,case['layout'],head_rows)
        need(prefix_source==source, 'prefix source equals reconstructed actual fixture source')
        refined_alpha = source-source_tail
        refined_gap = target*refined_alpha-source_query
        need(refined_alpha>0 and refined_gap>0, 'all four same-source all-height certificates positive')
        need(source_tail<=tau and source_query<=query, 'refined same-source costs improve coarse caps')
        refined_mass = (1+s_out-q_out)*refined_alpha-q_out*source_query
        refined_density = refined_mass/(d0*c_out)
        need(refined_density==49*refined_gap/(616*d0), 'refined exact Haar-density conversion')
        rows.append(dict(head=case['head_layout'],layout=case['layout'],original_phase_sha256=digest,
            S=str(source),coarse_query=str(query),coarse_alpha_lower=str(alpha),
            coarse_gate=str(gap),coarse_gate_decimal=float(gap),coarse_gate_positive=positive,
            coarse_haar_density_lower=str(density) if positive else None,
            shallow_screens=len(screens),source_deep_tail=str(source_tail),
            source_deep_tail_decimal=float(source_tail),shallow_query=str(shallow_query),
            all_height_query=str(source_query),alpha_lower=str(refined_alpha),gate=str(refined_gap),
            gate_decimal=float(refined_gap),positive_all_height_gate=True,
            haar_density_lower=str(refined_density),haar_density_lower_decimal=float(refined_density)))
    out = dict(scope='Four fixed 191-original phase patterns; arbitrary additional distinct core-only labels and phases of any nonternary height, and arbitrary 23/29-bearing originals, all with v3<=2 and no support outside 3,5,7,11,13,17,19,23,29. The refined same-source gate is positive for all four; the coarser product-tail gate fails on two spread layouts.',
        base_source='Haar conditioned only on 0 mod q avoidance for q=5,7,11,13,17,19, with fixed five-leaf ternary weights; higher pure originals are charged, not absorbed into changed pure laws.',
        complete_shallow_labels=191,coarse_product_tail=str(tau),coarse_product_tail_decimal=float(tau),
        method='One prefix-dependent source with independent Haar tails; its 192 first-cylinder caps pay every deeper original once and bound the complete nonunit query sum.',
        base_haar_density_cap=str(d0), continuation_target=str(target),
        fixture_sha256=hashlib.sha256(src.read_bytes()).hexdigest(), cases=rows)
    return out


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result=json.loads(json.dumps(calculate()))
    rendered=json.dumps(result,sort_keys=True,indent=2)+'\n'
    if args.output is None:
        retained=json.loads(Path(__file__).resolve().with_suffix('.json').read_text())
        need(retained==result,'retained result agrees with exact replay')
        print(rendered,end='')
    else:
        args.output.write_text(rendered)


if __name__=='__main__':
    main()
