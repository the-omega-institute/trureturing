#!/usr/bin/env python3
"""Move one p-root digit in front of the complete old q-coordinate.

Standalone exact finite constructor and shared-source joint-law checker.
Every q-divisible input modulus must also be p-divisible. The output need
not be q-flat. Even fixtures are complete covers, not all-odd witnesses.
This is an ordinary conditional construction, not a Lean or novelty claim.
"""
from collections import Counter
from fractions import Fraction as F
from math import gcd, isqrt, lcm
import json


def require(ok, message):
    if not ok:
        raise ValueError(message)


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n)+1))


def valuation(n, p):
    h = 0
    while n % p == 0:
        n //= p
        h += 1
    return h


def period(classes):
    return lcm(*(m for _, m in classes))


def mass(classes):
    return sum((F(1, m) for _, m in classes), F(0))


def bits(classes, x):
    return tuple((x-a) % m == 0 for a, m in classes)


def crt(a, m, b, n):
    require(gcd(m, n) == 1, 'CRT factors are not coprime')
    return (a + m*(((b-a)*pow(m, -1, n)) % n)) % (m*n)


def old_q_memory_construct(classes, p, q, *, selected_roots=None,
                           allow_even=False, max_period=200000):
    """Construct the cover and check every full source event vector.

    The last k=min(q,p-s) q-digits encode the selected nonpure p-roots.
    Each selected p-divisible original has exactly one AP image. Every
    p-free original stays literal, under the required q-free support rule.
    All complete carriers must fit max_period; this cap limits the finite
    checker, not the general mathematical construction.
    """
    require(prime(p) and p % 2, 'p must be an odd prime')
    require(prime(q) and q % 2, 'q must be an odd prime')
    require(q != p, 'p and q must be distinct')
    classes = list(classes)
    require(bool(classes), 'input must be nonempty')
    require(all(m > 1 for _, m in classes), 'all input moduli must be nonunit')
    classes = [(a % m, m) for a, m in classes]
    require(allow_even or all(m % 2 for _, m in classes), 'even input forbidden')
    pure = [i for i, (_, m) in enumerate(classes) if m == p]
    pure_roots = {classes[i][0] for i in pure}
    require(len(pure) == len(pure_roots), 'same-residue duplicate pure-p class')
    other_moduli = [m for _, m in classes if m != p]
    require(len(other_moduli) == len(set(other_moduli)), 'duplicate non-p modulus')
    require(all(m % q or m % p == 0 for _, m in classes),
            'support condition: every q-divisible original must be p-divisible')
    roots = [a for a in range(p) if a not in pure_roots]
    s, t = len(pure), len(roots)
    require(t > 0, 'require t=p-s positive')
    k = min(q, t)
    selected = roots[:k] if selected_roots is None else list(selected_roots)
    require(len(selected) == k and len(set(selected)) == k
            and all(a in roots for a in selected), 'invalid selected nonpure roots')
    root_map = dict(zip(selected, range(q-k, q)))
    p_heights = [valuation(m, p) for _, m in classes]
    q_heights = [valuation(m, q) for _, m in classes]
    actual_p_height = max(p_heights)
    H, K = max(1, actual_p_height), max(q_heights)
    R = lcm(*(m//(p**alpha*q**beta)
              for (_, m), alpha, beta in zip(classes, p_heights, q_heights)))
    in_period = period(classes)
    source_carrier = p**H*q**K*R
    joint_carrier = p**(H-1)*q**(K+1)*R
    require(max(in_period, source_carrier, joint_carrier) <= max_period,
            'complete-period finite-check cap exceeded')
    require(all(any(bits(classes, x)) for x in range(in_period)),
            'input does not cover its complete period')

    output, provenance, deleted = [], [], []
    original_to_output = {i: [] for i in range(len(classes))}
    p_free, transported_labels = [], []

    def emit(a, m, role, original=None):
        j = len(output)
        output.append((a % m, m))
        provenance.append(dict(output=j, role=role, original=original))
        if original is not None:
            original_to_output[original].append(j)

    for i, ((a, m), alpha, beta) in enumerate(zip(classes, p_heights, q_heights)):
        if m == p:
            deleted.append(dict(original=i, reason='original pure-p class'))
        elif alpha == 0:
            require(beta == 0, 'p-free original unexpectedly has old q-memory')
            emit(a, m, 'unchanged p-free q-free original', i)
            p_free.append(i)
        elif a % p not in root_map:
            deleted.append(dict(original=i, reason='covered pure-p root'
                                if a % p in pure_roots else 'dropped nonpure root'))
        else:
            xi, b = a % p, root_map[a % p]
            r = m//(p**alpha*q**beta)
            p_tail = p**(alpha-1)
            q_memory = q**(beta+1)
            q_residue = b+q*(a % q**beta)
            residue = crt((a-xi)//p, p_tail, q_residue, q_memory)
            residue = crt(residue, p_tail*q_memory, a, r)
            modulus = p_tail*q_memory*r
            require(modulus == q*(m//p), 'wrong literal transported modulus')
            require(residue % q_memory == q_residue,
                    'old q digits were not shifted with the selected root')
            emit(residue, modulus, 'one-AP old-q-memory transport', i)
            transported_labels.append(i)
    for b in range(q-k):
        emit(b, q, 'auxiliary pure-q closing class')

    output_pure = [(a, m) for a, m in output if m == q]
    output_other = [m for _, m in output if m != q]
    require(len(output_pure) == q-k
            and len({a for a, _ in output_pure}) == q-k, 'pure-q output count')
    require(len(output_other) == len(set(output_other)), 'output non-q modulus collision')
    require(all(m > 1 for _, m in output), 'output has a unit modulus')
    require(allow_even or all(m % 2 for _, m in output), 'output is not odd')
    require(all(len(images) <= 1 for images in original_to_output.values()),
            'an original label was split into multiple APs')
    out_period = period(output)
    require(joint_carrier % out_period == 0, 'output period does not divide joint carrier')
    require(all(any(bits(output, x)) for x in range(out_period)),
            'output does not cover its complete period')
    q_flat = all(m % (q*q) for _, m in output)
    distinct = len({m for _, m in output}) == len(output)
    require(distinct == (q-k <= 1), 'distinctness classification disagrees with actual moduli')

    # A single deterministic source point supplies the entire original event
    # vector. Uniformity is checked on complete fibres, not independent marginals.
    reverse_roots = {b: xi for xi, b in root_map.items()}
    source_images = {xi: set() for xi in selected}
    observed_hist = {xi: Counter() for xi in selected}
    source_hist = {xi: Counter() for xi in selected}
    transported_points = closing_points = 0
    for x in range(joint_carrier):
        observed = bits(output, x)
        b = x % q
        if b in reverse_roots:
            xi = reverse_roots[b]
            source_p = xi+p*(x % p**(H-1))
            source_q = (x//q) % q**K
            y = crt(source_p, p**H, source_q, q**K)
            y = crt(y, p**H*q**K, x % R, R)
            original = bits(classes, y)
            pulled_back = tuple(any(observed[j] for j in original_to_output[i])
                                for i in range(len(classes)))
            require(original == pulled_back, 'full shared-source event vector failed')
            require(sum(observed) == sum(original), 'same-source covering multiplicity failed')
            require(y % p == xi and y % q**K == source_q and y % R == x % R,
                    'shared source lost an old coordinate')
            source_images[xi].add(y)
            observed_hist[xi][pulled_back] += 1
            transported_points += 1
        else:
            require(sum(observed) == 1+sum((x-classes[i][0]) % classes[i][1] == 0
                                         for i in p_free),
                    'closing branch does not equal one pure-q plus p-free events')
            closing_points += 1
    for xi in selected:
        actual_source = set(range(xi, source_carrier, p))
        require(source_images[xi] == actual_source, 'not onto the entire original root fibre')
        require(len(source_images[xi]) == joint_carrier//q,
                'conditional shared-source map is not one-to-one')
        for y in actual_source:
            source_hist[xi][bits(classes, y)] += 1
        require(source_hist[xi] == observed_hist[xi], 'uniform conditional JOINT law failed')
    require(transported_points+closing_points == joint_carrier, 'branch accounting failed')

    A = sum((F(1, classes[i][1]) for i in p_free), F(0))
    selected_mass = sum((F(1, classes[i][1]) for i in transported_labels), F(0))
    expected_mass = A+F(p, q)*selected_mass+F(q-k, q)
    require(mass(output) == expected_mass, 'literal reciprocal transport failed')
    conditional_excess = {
        xi: A+p*sum((F(1, m) for (a, m), alpha in zip(classes, p_heights)
                      if alpha and m != p and a % p == xi), F(0))-1
        for xi in selected
    }
    require(all(h >= 0 for h in conditional_excess.values()),
            'complete original fibre has negative excess')
    require(expected_mass-1 == F(q-k, q)*A
            +sum(conditional_excess.values(), F(0))/q,
            'conditional full-source excess identity failed')

    return dict(input=classes, output=output, p=p, q=q, s=s, t=t, k=k,
                fixture_scope=('actual even cover; NOT an all-odd witness' if allow_even
                               else 'all-odd conditional construction'),
                selected_roots=selected, target_roots=root_map,
                input_p_height=actual_p_height, source_p_height=H, input_q_height=K,
                output_q_height=max(valuation(m, q) for _, m in output),
                output_q_flat=q_flat, output_distinct=distinct,
                pure_q_classes=q-k,
                p_flat_two_copy_premise=(q-k == 2 and q_flat),
                input_period=in_period, output_period=out_period,
                conditional_source_carrier=source_carrier,
                joint_transport_carrier=joint_carrier,
                original_to_output=original_to_output, provenance=provenance,
                deleted_original_labels=deleted,
                transported_joint_points=transported_points,
                closing_branch_points=closing_points,
                conditional_source_points_checked=sum(map(len, source_images.values())),
                full_event_coordinate_checks=transported_points*len(classes),
                checked_period_points=in_period+out_period+joint_carrier,
                A=str(A), selected_mixed_mass=str(selected_mass),
                input_excess=str(mass(classes)-1), output_excess=str(expected_mass-1))


def dyadic_fixture(p, t):
    """Complete even cover with distinct non-p moduli and s=p-t pure p-roots."""
    require(prime(p) and p % 2 and 1 <= t <= p, 'invalid dyadic fixture parameters')
    classes = [(a, p) for a in range(p-t)]
    classes += [(2**(h-1), 2**h) for h in range(1, t+1)]
    for h, xi in enumerate(range(p-t, p), 1):
        classes.append((crt(xi, p, 0, 2**h), p*2**h))
    return classes


def expect_rejection(classes, p, q, reason, **kwargs):
    try:
        old_q_memory_construct(classes, p, q, **kwargs)
    except ValueError as exc:
        require(reason in str(exc), f'wrong rejection: {exc}')
        return str(exc)
    raise ValueError('invalid fixture unexpectedly admitted')


def main():
    direct = dyadic_fixture(5, 2)+[(crt(3, 5, 7, 9), 5*9)]
    two_copy = dyadic_fixture(7, 3)+[(crt(4, 7, 17, 25), 7*25)]
    high_residue = crt(2+7*5, 7**3, 5, 9)
    high_residue = crt(high_residue, 7**3*9, 3, 4)
    high = dyadic_fixture(7, 5)+[(high_residue, 7**3*9*4)]
    dropped = dyadic_fixture(7, 5)+[(crt(6, 7, 20, 27), 7*27),
                                  (crt(0, 7, 5, 9), 7*9)]
    dropped_two_copy = dyadic_fixture(7, 3)+[(crt(0, 7, 17, 25), 7*25)]
    specs = [('q=t+1 with existing q^2 memory', direct, 5, 3, None),
             ('q=t+2 is not q-flat', two_copy, 7, 5, None),
             ('q<t reordered roots and high p/q powers', high, 7, 3, [6, 2, 5]),
             ('highest old q memory only in discarded roots', dropped, 7, 3, None),
             ('q=t+2 becomes flat after all old q labels disappear',
              dropped_two_copy, 7, 5, None)]
    results = []
    for name, seed, p, q, selected in specs:
        result = old_q_memory_construct(seed, p, q, selected_roots=selected, allow_even=True)
        result['case'] = name
        results.append(result)
    require(results[0]['output_distinct'] and results[0]['output_q_height'] == 3,
            'direct existing-q fixture lost high q memory')
    require(results[1]['pure_q_classes'] == 2 and not results[1]['output_q_flat']
            and not results[1]['p_flat_two_copy_premise'],
            'nonflat two-copy fixture was falsely eligible for p-flat closure')
    require(results[2]['input_p_height'] == 3 and results[2]['input_q_height'] == 2,
            'high-coordinate fixture does not exercise both heights')
    require(results[3]['output_period'] < results[3]['joint_transport_carrier']
            and results[3]['output_q_flat'], 'discarded old memory carrier was collapsed')
    require(results[4]['input_q_height'] == 2 and results[4]['p_flat_two_copy_premise']
            and results[4]['output_period'] < results[4]['joint_transport_carrier'],
            'deleted old q labels must not invalidate a genuinely flat two-copy output')
    base = dyadic_fixture(5, 2)
    rejections = [
        expect_rejection(direct+[(0, 3)], 5, 3, 'support condition', allow_even=True),
        expect_rejection(base, 5, 5, 'must be distinct', allow_even=True),
        expect_rejection(base, 5, 3, 'even input forbidden'),
        expect_rejection(base+[(0, 5)], 5, 3, 'same-residue duplicate', allow_even=True),
        expect_rejection(base+[(0, 2)], 5, 3, 'duplicate non-p modulus', allow_even=True),
        expect_rejection(base, 5, 3, 'invalid selected', selected_roots=[0, 4], allow_even=True),
        expect_rejection(base[:-1], 5, 3, 'does not cover', allow_even=True),
        expect_rejection(base, 5, 9, 'q must be an odd prime', allow_even=True),
        expect_rejection(direct, 5, 3, 'finite-check cap', allow_even=True, max_period=100),
        expect_rejection([(a, 5) for a in range(5)], 5, 3, 't=p-s positive'),
        expect_rejection(base+[(0, 1)], 5, 3, 'must be nonunit', allow_even=True),
    ]
    print(json.dumps(dict(success=True, fixtures=results, rejections=rejections,
                          rejection_count=len(rejections),
                          checked_period_points=sum(r['checked_period_points'] for r in results),
                          transported_joint_points=sum(r['transported_joint_points'] for r in results),
                          full_event_coordinate_checks=sum(r['full_event_coordinate_checks'] for r in results),
                          conditional_source_points_checked=sum(r['conditional_source_points_checked'] for r in results),
                          scope='Complete even-cover fixtures; ordinary conditional proof; no odd witness or Lean claim'),
                     sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
