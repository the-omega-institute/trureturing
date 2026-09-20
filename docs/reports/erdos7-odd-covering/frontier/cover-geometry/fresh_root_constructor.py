#!/usr/bin/env python3
"""Fresh-prime replacement of selected lowest-p-digit branches.

Standalone exact finite constructor and checker. The mathematical map permits
arbitrary original p-height. The default API accepts only odd moduli; the
explicit allow_even=True mode supplies honest test covers, not witnesses to
the unknown all-odd premise. No Lean verification is claimed.
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


def fresh_root_construct(classes, p, q, *, selected_roots=None, allow_even=False,
                         max_period=200000):
    """Return the constructed cover, original provenance, and exact checks.

    Repetition is permitted only for distinct residue classes of modulus p.
    q must divide no original modulus and differ from p. Exactly min(q,p-s)
    nonpure roots are selected, defaulting to their increasing first values.
    Their target roots are the last k q-roots, so q=t+2 leaves pure roots 0,1.

    All complete input/output periods and the joint-transport carrier must
    fit max_period; exceeding it is a finite-check limitation, not a
    mathematical rejection of the general construction.
    """
    require(prime(p) and p % 2, 'p must be an odd prime')
    require(prime(q) and q % 2, 'q must be an odd prime')
    classes = list(classes)
    require(bool(classes), 'input must be nonempty')
    require(all(m > 1 for _, m in classes), 'all input moduli must be nonunit')
    classes = [(a % m, m) for a, m in classes]
    require(allow_even or all(m % 2 for _, m in classes), 'even input forbidden')
    pure = [i for i, (_, m) in enumerate(classes) if m == p]
    pure_roots = {classes[i][0] for i in pure}
    require(len(pure_roots) == len(pure), 'same-residue duplicate pure-p class')
    other_moduli = [m for _, m in classes if m != p]
    require(len(other_moduli) == len(set(other_moduli)), 'duplicate non-p modulus')
    require(q != p and all(m % q for _, m in classes), 'q is not fresh')
    roots = [r for r in range(p) if r not in pure_roots]
    s, t = len(pure), len(roots)
    require(t > 0, 'require a nonpure p-root: t=p-s must be positive')
    k = min(q, t)
    selected = roots[:k] if selected_roots is None else list(selected_roots)
    require(len(selected) == k and len(set(selected)) == k
            and all(r in roots for r in selected), 'invalid selected nonpure roots')
    root_map = dict(zip(selected, range(q-k, q)))
    in_period = period(classes)
    heights = [valuation(m, p) for _, m in classes]
    actual_height = max(heights)
    H = max(1, actual_height)
    R = lcm(*(m//p**h for (_, m), h in zip(classes, heights)))
    source_carrier = p**H*R
    transport_carrier = q*p**(H-1)*R
    require(max(in_period, source_carrier, transport_carrier) <= max_period,
            'complete-period finite-check cap exceeded')
    input_vectors = [bits(classes, x) for x in range(in_period)]
    require(all(any(v) for v in input_vectors), 'input does not cover its complete period')

    output, provenance = [], []
    original_to_output = {i: [] for i in range(len(classes))}
    deleted = []
    p_free = []
    selected_mixed = []

    def emit(a, m, role, original=None):
        j = len(output)
        output.append((a % m, m))
        provenance.append(dict(output=j, original=original, role=role))
        if original is not None:
            original_to_output[original].append(j)

    for i, ((a, m), alpha) in enumerate(zip(classes, heights)):
        if m == p:
            deleted.append(dict(original=i, reason='original pure-p root'))
        elif alpha == 0:
            emit(a, m, 'unchanged p-free original', i)
            p_free.append(i)
        elif a % p not in root_map:
            deleted.append(dict(original=i,
                                reason='covered pure-p root' if a % p in pure_roots
                                else 'dropped nonpure root'))
        else:
            xi, b = a % p, root_map[a % p]
            d = m//p**alpha
            tail_modulus = p**(alpha-1)
            tail_residue = (a-xi)//p % tail_modulus
            new_residue = crt(b, q, tail_residue, tail_modulus)
            new_residue = crt(new_residue, q*tail_modulus, a % d, d)
            emit(new_residue, q*tail_modulus*d, 'transported original lowest-p-digit branch', i)
            selected_mixed.append(i)
    for b in range(q-k):
        emit(b, q, 'fresh pure-q branch')

    output_pure = [(a, m) for a, m in output if m == q]
    output_other = [m for _, m in output if m != q]
    require(len(output_pure) == q-k
            and len({a for a, _ in output_pure}) == q-k, 'pure-q output palette')
    require(len(output_other) == len(set(output_other)), 'output non-q modulus collision')
    require(all(m > 1 for _, m in output), 'output contains a unit modulus')
    require(allow_even or all(m % 2 for _, m in output), 'output is not odd')
    require(all(m % (q*q) for _, m in output), 'output is not q-flat')
    out_period = period(output)
    require(transport_carrier % out_period == 0, 'output period does not divide common carrier')
    require(out_period <= max_period, 'output complete-period finite-check cap exceeded')
    require(all(any(bits(output, x)) for x in range(out_period)),
            'output does not cover its complete period')

    # Verify one deterministic shared source, retaining the WHOLE original
    # event vector. No independent relabelling or cofactor sampling occurs.
    source_hist = {xi: Counter() for xi in selected}
    transported_hist = {xi: Counter() for xi in selected}
    source_images = {xi: set() for xi in selected}
    reverse_roots = {b: xi for xi, b in root_map.items()}
    transported_points = fresh_points = 0
    for y in range(transport_carrier):
        observed = bits(output, y)
        b = y % q
        if b in reverse_roots:
            xi = reverse_roots[b]
            w = crt(xi+p*(y % p**(H-1)), p**H, y % R, R)
            require(w % p == xi, 'source root mismatch')
            original = bits(classes, w)
            transported = tuple(any(observed[j] for j in original_to_output[i])
                                for i in range(len(classes)))
            require(original == transported, 'full joint original-event vector transport')
            require(sum(observed) == sum(original), 'same-source covering multiplicity')
            source_images[xi].add(w)
            transported_hist[xi][transported] += 1
            transported_points += 1
        else:
            require(sum(observed) == 1+sum((y-classes[i][0]) % classes[i][1] == 0
                                         for i in p_free),
                    'fresh branch retains exactly pure-q plus p-free events')
            fresh_points += 1
    for xi in selected:
        actual_source = set(range(xi, source_carrier, p))
        require(source_images[xi] == actual_source,
                'transport is not onto the complete conditional source fibre')
        require(len(source_images[xi]) == transport_carrier//q,
                'source-fibre map is not one-to-one')
        for w in actual_source:
            source_hist[xi][bits(classes, w)] += 1
        require(source_hist[xi] == transported_hist[xi],
                'uniform conditional JOINT law was not preserved')
    require(transported_points+fresh_points == transport_carrier,
            'joint and fresh branch accounting')

    A = sum((F(1, classes[i][1]) for i in p_free), F(0))
    D_selected = sum((F(1, classes[i][1]) for i in selected_mixed), F(0))
    expected_mass = A+F(q-k, q)+F(p, q)*D_selected
    require(mass(output) == expected_mass, 'all-q reciprocal-mass formula')
    conditional_excess = {
        xi: A+p*sum((F(1, m) for (a, m), alpha in zip(classes, heights)
                      if alpha and m != p and a % p == xi), F(0))-1
        for xi in selected
    }
    require(all(h >= 0 for h in conditional_excess.values()),
            'covered source fibre has negative conditional excess')
    require(expected_mass-1 == F(q-k, q)*A
            + sum(conditional_excess.values(), F(0))/q,
            'branchwise excess disintegration')
    pure_root_deleted_mass = sum((F(1, m) for (a, m), alpha in zip(classes, heights)
                                  if alpha and m != p and a % p in pure_roots), F(0))
    large_q_formula = None
    if q >= t:
        large_q_formula = (F(p, q)*(mass(classes)-1-pure_root_deleted_mass)
                           +(1-F(p, q))*A)
        require(expected_mass-1 == large_q_formula, 'q>=t global excess identity')

    return dict(input=classes, output=output, p=p, q=q, s=s, t=t, k=k,
                fixture_scope=('even cofactors explicitly allowed; NOT an all-odd cover witness'
                               if allow_even else 'all-odd conditional construction'),
                selected_roots=selected, target_roots=root_map,
                input_p_height=actual_height, source_p_height=H, output_q_flat=True,
                input_period=in_period, output_period=out_period,
                conditional_source_carrier=source_carrier,
                joint_transport_carrier=transport_carrier,
                transported_joint_points=transported_points, fresh_branch_points=fresh_points,
                original_to_output=original_to_output, provenance=provenance,
                deleted_original_labels=deleted,
                A=str(A), selected_mixed_mass=str(D_selected),
                deleted_pure_root_mass=str(pure_root_deleted_mass),
                input_excess=str(mass(classes)-1), output_excess=str(expected_mass-1),
                q_ge_t_excess_formula=None if large_q_formula is None else str(large_q_formula),
                checked_period_points=in_period+out_period+transport_carrier,
                conditional_source_points_checked=sum(len(v) for v in source_images.values()))


def dyadic_fixture(p, t):
    """An actual cover with distinct EVEN cofactors, s=p-t pure p-roots."""
    require(prime(p) and p % 2 and 1 <= t <= p, 'invalid dyadic fixture parameters')
    classes = [(a, p) for a in range(p-t)]
    classes += [(2**(h-1), 2**h) for h in range(1, t+1)]
    for h, xi in enumerate(range(p-t, p), 1):
        classes.append((crt(xi, p, 0, 2**h), p*2**h))
    return classes


def expect_rejection(classes, p, q, reason, **kwargs):
    try:
        fresh_root_construct(classes, p, q, **kwargs)
    except ValueError as exc:
        require(reason in str(exc), f'wrong rejection: {exc}')
        return str(exc)
    raise ValueError('invalid fixture unexpectedly admitted')


def main():
    specs = [
        ('q<t, dropped roots', dyadic_fixture(7, 5), 7, 3, None),
        ('q=t', dyadic_fixture(7, 5), 7, 5, None),
        ('q=t+1', dyadic_fixture(7, 4), 7, 5, None),
        ('q=t+2', dyadic_fixture(7, 3), 7, 5, None),
        ('q>t+2', dyadic_fixture(7, 3), 7, 11, None),
        ('different selected roots/order', dyadic_fixture(7, 5), 7, 3, [6, 2, 5]),
    ]
    # d=1, alpha=8: this is a mixed label, never a pure-q output.
    high_pure = dyadic_fixture(3, 1)+[(2+3*17, 3**8)]
    specs.append(('retained pure p^8 with d=1', high_pure, 3, 5, None))
    high_mixed = dyadic_fixture(5, 2)+[(3+5*17, 5**4),
                                    (crt(4+5*7, 5**3, 0, 8), 5**3*8),
                                    (0, 5**2)]
    specs.append(('retained unequal p-heights and cofactors', high_mixed, 5, 3, None))
    dropped_high = dyadic_fixture(7, 5)+[(6, 7**3), (0, 7**2)]
    specs.append(('high dropped roots retain common joint carrier', dropped_high, 7, 3, None))
    no_pure = dyadic_fixture(3, 3)
    specs.append(('s=0 boundary', no_pure, 3, 5, None))
    no_p_factor = [(0, 2), (0, 3), (1, 4), (5, 6), (7, 12)]
    specs.append(('p absent from input period', no_p_factor, 5, 7, None))
    results = []
    for name, seed, p, q, selected in specs:
        result = fresh_root_construct(seed, p, q, selected_roots=selected, allow_even=True)
        result['case'] = name
        results.append(result)
    retained_high = results[6]
    require(any(m == 5*3**7 for _, m in retained_high['output']),
            'pure p^8 label did not transport to q*p^7')
    require(results[7]['deleted_pure_root_mass'] == '1/25'
            and results[7]['q_ge_t_excess_formula'] == results[7]['output_excess'],
            'q>=t mass test must include a nonzero deleted pure-root correction')
    require(results[8]['output_period'] < results[8]['joint_transport_carrier'],
            'dropped-height fixture failed to expose the common-carrier distinction')
    require(results[10]['input_p_height'] == 0 and results[10]['source_p_height'] == 1,
            'auxiliary root must not be reported as an original prime factor')
    base = dyadic_fixture(7, 3)
    rejections = [
        expect_rejection(base+[(7, 7)], 7, 5, 'same-residue duplicate', allow_even=True),
        expect_rejection(base+[(0, 2)], 7, 5, 'duplicate non-p modulus', allow_even=True),
        expect_rejection(base+[(0, 5)], 7, 5, 'not fresh', allow_even=True),
        expect_rejection(base, 7, 7, 'not fresh', allow_even=True),
        expect_rejection(base[:-1], 7, 5, 'does not cover', allow_even=True),
        expect_rejection(base, 7, 5, 'even input forbidden'),
        expect_rejection(base, 7, 5, 'invalid selected', selected_roots=[0, 4, 5], allow_even=True),
        expect_rejection([(a, 7) for a in range(7)], 7, 5, 't=p-s must be positive'),
        expect_rejection(base, 7, 9, 'q must be an odd prime', allow_even=True),
    ]
    summary = [{key: result[key] for key in
                ('case', 'p', 'q', 's', 't', 'k', 'input_p_height', 'input_period',
                 'output_period', 'joint_transport_carrier', 'output_excess')}
               for result in results]
    print(json.dumps(dict(success=True, fixtures=summary, rejection_count=len(rejections),
                          rejections=rejections,
                          checked_period_points=sum(r['checked_period_points'] for r in results),
                          conditional_source_points_checked=sum(r['conditional_source_points_checked']
                                                                 for r in results),
                          scope='Actual covers with even cofactors; no distinct all-odd witness or Lean claim'),
                     sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
