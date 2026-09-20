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


def contract_small_projection(classes, q, p, *, selected_roots=None,
                              allow_even=False, max_period=200000):
    """Cover-preserving class-count descent from <= p-q actual residual roots.

    Original classes have distinct moduli. This computes their q-free residual
    and transports q complete p-root branches that avoid it. The whole q-free
    original event vector is retained on each selected branch; q-bearing
    original labels are explicitly removed, not treated as measure transport.
    No claim of global minimum cardinality is inferred from a finite run.
    """
    classes = list(classes)
    require(prime(q) and prime(p) and 2 < q < p, 'require odd primes q < p')
    require(classes and all(d > 1 for _, d in classes), 'original moduli must be nonunit')
    classes = [(a % d, d) for a, d in classes]
    require(len({d for _, d in classes}) == len(classes), 'original moduli must be distinct')
    require(allow_even or all(d % 2 for _, d in classes), 'even input forbidden')
    Q = period(classes)
    require(Q % q == 0 and Q % p == 0, 'q and p must divide the original period')
    require(Q <= max_period, 'original complete-period finite-check cap exceeded')
    require(all(any(bits(classes, x)) for x in range(Q)),
            'original input does not cover its complete period')
    original_indices = [i for i, (_, d) in enumerate(classes) if d % q]
    qfree = [classes[i] for i in original_indices]
    B = Q // q**valuation(Q, q)
    residual = [x for x in range(B) if not any(bits(qfree, x))]
    roots = sorted({x % p for x in residual})
    require(len(roots) <= p-q, 'residual projection exceeds the contraction threshold')
    selected = ([x for x in range(p) if x not in roots][:q]
                if selected_roots is None else list(selected_roots))
    require(len(selected) == q and len(set(selected)) == q
            and all(0 <= x < p and x not in roots for x in selected),
            'invalid selected covered roots')
    root_map = {xi: b for b, xi in enumerate(selected)}
    K = valuation(B, p)
    R = B // p**K
    carrier = q * (B//p)
    require(carrier <= max_period, 'transport complete-period finite-check cap exceeded')
    output, provenance = [], []
    original_to_output = {}
    for i, (a, d) in enumerate(qfree):
        alpha = valuation(d, p)
        if alpha == 0:
            new_a, new_d, role = a, d, 'unchanged q-free p-free original'
        elif a % p in root_map:
            xi, r = a % p, d // p**alpha
            tail = p**(alpha-1)
            new_a = crt(root_map[xi], q, (a-xi)//p % tail, tail)
            new_a = crt(new_a, q*tail, a % r, r)
            new_d, role = q*(d//p), 'transported q-free original'
        else:
            continue
        original_to_output[i] = len(output)
        provenance.append(dict(original=original_indices[i], role=role))
        output.append((new_a, new_d))
    require(output and len({d for _, d in output}) == len(output),
            'empty output or repeated output modulus')
    require(all(d > 1 for _, d in output), 'output contains a unit modulus')
    require(allow_even or all(d % 2 for _, d in output), 'output is not odd')
    require(len(output) <= len(qfree) < len(classes),
            'contraction does not strictly reduce original class count')
    out_period = period(output)
    require(carrier % out_period == 0, 'output period does not divide transport carrier')
    images = {xi: set() for xi in selected}
    for z in range(carrier):
        xi = selected[z % q]
        old = crt(xi+p*(z % p**(K-1)), p**K, z % R, R)
        observed = bits(output, z)
        actual = bits(qfree, old)
        transported = tuple(observed[original_to_output[i]] if i in original_to_output else False
                            for i in range(len(qfree)))
        require(actual == transported and any(actual),
                'selected complete branch loses original q-free event vector or coverage')
        images[xi].add(old)
    for xi in selected:
        require(images[xi] == set(range(xi, B, p)),
                'transport misses a full old conditional source fibre')
        require(len(images[xi]) == carrier//q, 'conditional source map is not bijective')
    require(all(any(bits(output, z)) for z in range(out_period)),
            'output fails complete-period coverage')
    return dict(original=classes, original_period=Q, original_count=len(classes),
                q=q, p=p, original_q_height=valuation(Q, q), original_p_height=K,
                cofactor_period=B, cofactor_residual=residual, residual_p_roots=roots,
                qfree_original_count=len(qfree), selected_old_p_roots=selected,
                output_count=len(output), output=output, output_period=out_period,
                provenance=provenance, transport_carrier=carrier,
                original_event_coordinates_checked=carrier*len(qfree),
                conditional_source_points_checked=carrier,
                scope=('even control, not a minimum odd cover' if allow_even
                       else 'conditional odd-cover class-count descent'))


def contract_prefix_tree(classes, q, p, depth, *, child_preferences=None,
                         allow_even=False, max_period=200000):
    """Transport a complete good q-ary subtree of old p-adic prefixes.

    child_preferences maps old lowest-first digit tuples to permutations of
    range(p); the first q recursively good children in that order are used.
    It may vary independently at every node. Absence of a good subtree is
    rejected. Full checks are finite and bounded by max_period; the general
    proof does not impose a prime-height bound. No minimality is certified.
    """
    require(prime(q) and prime(p) and 2 < q < p, 'require odd primes q < p')
    classes = list(classes)
    require(classes and all(d > 1 for _, d in classes), 'original moduli must be nonunit')
    classes = [(a % d, d) for a, d in classes]
    require(len({d for _, d in classes}) == len(classes), 'original moduli must be distinct')
    require(allow_even or all(d % 2 for _, d in classes), 'even input forbidden')
    Q = period(classes)
    require(Q % q == 0 and Q % p == 0, 'q and p must divide the original period')
    require(Q <= max_period, 'original complete-period finite-check cap exceeded')
    H = valuation(Q, p)
    require(isinstance(depth, int) and 1 <= depth <= H, 'depth outside original p-height')
    require(all(any(bits(classes, z)) for z in range(Q)),
            'original input does not cover its complete period')
    original_indices = [i for i, (_, d) in enumerate(classes) if d % q]
    qfree = [classes[i] for i in original_indices]
    B = Q // q**valuation(Q, q)
    M = B // p**H
    residual = [z for z in range(B) if not any(bits(qfree, z))]
    bad_prefixes = {z % p**depth for z in residual}
    good = [None] * (depth + 1)
    good[depth] = [a not in bad_prefixes for a in range(p**depth)]
    for j in range(depth - 1, -1, -1):
        good[j] = [sum(good[j+1][a+d*p**j] for d in range(p)) >= q
                   for a in range(p**j)]
    require(good[0][0], 'no complete good q-ary prefix subtree')
    preferences = {} if child_preferences is None else child_preferences
    theta = [{0: 0}] + [{} for _ in range(depth)]
    node_choices = []
    for j in range(depth):
        for new, old in theta[j].items():
            prefix = tuple((old // p**i) % p for i in range(j))
            shift = (sum((i+1)*d for i, d in enumerate(prefix)) + j) % p
            default = list(range(shift, p)) + list(range(shift))
            order = list(preferences.get(prefix, default))
            require(len(order) == p and set(order) == set(range(p)),
                    'child preference is not a digit permutation')
            chosen = [d for d in order if good[j+1][old+d*p**j]][:q]
            require(len(chosen) == q, 'chosen prefix lacks q good children')
            node_choices.append(dict(old_prefix=list(prefix), new_prefix_residue=new,
                                     depth=j, selected_old_children=chosen))
            for b, d in enumerate(chosen):
                theta[j+1][new+b*q**j] = old+d*p**j
    for j in range(depth + 1):
        require(len(theta[j]) == q**j and len(set(theta[j].values())) == q**j,
                'prefix map is not injective on its complete domain')
        if j:
            require(all(old % p**(j-1) == theta[j-1][new % q**(j-1)]
                        for new, old in theta[j].items()), 'prefix maps do not commute')
    require(set(theta[depth].values()).isdisjoint(bad_prefixes),
            'selected prefix meets the original residual')
    inverse = [{old: new for new, old in layer.items()} for layer in theta]
    output, provenance, original_to_output = [], [], {}
    for i, (a, d) in enumerate(qfree):
        alpha = valuation(d, p)
        r = d // p**alpha
        if alpha == 0:
            new_a, new_d, role = a, d, 'unchanged q-free p-free original'
        elif alpha <= depth:
            prefix = a % p**alpha
            if prefix not in inverse[alpha]:
                continue
            b = inverse[alpha][prefix]
            new_a = crt(b, q**alpha, a % r, r)
            new_d, role = q**alpha*r, 'transported lower-or-equal prefix original'
        else:
            prefix = a % p**depth
            if prefix not in inverse[depth]:
                continue
            b = inverse[depth][prefix]
            tail_modulus = p**(alpha-depth)
            tail_residue = (a-prefix)//p**depth % tail_modulus
            new_a = crt(b, q**depth, tail_residue, tail_modulus)
            new_a = crt(new_a, q**depth*tail_modulus, a % r, r)
            new_d, role = q**depth*tail_modulus*r, 'transported original with complete higher p-tail'
        original_to_output[i] = len(output)
        provenance.append(dict(original=original_indices[i], original_p_exponent=alpha,
                               original_class=[a, d], output_class=[new_a, new_d], role=role))
        output.append((new_a, new_d))
    require(output and len({d for _, d in output}) == len(output),
            'empty output or repeated output modulus')
    require(all(d > 1 for _, d in output), 'output contains a unit modulus')
    require(allow_even or all(d % 2 for _, d in output), 'output is not odd')
    require(len(output) <= len(qfree) < len(classes), 'no strict class-count descent')
    carrier = q**depth * p**(H-depth) * M
    require(carrier <= max_period, 'transport complete-period finite-check cap exceeded')
    out_period = period(output)
    require(carrier % out_period == 0, 'output period does not divide transport carrier')
    # Enumerated CRT coordinate lookup is independent of the output residue
    # construction's crt calculations. All events use the same old point.
    source_lookup = {(y % p**H, y % M): y for y in range(B)}
    require(len(source_lookup) == B, 'source CRT coordinates are not unique')
    images = set()
    leaf_images = {b: set() for b in range(q**depth)}
    for z in range(carrier):
        b = z % q**depth
        old_p = theta[depth][b] + p**depth * (z % p**(H-depth))
        old = source_lookup[(old_p, z % M)]
        actual, observed = bits(qfree, old), bits(output, z)
        transported = tuple(observed[original_to_output[i]] if i in original_to_output else False
                            for i in range(len(qfree)))
        require(actual == transported and any(actual),
                'selected prefix subtree loses complete original q-free event vector or coverage')
        images.add(old)
        leaf_images[b].add(old)
    selected = set(theta[depth].values())
    require(images == {y for y in range(B) if y % p**depth in selected}
            and len(images) == carrier, 'prefix source map is not bijective onto selected full fibres')
    for b, points in leaf_images.items():
        require(len(points) == p**(H-depth)*M
                and all(y % p**depth == theta[depth][b] for y in points),
                'prefix conditional source fibre mismatch')
    require(all(any(bits(output, z)) for z in range(out_period)),
            'output fails complete-period coverage')
    return dict(original=classes, original_period=Q, original_count=len(classes), q=q, p=p,
                depth=depth, original_q_height=valuation(Q, q), original_p_height=H,
                cofactor_period=B, cofactor_residual=residual,
                residual_p_prefixes=sorted(bad_prefixes),
                tree_blocker_threshold=(p-q+1)**depth,
                qfree_original_count=len(qfree), selected_prefix_maps=theta,
                node_choices=node_choices, output_count=len(output), output=output,
                output_period=out_period, provenance=provenance, transport_carrier=carrier,
                original_event_coordinates_checked=carrier*len(qfree),
                conditional_source_points_checked=carrier,
                scope=('even control, not a minimum odd cover' if allow_even
                       else 'conditional odd-cover prefix-tree class-count descent'))


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


def prefix_tree_controls(original5040):
    """Actual whole covers exercising variable prefixes and all height cases."""
    seed = original5040 + [(11, 25), (36, 125), (186, 625), (2, 200), (92, 1000)]
    preferences = {(): [0, 1, 2, 3, 4], (0,): [0, 1, 3, 2, 4],
                   (1,): [2, 0, 4, 1, 3], (2,): [0, 3, 1, 2, 4],
                   (1, 2): [1, 2, 4, 0, 3], (2, 3): [3, 1, 4, 0, 2]}
    rows = []
    for depth in (1, 2, 3, 4):
        item = contract_prefix_tree(seed, 3, 5, depth, child_preferences=preferences,
                                    allow_even=True, max_period=1000000)
        live = {r['original_p_exponent'] for r in item['provenance']}
        choices = {tuple(sorted(r['selected_old_children']))
                   for r in item['node_choices'] if r['depth'] > 0}
        if depth in (2, 3):
            require(any(0 < a < depth for a in live) and depth in live
                    and any(a > depth for a in live), 'missing live positive-height case')
            require(len(choices) > 1, 'nonroot child sets do not vary')
        if depth == 1:
            legacy = contract_small_projection(seed, 3, 5, selected_roots=[0, 1, 2],
                                               allow_even=True, max_period=1000000)
            require(item['output'] == legacy['output'], 'depth-one constructor disagreement')
        if depth == 4:
            require(all(d % 5 for _, d in item['output']), 'full-depth transport retained p')
        row = {key: item[key] for key in
               ('depth', 'original_count', 'qfree_original_count', 'output_count',
                'original_period', 'original_p_height', 'output_period', 'transport_carrier',
                'original_event_coordinates_checked', 'conditional_source_points_checked')}
        row.update(bad_prefix_count=len(item['residual_p_prefixes']),
                   tree_blocker_threshold=item['tree_blocker_threshold'],
                   different_nonroot_child_sets=len(choices),
                   retained_positive_p_exponents=sorted(live - {0}))
        rows.append(row)
    rejections = []
    bad_inputs = [
        (seed, 0, dict(allow_even=True, max_period=1000000), 'depth outside'),
        (seed, 5, dict(allow_even=True, max_period=1000000), 'depth outside'),
        (seed, 2, dict(max_period=1000000), 'even input forbidden'),
        (seed, 2, dict(allow_even=True, max_period=1000000,
                      child_preferences={(): [0, 0, 1, 2, 3]}), 'not a digit permutation'),
        ([(0, 2), (0, 3), (1, 4), (5, 6), (7, 12), (0, 25)], 2,
         dict(allow_even=True), 'no complete good q-ary'),
    ]
    for bad_seed, depth, options, expected in bad_inputs:
        try:
            contract_prefix_tree(bad_seed, 3, 5, depth, **options)
        except ValueError as exc:
            require(expected in str(exc), 'wrong prefix-tree rejection: '+str(exc))
            rejections.append(str(exc))
        else:
            raise ValueError('invalid prefix-tree input unexpectedly admitted')
    return dict(controls=rows, rejections=rejections,
                event_coordinates_checked=sum(r['original_event_coordinates_checked'] for r in rows),
                source_points_checked=sum(r['conditional_source_points_checked'] for r in rows),
                scope='Even controls; no minimum odd cover or whole original Haar transport')


def cross_joint_probability_control():
    """Actual irredundant EVEN whole cover; two separate laws have no common law.

    This checks the projection-to-common-law nonimplication on original APs.
    It does not certify global cardinality minimality or an odd counterexample.
    """
    classes = [
        (0, 2), (1, 4), (3, 8), (7, 16), (15, 32), (31, 64), (63, 128),
        (3, 5), (9, 10), (5, 7), (13, 14),
        (1, 35), (51, 70), (31, 140), (151, 280),
        (127, 560), (1087, 1120), (2047, 2240), (767, 4480),
        (0, 3), (895, 1920), (511, 2688), (575, 960), (959, 1344),
    ]
    Q = period(classes)
    require(Q == 13440 and len(classes) == 24, 'cross control size/period')
    require(len({d for _, d in classes}) == len(classes), 'cross repeated modulus')
    require(all(d > 1 for _, d in classes) and any(d % 2 == 0 for _, d in classes),
            'cross control must be explicitly even and nonunit')
    private = [None]*len(classes)
    for x in range(Q):
        vector = bits(classes, x)
        require(any(vector), 'cross control does not cover its whole period')
        if sum(vector) == 1:
            j = vector.index(True)
            if private[j] is None:
                private[j] = x
    require(all(x is not None for x in private), 'cross control is redundant')
    B = Q//3**valuation(Q, 3)
    q_free = [(a, d) for a, d in classes if d % 3]
    residual = [x for x in range(B) if not any(bits(q_free, x))]
    expected = [255, 511, 1407, 1535, 2815, 3455, 4095]
    require(B == 4480 and residual == expected, 'cross actual residual changed')
    graph = {(x % 5, x % 7) for x in residual}
    cross = {(0, y) for y in range(5)} | {(1, 0), (2, 0)}
    require(graph == cross and all(x % 128 == 127 for x in residual),
            'cross joint source was not retained')
    require(valuation(Q, 5) == valuation(Q, 7) == 1,
            'cross has only depth-one large-prime coordinates')
    require(len({x % 5 for x in residual}) == 5-3+1
            and len({x % 7 for x in residual}) == 7-3+1,
            'cross does not meet both ternary deep bounds')
    # Exhibit the two individually valid actual-source laws.
    individual = {}
    for p in (5, 7):
        r0 = p-3+1
        roots = sorted({x % p for x in residual})
        witnesses = [next(x for x in residual if x % p == c) for c in roots]
        require(len(witnesses) == r0, 'cross individual law count')
        for c in range(p):
            cylinder_mass = F(sum(x % p == c for x in witnesses), r0)
            require(cylinder_mass <= F(1, r0), 'cross individual cylinder cap')
        individual[p] = dict(witnesses=witnesses, equal_atom_mass=str(F(1, r0)))
    # A common probability would give 1 <= nu(x5=0)+nu(x7=0) <= 8/15.
    require(all(x % 5 == 0 or x % 7 == 0 for x in residual), 'cross cut support')
    cut_capacity = F(1, 3)+F(1, 5)
    require(cut_capacity < 1, 'cross does not separate the law quantifiers')
    return dict(
        classes=classes, period=Q, cofactor_period=B, private_witnesses=private,
        actual_R3=residual, joint_5_7_projection=sorted(graph),
        prime_heights={5: 1, 7: 1}, projection_sizes={5: 3, 7: 5},
        individual_supported_laws=individual,
        common_law_cut_capacity=str(cut_capacity), deficit=str(1-cut_capacity),
        scope='Actual distinct irredundant even whole cover; no odd or globally minimum claim',
    )


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
    original5040 = [
        (0, 2), (0, 3), (1, 4), (0, 5), (0, 7), (3, 8), (4, 9),
        (7, 10), (5, 14), (14, 15), (15, 16), (11, 20), (10, 21),
        (11, 28), (23, 40), (19, 45), (23, 56), (43, 63), (55, 112),
    ]
    contraction_specs = [
        ('5040, original p becomes q', original5040, 3, 5, None),
        ('5040, omit original p root', original5040, 3, 5, [1, 2, 3]),
        ('5040, a different large prime', original5040, 3, 7, None),
        ('5040, s=p-q boundary', original5040, 5, 7, None),
        ('translated original labels', [(a+37, d) for a, d in original5040], 3, 5, None),
        ('retained p^3 and mixed p^2', original5040+[(36, 125), (2, 200)], 3, 5, None),
    ]
    contractions = []
    for name, seed, q, p, selected in contraction_specs:
        item = contract_small_projection(seed, q, p, selected_roots=selected, allow_even=True)
        item['case'] = name
        contractions.append(item)
    require(any(d == 3 for _, d in contractions[0]['output']), 'original p failed to become q')
    require(all(d != 3 for _, d in contractions[1]['output']), 'omitted pure-p root survived')
    require(len(contractions[3]['residual_p_roots']) == 7-5, 'threshold endpoint not exercised')
    require({75, 120}.issubset({d for _, d in contractions[-1]['output']}),
            'higher pure or mixed p digits were not retained')
    contraction_rejections = []
    bad_inputs = [
        (original5040, 3, 5, {}, 'even input forbidden'),
        (original5040+[(1, 2)], 3, 5, dict(allow_even=True), 'original moduli must be distinct'),
        (original5040[:-1], 3, 5, dict(allow_even=True), 'does not cover'),
        (original5040, 3, 5, dict(allow_even=True, selected_roots=[0, 1, 4]), 'invalid selected'),
        (original5040, 3, 5, dict(allow_even=True, selected_roots=[0, 0, 1]), 'invalid selected'),
        (original5040, 3, 11, dict(allow_even=True), 'must divide'),
        ([(0, 2), (0, 3), (1, 4), (5, 6), (7, 12), (0, 5)],
         3, 5, dict(allow_even=True), 'exceeds the contraction threshold'),
        (original5040, 3, 5, dict(allow_even=True, max_period=5000), 'finite-check cap'),
    ]
    for seed, q, p, options, expected in bad_inputs:
        try:
            contract_small_projection(seed, q, p, **options)
        except ValueError as exc:
            require(expected in str(exc), 'wrong contraction rejection: '+str(exc))
            contraction_rejections.append(str(exc))
        else:
            raise ValueError('invalid contraction fixture unexpectedly admitted')
    summary = [{key: result[key] for key in
                ('case', 'p', 'q', 's', 't', 'k', 'input_p_height', 'input_period',
                 'output_period', 'joint_transport_carrier', 'output_excess')}
               for result in results]
    contraction_summary = [{key: item[key] for key in
                           ('case', 'q', 'p', 'original_count', 'output_count', 'original_period',
                            'output_period', 'residual_p_roots', 'selected_old_p_roots',
                            'original_p_height', 'original_q_height', 'transport_carrier')}
                           for item in contractions]
    print(json.dumps(dict(success=True, fixtures=summary, rejection_count=len(rejections),
                          rejections=rejections,
                          prefix_tree_contractions=prefix_tree_controls(original5040),
                          cross_joint_probability=cross_joint_probability_control(),
                          projection_contractions=contraction_summary,
                          contraction_rejections=contraction_rejections,
                          contraction_event_coordinates_checked=sum(
                              item['original_event_coordinates_checked'] for item in contractions),
                          contraction_source_points_checked=sum(
                              item['conditional_source_points_checked'] for item in contractions),
                          checked_period_points=sum(r['checked_period_points'] for r in results),
                          conditional_source_points_checked=sum(r['conditional_source_points_checked']
                                                                 for r in results),
                          scope='Actual covers with even cofactors; no distinct all-odd witness or Lean claim'),
                     sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
