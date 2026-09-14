#!/usr/bin/env python3
"""Exact finite probes for task-relative ML closure, using only the standard library.

The raw parameter dynamics and reduced dynamics are evaluated independently.
The finite families can detect algebraic mistakes and find counterexamples;
they are not proofs of the volume's universal assertions. With --output, writes
one deterministic JSON result including the source digest and exact scope.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as F
import hashlib
from itertools import product
import json
from pathlib import Path
from random import Random

SEED = 20270914
RNG = Random(SEED)
COUNTS: dict[str, int] = {}


def record(name, count=1):
    COUNTS[name] = COUNTS.get(name, 0) + count


def rat():
    return F(RNG.randint(-4, 4), RNG.randint(1, 5))


def dot(a, b):
    return sum((x * y for x, y in zip(a, b)), F(0))


def add(a, b):
    return [x + y for x, y in zip(a, b)]


def scale(c, a):
    return [c * x for x in a]


def transpose(a):
    return [list(c) for c in zip(*a)]


def mm(a, b):
    return [[dot(row, col) for col in transpose(b)] for row in a]


def madd(a, b):
    return [add(x, y) for x, y in zip(a, b)]


def ms(c, a):
    return [scale(c, row) for row in a]


def gram(a):
    return mm(transpose(a), a)


def mat(rows, cols):
    return [[rat() for _ in range(cols)] for _ in range(rows)]


def ws(u, v):
    return dot(u, v), dot(u, u) + dot(v, v)


def reduced(w, s, g, eta):
    alpha = eta * g
    return ((1 + alpha * alpha) * w - alpha * s,
            (1 + alpha * alpha) * s - 4 * alpha * w)


def regression():
    for trial in range(48):
        data = [(rat(), rat()) for _ in range(1 + trial % 7)]
        if trial % 8 == 0:
            data = [(F(0), y) for _, y in data]
        n = len(data)
        a = sum(x * x for x, _ in data) / n
        b = sum(x * y for x, y in data) / n
        c = sum(y * y for _, y in data) / n
        raw_w = rat()
        summary_w = raw_w
        initial = raw_w
        eta = F(1, 10)
        for step in range(1, 6):
            grad = sum((raw_w * x - y) * x for x, y in data) / n
            raw_w -= eta * grad
            summary_w = (1 - eta * a) * summary_w + eta * b
            assert raw_w == summary_w
            loss = sum((raw_w * x - y) ** 2 for x, y in data) / (2 * n)
            assert loss == (a * raw_w**2 - 2 * b * raw_w + c) / 2
            if a:
                assert raw_w == b / a + (1 - eta * a)**step * (initial - b / a)
            else:
                assert b == 0 and raw_w == initial
        record('regression_trajectories')
    a, b, c = F(14, 3), F(28, 3), F(56, 3)
    data = [(F(i), F(2 * i)) for i in (1, 2, 3)]
    assert (a, b, c) == (sum(x*x for x, _ in data)/3,
                         sum(x*y for x, y in data)/3,
                         sum(y*y for _, y in data)/3)
    w = F(0)
    for t in range(1, 11):
        w -= F(1, 10) * sum((w*x-y)*x for x, y in data)/3
        assert w == 2 * (1 - F(8, 15)**t)
    record('worked_regression_trajectory')
    # Training output is not sufficient for a row outside the design rowspace.
    design = [[F(1), F(0)], [F(2), F(0)]]
    assert mm(design, [[F(0)], [F(0)]]) == mm(design, [[F(0)], [F(1)]])


def two_layer():
    for width in (1, 2, 3, 5, 8):
        for _ in range(18):
            u, v = [rat() for _ in range(width)], [rat() for _ in range(width)]
            w, s = ws(u, v)
            a, b, eta = abs(rat()), rat(), F(1, 10)
            for _step in range(4):
                g_raw = a * dot(u, v) - b
                new_u = [ui - eta * g_raw * vi for ui, vi in zip(u, v)]
                new_v = [vi - eta * g_raw * ui for ui, vi in zip(u, v)]
                g = a * w - b
                w1, s1 = reduced(w, s, g, eta)
                assert ws(new_u, new_v) == (w1, s1)
                p, n = dot(add(u, v), add(u, v)), dot(add(u, scale(-1, v)), add(u, scale(-1, v)))
                assert (w, s) == ((p-n)/4, (p+n)/2)
                assert dot(add(new_u, new_v), add(new_u, new_v)) == (1-eta*g)**2*p
                assert dot(add(new_u, scale(-1, new_v)), add(new_u, scale(-1, new_v))) == (1+eta*g)**2*n
                assert s1*s1-4*w1*w1 == (1-(eta*g)**2)**2*(s*s-4*w*w)
                assert s1 >= 2*abs(w1)
                # The flow derivative is zero; no finite-step invariance is assumed.
                assert 2*s*(-4*g*w)-8*w*(-g*s) == 0
                u, v, w, s = new_u, new_v, w1, s1
            record('two_layer_trajectories')


def matrix_closure():
    for width, d, k in product((1, 2, 5), (1, 2, 3), (1, 2)):
        for _ in range(6):
            u, v, target = mat(width, d), mat(k, width), mat(k, d)
            eta = F(1, 10)
            raw_g = madd(mm(v, u), ms(-1, target))
            new_u = madd(u, ms(-eta, mm(transpose(v), raw_g)))
            new_v = madd(v, ms(-eta, mm(raw_g, transpose(u))))
            w, a, b = mm(v, u), gram(u), mm(v, transpose(v))
            g = madd(w, ms(-1, target))
            w1 = madd(madd(w, ms(-eta, madd(mm(b, g), mm(g, a)))),
                       ms(eta**2, mm(mm(g, transpose(w)), g)))
            a1 = madd(madd(a, ms(-eta, madd(mm(transpose(w), g), mm(transpose(g), w)))),
                       ms(eta**2, mm(mm(transpose(g), b), g)))
            b1 = madd(madd(b, ms(-eta, madd(mm(w, transpose(g)), mm(g, transpose(w))))),
                       ms(eta**2, mm(mm(g, a), transpose(g))))
            assert w1 == mm(new_v, new_u)
            assert a1 == gram(new_u)
            assert b1 == mm(new_v, transpose(new_v))
            z = [ur + vr for ur, vr in zip(u, transpose(v))]
            block = [ar + wr for ar, wr in zip(a, transpose(w))] + [wr + br for wr, br in zip(w, b)]
            assert gram(z) == block
            record('matrix_cases')


def momentum():
    for width in (1, 2, 4, 8, 16):
        for _ in range(12):
            u, v, p, q = ([rat() for _ in range(width)] for _ in range(4))
            a, b, eta, beta = abs(rat()), rat(), F(1, 10), F(4, 5)
            summary = gram(transpose([u, v, p, q]))
            for _step in range(3):
                g_raw = a*dot(u, v)-b
                pn, qn = add(scale(beta, p), scale(g_raw, v)), add(scale(beta, q), scale(g_raw, u))
                un, vn = add(u, scale(-eta, pn)), add(v, scale(-eta, qn))
                g = a*summary[0][1]-b
                m = [[F(1), -eta*g, F(0), g], [-eta*g, F(1), g, F(0)],
                     [-eta*beta, F(0), beta, F(0)], [F(0), -eta*beta, F(0), beta]]
                summary = mm(mm(transpose(m), summary), m)
                assert summary == gram(transpose([un, vn, pn, qn]))
                u, v, p, q = un, vn, pn, qn
            record('momentum_trajectories')


def canonical(values):
    ids = {}
    return tuple(ids.setdefault(value, len(ids)) for value in values)


def words(actions, h):
    return [w for size in range(h+1) for w in product(actions, repeat=size)]


def partition_check(states, actions, trans, obs, horizon, raw_response=None):
    labels = canonical(obs(x) for x in states)
    index = {x: i for i, x in enumerate(states)}
    for h in range(horizon+1):
        def response(x, word):
            if raw_response is not None:
                return raw_response(x, word)
            for action in word:
                x = trans(x, action)
                if x is None:
                    return ('fail',)
            return ('ok', obs(x))
        brute = canonical(tuple(response(x, w) for w in words(actions, h)) for x in states)
        assert labels == brute
        record('partition_horizon_comparisons')
        signatures = []
        for x in states:
            next_classes = []
            for action in actions:
                nxt = trans(x, action)
                next_classes.append(-1 if nxt is None else labels[index[nxt]])
            signatures.append((obs(x), tuple(next_classes)))
        yield len(set(labels))
        labels = canonical(signatures)


def finite_automata():
    for size in (1, 2):
        states, actions = list(range(size)), (0, 1)
        for table in product(range(-1, size), repeat=2*size):
            def trans(x, action):
                value = table[2*x+action]
                return None if value == -1 else value
            for output in product((0, 1), repeat=size):
                list(partition_check(states, actions, trans, lambda x: output[x], 4))
                record('exhaustive_partial_automata')


def mobius_integer(n):
    sign, p = 1, 2
    while p*p <= n:
        if n % p == 0:
            n //= p
            sign = -sign
            if n % p == 0:
                return 0
        p += 1
    return -sign if n > 1 else sign


def capacity_boxes():
    out = {}
    cases = ((5040, (2, 3, 5, 7), (4, 2, 1, 1), (3, 32, 52, 56, 60)),
             (210, (2, 3, 5, 7), (1, 1, 1, 1), (2, 16, 16, 16, 16)),
             (30030, (2, 3, 5, 7, 11, 13), (1, 1, 1, 1, 1, 1), (2, 64, 64, 64, 64)))
    for bound, primes, capacity, expected in cases:
        states = list(product(*(range(a+1) for a in capacity)))
        def trans(x, axis):
            if x[axis] == capacity[axis]:
                return None
            y = list(x)
            y[axis] += 1
            return tuple(y)
        def obs(x):
            return 0 if max(x) >= 2 else (-1)**sum(x)
        def raw(x, word):
            n = 1
            for p, e in zip(primes, x):
                n *= p**e
            for axis in word:
                n *= primes[axis]
                if bound % n:
                    return ('fail',)
            return ('ok', mobius_integer(n))
        counts = tuple(partition_check(states, tuple(range(len(primes))), trans, obs, 4, raw))
        assert counts == expected
        for h in range(1, 5):
            first = second = 1
            for a in capacity:
                first *= min(a, h)+1
                second *= max(0, min(a, h)-a+2)
            assert counts[h] == 2**len(primes)+first-second
        out[str(bound)] = {'capacities': capacity, 'states': len(states), 'classes_h0_to_h4': counts,
                           'minimum_label_bits': [(n-1).bit_length() for n in counts]}
        if bound == 5040:
            nine, eighteen = (0, 2, 0, 0), (1, 2, 0, 0)
            assert all(raw(nine, w) == raw(eighteen, w) for w in words(tuple(range(4)), 3))
            assert raw(nine, (0,)*4) == ('ok', 0)
            assert raw(eighteen, (0,)*4) == ('fail',)
        record('capacity_boxes')
    return out


@dataclass(frozen=True)
class QC:
    """A rational complex number, with no floating-point operations."""
    re: F = F(0)
    im: F = F(0)

    @staticmethod
    def lift(value):
        return value if isinstance(value, QC) else QC(F(value))

    def __add__(self, other):
        other = QC.lift(other)
        return QC(self.re+other.re, self.im+other.im)

    __radd__ = __add__

    def __neg__(self):
        return QC(-self.re, -self.im)

    def __mul__(self, other):
        other = QC.lift(other)
        return QC(self.re*other.re-self.im*other.im, self.re*other.im+self.im*other.re)

    __rmul__ = __mul__

    def conj(self):
        return QC(self.re, -self.im)


def dagger(a):
    return [[x.conj() for x in row] for row in transpose(a)]


def density(x, y, z):
    return [[QC((1+z)/2), QC(x/2, -y/2)], [QC(x/2, y/2), QC((1-z)/2)]]


def quantum():
    h0 = [[QC(F(1)), QC(F(1))], [QC(F(1)), QC(F(-1))]]
    sg = [[QC(F(1)), QC()], [QC(), QC(F(0), F(1))]]
    zgate = [[QC(F(1)), QC()], [QC(), QC(F(-1))]]
    axis = [F(i, 2) for i in range(-2, 3)]
    for xyz in product(axis, repeat=3):
        if sum(v*v for v in xyz) > 1:
            continue
        record('bloch_initial_states')
        for word in words(('H', 'S'), 4):
            rho = density(*xyz)
            x, y, z = xyz
            for gate in word:
                if gate == 'H':
                    rho = ms(F(1, 2), mm(mm(h0, rho), dagger(h0)))
                    x, y, z = z, -y, x
                else:
                    rho = mm(mm(sg, rho), dagger(sg))
                    x, y, z = -y, x, z
            assert rho == density(x, y, z)
            record('quantum_word_cases')
    plus, minus = density(F(1), F(0), F(0)), density(F(-1), F(0), F(0))
    def dephase(rho):
        return ms(F(1, 2), madd(rho, mm(mm(zgate, rho), zgate)))
    assert dephase(plus) == dephase(minus) == density(F(0), F(0), F(0))


def hidden_memory():
    for _ in range(72):
        a, b, c, d, x, hidden = [rat() for _ in range(6)]
        initial_hidden = hidden
        xs = [x]
        for t in range(6):
            assert hidden == d**t*initial_hidden+c*sum(d**(t-1-j)*xs[j] for j in range(t))
            visible_history_update = a*x+b*c*sum(d**(t-1-j)*xs[j] for j in range(t))+b*d**t*initial_hidden
            x, hidden = a*x+b*hidden, c*x+d*hidden
            assert x == visible_history_update
            xs.append(x)
        for t in range(5):
            assert xs[t+2] == (a+d)*xs[t+1]+(b*c-a*d)*xs[t]
        record('hidden_memory_trajectories')


def lipschitz():
    for _ in range(108):
        a, b, eta = abs(rat()), rat(), F(1, 10)
        w_bound, s_bound = F(RNG.randint(1, 4)), F(RNG.randint(1, 8))
        g_bound = a*w_bound+abs(b)
        first = 1+eta**2*g_bound**2+2*eta**2*a*g_bound*w_bound+eta*a*s_bound+eta*g_bound
        second = 1+eta**2*g_bound**2+2*eta**2*a*g_bound*s_bound+4*eta*a*w_bound+4*eta*g_bound
        bound = max(first, second)
        w, s = F(RNG.randint(-10, 10), 10)*w_bound, F(RNG.randint(0, 10), 10)*s_bound
        z, t = F(RNG.randint(-10, 10), 10)*w_bound, F(RNG.randint(0, 10), 10)*s_bound
        fw, fs = reduced(w, s, a*w-b, eta)
        fz, ft = reduced(z, t, a*z-b, eta)
        assert max(abs(fw-fz), abs(fs-ft)) <= bound*max(abs(w-z), abs(s-t))
        g = a*w-b
        row1 = abs(1+eta**2*g*g+2*eta**2*a*g*w-eta*a*s)+abs(-eta*g)
        row2 = abs(2*eta**2*a*g*s-4*eta*a*w-4*eta*g)+abs(1+eta**2*g*g)
        assert row1 <= first and row2 <= second
        record('lipschitz_box_pairs')


def approximation_counterexamples():
    """Exact witnesses separating stability, state error, and task output error."""
    epsilon = F(1, 100)
    squaring_cases = []
    for initial, expected_e2 in zip((F(1), F(10), F(100)),
                                   (F(301, 10000), F(20101, 10000), F(2000101, 10000))):
        actual = approximate = initial
        errors = [abs(actual-approximate)]
        for _ in range(2):
            actual = actual**2
            approximate = approximate**2+epsilon
            assert actual >= 0 and approximate >= 0
            errors.append(abs(actual-approximate))
        # At the second update the two inputs have this exact secant slope.
        left, right = initial**2, initial**2+epsilon
        slope = (right**2-left**2)/(right-left)
        assert slope == 2*initial**2+epsilon
        assert errors == [F(0), epsilon, expected_e2]
        assert errors[2] == epsilon*(slope+1)
        squaring_cases.append({'x0': str(initial), 'state_errors_h0_to_h2': list(map(str, errors)),
                               'second_step_secant_slope': str(slope)})
        record('regional_missing_stability_cases')

    threshold_cases = []
    output = lambda value: int(value > 0)
    identity = lambda value: value
    budget = F(1, 2)
    for a in (F(1, 10), F(1, 100), F(1, 10000)):
        actual, approximate = -a, a
        state_errors, output_errors = [], []
        for _ in range(3):
            assert -1 <= actual <= 1 and -1 <= approximate <= 1
            state_errors.append(abs(actual-approximate))
            output_errors.append(abs(output(actual)-output(approximate)))
            actual, approximate = identity(actual), identity(approximate)
        assert state_errors == [2*a]*3
        assert all(error < budget for error in state_errors)
        assert output_errors == [1]*3 and all(error > budget for error in output_errors)
        threshold_cases.append({'a': str(a), 'initial_exact': str(-a), 'initial_approximate': str(a),
                                'state_errors_h0_to_h2': list(map(str, state_errors)),
                                'output_errors_h0_to_h2': output_errors})
        record('state_error_without_readout_regularity_cases')

    return {
        'regional_missing_stability': {
            'domain': '[0,infinity)', 'regions': 1, 'actions': 1, 'guard': 'constant true',
            'q': 'identity', 'T_and_F': 'x^2', 'Fhat': 'x^2+epsilon', 'output': 'x', 'cost': '0',
            'delta_close': '0', 'delta_eval': str(epsilon), 'cases': squaring_cases},
        'state_error_without_readout_regularity': {
            'domain': '[-1,1]', 'regions': 1, 'actions': 1, 'guard': 'constant true',
            'q_T_F_Fhat': 'identity', 'L': '1', 'delta_close': '0', 'delta_eval': '0',
            'output': '1{x>0}', 'output_evaluation_error': '0',
            'requested_output_budget_each_h0_to_h2': str(budget), 'cases': threshold_cases}}


def counterexamples():
    eta = F(1, 10)
    def step(u, v):
        g = u*v
        return (u-eta*g*v)*(v-eta*g*u)
    x, y = step(F(1), F(1)), step(F(2), F(1, 2))
    assert (x, y, x-y, (x-y)/2) == (F(81, 100), F(117, 200), F(9, 40), F(9, 80))
    assert ws([F(1)], [F(2)]) == ws([F(2)], [F(1)])
    assert F(1)*F(2) != F(1)*F(1)  # u := 1
    assert ws([F(1)], [F(2)]) == ws([F(-1)], [F(-2)])
    assert F(2)*max(0, F(1)) != F(-2)*max(0, F(-1))
    f = lambda theta: theta**3-theta
    fp = lambda theta: 3*theta**2-1
    fpp = lambda theta: 6*theta
    kdot = [-2*fp(t)**2*fpp(t)*(f(t)-1) for t in (F(1), F(-1))]
    assert kdot == [F(48), F(-48)]
    w1, s1 = reduced(F(2), F(5), F(2), eta)
    assert (w1, s1, s1*s1-4*w1*w1) == (F(27, 25), F(18, 5), F(5184, 625))
    xor_accuracy = {}
    for name, predictor in [('ignore', lambda b, r: b), ('use', lambda b, r: b ^ r),
                            ('reverse', lambda b, r: 1 ^ b ^ r)]:
        xor_accuracy[name] = F(sum(predictor(b, r) == b ^ r for b, r in product((0, 1), repeat=2)), 4)
    assert xor_accuracy == {'ignore': F(1, 2), 'use': F(1), 'reverse': F(0)}
    # Same final marginal, different full transcript laws.
    correlated = {(0, 0): F(1, 2), (1, 1): F(1, 2)}
    anticorrelated = {(0, 1): F(1, 2), (1, 0): F(1, 2)}
    marginal = lambda law: [sum(p for ys, p in law.items() if ys[-1] == y) for y in (0, 1)]
    assert correlated != anticorrelated and marginal(correlated) == marginal(anticorrelated)
    # Fixed-loss stationary fibers can have different s forever.
    stationary = [(F(1), F(1)), (F(2), F(1, 2))]
    assert len({u*u+v*v for u, v in stationary}) == 2
    for u, v in stationary:
        g = u*v-1
        assert g == 0 and (u-eta*g*v, v-eta*g*u) == (u, v)
    # Same weights, distinct optimizer memory.
    assert (F(1)-eta*F(0))*F(1) == 1
    assert (F(1)-eta*F(1))*F(1) == F(9, 10)
    # Coordinate-sensitive preconditioners distinguish identical Gram data.
    assert (1-eta)**2 == F(81, 100)
    assert (1-2*eta)**2 == F(16, 25)
    # A positive ReLU cell need not remain positive after synchronous GD.
    u, v, g = F(1), F(2), F(2)
    assert (u-g*v, v-g*u) == (F(-3), F(0))
    # Existential quotient edges can have no common concrete lift.
    edges = {('a', 'b'), ('c', 'd')}
    classes = {'a': 'A', 'b': 'B', 'c': 'B', 'd': 'D'}
    assert {(classes[a], classes[b]) for a, b in edges} == {('A', 'B'), ('B', 'D')}
    assert not any((a, middle) in edges and (middle, d) in edges
                   for a, middle, d in product(classes, repeat=3))
    families = ['same_w_different_next_w', 'coordinate_intervention', 'relu_prediction',
                'ntk_nonclosure', 'flow_invariant_not_discrete_invariant', 'xor_use_and_misuse',
                'terminal_marginal_not_transcript', 'stationary_fiber_exception',
                'optimizer_memory', 'coordinate_preconditioning', 'relu_region_exit',
                'quotient_path_without_common_lift']
    approximation = approximation_counterexamples()
    families.extend(approximation)
    record('named_counterexample_families', len(families))
    return {'two_layer_next_w': [str(x), str(y)], 'pair_difference': str(x-y),
            'minimax_absolute_error': str((x-y)/2), 'ntk_Kdot': list(map(str, kdot)),
            'discrete_C_before_after': ['9', str(s1*s1-4*w1*w1)],
            'families': families, 'approximation': approximation,
            'xor_accuracy': {k: str(v) for k, v in xor_accuracy.items()}}


def stochastic_records():
    """Enumerate joint kernels and complete records with exact rational laws."""
    def tv(left, right):
        return sum((abs(left.get(key, F(0))-right.get(key, F(0)))
                    for key in left.keys() | right.keys()), F(0))/2

    def push(law, mapping):
        out = {}
        for key, mass in law.items():
            target = mapping(key)
            out[target] = out.get(target, F(0))+mass
        return out

    def traces(kernel, initial, horizon):
        # Initial public output and the singleton action are common constants.
        law = {(('o',), initial): F(1)}
        for _ in range(horizon):
            next_law = {}
            for (trace, state), mass in law.items():
                for (output, nxt), probability in kernel[state].items():
                    key = (trace+('a', output), nxt)
                    next_law[key] = next_law.get(key, F(0))+mass*probability
            law = next_law
        out = push(law, lambda pair: pair[0])
        assert sum(out.values()) == 1 and all(p >= 0 for p in out.values())
        return out

    joint_kernel = {
        'x': {(0, 't0'): F(1, 2), (1, 't1'): F(1, 2)},
        'xprime': {(0, 't1'): F(1, 2), (1, 't0'): F(1, 2)},
        't0': {(0, 'stop'): F(1)}, 't1': {(1, 'stop'): F(1)},
        'stop': {('#', 'stop'): F(1)},
    }
    summary = {'x': 's', 'xprime': 's', 't0': 'q0', 't1': 'q1', 'stop': 'end'}
    left, right = (joint_kernel[state] for state in ('x', 'xprime'))
    assert push(left, lambda pair: pair[0]) == push(right, lambda pair: pair[0])
    assert push(left, lambda pair: summary[pair[1]]) == push(right, lambda pair: summary[pair[1]])
    assert tv(push(left, lambda pair: (pair[0], summary[pair[1]])),
              push(right, lambda pair: (pair[0], summary[pair[1]]))) == 1
    trace_left, trace_right = (traces(joint_kernel, state, 2) for state in ('x', 'xprime'))
    assert trace_left == {('o', 'a', 0, 'a', 0): F(1, 2), ('o', 'a', 1, 'a', 1): F(1, 2)}
    assert trace_right == {('o', 'a', 0, 'a', 1): F(1, 2), ('o', 'a', 1, 'a', 0): F(1, 2)}
    assert tv(trace_left, trace_right) == 1
    record('stochastic_joint_law_cases')

    parameters = (F(0), F(1, 2), F(1))
    bernoulli_kernel = {p: {(0, 'stop'): 1-p, (1, 'stop'): p} for p in parameters}
    bernoulli_kernel['stop'] = {('#', 'stop'): F(1)}
    for rho in (F(1, 4), F(1, 2), F(3, 4)):
        for p, other in product(parameters, repeat=2):
            discounted = []
            for horizon in range(5):
                distance = tv(traces(bernoulli_kernel, p, horizon), traces(bernoulli_kernel, other, horizon))
                assert distance == (F(0) if horizon == 0 else abs(p-other))
                discounted.append(rho**horizon*distance)
            assert max(discounted) == rho*abs(p-other)
            record('stochastic_discounted_pairs')

    tight_bounds = {}
    for epsilon in (F(0), F(1, 5), F(1, 2), F(1)):
        exact = {'s': {(0, 's'): 1-epsilon, (1, 's'): epsilon}}
        reduced_kernel = {'s': {(0, 's'): F(1)}}
        assert tv(exact['s'], reduced_kernel['s']) == epsilon
        assert push(exact['s'], lambda pair: pair[1]) == {'s': F(1)}
        assert push(reduced_kernel['s'], lambda pair: pair[1]) == {'s': F(1)}
        bounds = []
        for horizon in range(9):
            exact_trace, reduced_trace = (traces(kernel, 's', horizon) for kernel in (exact, reduced_kernel))
            distance = tv(exact_trace, reduced_trace)
            bound = 1-(1-epsilon)**horizon
            assert distance == bound and bound <= horizon*epsilon
            reward_gap = 3*sum(mass for trace, mass in exact_trace.items() if 1 in trace[2::2])
            assert reward_gap == 3*bound
            bounds.append(str(distance))
            record('stochastic_iid_horizons')
        tight_bounds[str(epsilon)] = bounds
    return {'joint_output_next_summary_tv': '1', 'joint_two_step_trace_tv': '1',
            'bernoulli_discounted_distance': 'rho*abs(p-pprime); first random output at depth 1',
            'iid_trace_tv_h0_to_h8': tight_bounds, 'iid_state_contraction': '0'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='write deterministic result JSON')
    args = parser.parse_args()
    regression()
    two_layer()
    matrix_closure()
    momentum()
    finite_automata()
    boxes = capacity_boxes()
    quantum()
    hidden_memory()
    lipschitz()
    witnesses = counterexamples()
    stochastic = stochastic_records()
    result = {
        'schema': 'contextual-spacetime-ml-finite-checks-v1',
        'source': 'docs/reports/contextual-spacetime-ml/finite_checks.py',
        'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'theory': 'docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md',
        'stochastic_records': stochastic,
        'configuration': {'seed': SEED, 'arithmetic': 'fractions.Fraction and rational-complex pairs',
                          'regression_steps': 5, 'two_layer_steps': 4, 'momentum_steps': 3,
                          'automata_scope': 'all binary-output partial deterministic machines with 1 or 2 states and 2 actions',
                          'automata_max_word_length': 4, 'quantum_max_word_length': 4,
                          'quantum_initial_grid': 'Bloch coordinates in {-1,-1/2,0,1/2,1} with squared norm at most 1'},
        'counts': COUNTS, 'capacity_boxes': boxes, 'counterexamples': witnesses,
        'result': 'all finite assertions passed',
        'boundary': 'Finite exact checks are not proofs of universal claims; no empirical 2027 or kernel-verification claim.'}
    payload = json.dumps(result, ensure_ascii=False, indent=2, sort_keys=True)+'\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload)
    print(payload, end='')


if __name__ == '__main__':
    main()
