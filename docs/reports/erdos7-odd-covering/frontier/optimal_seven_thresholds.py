#!/usr/bin/env python3
"""Exact fixed-branch dual for arbitrary real original-seven thresholds.

Profile58 proves the real-parameter optimization by affinity on integer
segments. This program checks its rational exposures, branch activity and
complete geometric tails at the actual off-diagonal source endpoint.
No global source scan, K improvement or actual-integral optimum is claimed.
"""
import argparse
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable source '+str(path))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def calculate(base):
    # Use the certificate's existing bindings for the mathematical helpers.
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() ==
            '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
            'Pinned certificate IO')
    io = load('optimal_seven_io', base/'certificate_io.py')
    raw = io.read_artifact_bytes(base/'certificates/source_norms/allocated_seven_thresholds.json')
    require(sha256(raw).hexdigest() ==
            '9400e4fae0a400edcc7ee7459103af677e512592823b683f67e7c896f8d345b8',
            'Pinned profile53 logical certificate')
    cert = json.loads(raw)
    pins = {'verify_joint_frontier.py':
            'a40fce0a5cb6a713dc8cb569b874d284b8dd66fb3f0a5e48fc2c69cb8fe286fe',
            'frontier/allocated_seven_thresholds.py':
            cert['helper_sha256']['frontier/allocated_seven_thresholds.py']}
    for name, pin in pins.items():
        require(sha256((base/name).read_bytes()).hexdigest() == pin, 'Pinned helper '+name)
    s = load('optimal_seven_source', base/'verify_joint_frontier.py')
    a = load('optimal_seven_allocation', base/'frontier/allocated_seven_thresholds.py')
    dat = s.data(list(s.vertices())[404])
    d, mass, eta, total, minimum = dat
    require((total, minimum) == (F(1, 4), F(3, 20)), 'Same actual source endpoint')

    class Asymmetric(a.AllocatedCost):
        def __init__(self, t, arrays, e):
            self.arrays = arrays
            super().__init__(s, t, tuple(arrays[j][0] for j in range(2, t)),
                             e, (1, 2, 0, 0, 0))

        @lru_cache(None)
        def g(self, cell, value):
            cost = s.zero5_cost(self.tag, value)
            if self.block == 0:
                cost -= F(self.weights[cell], 5)*min(F(1), a.hinge(self.t, value))
            for count, thresholds in self.arrays.items():
                if count > self.block:
                    cost += F(36, 5*7**count)*(a.hinge(thresholds[self.block], value)
                                                     - a.hinge(self.t/count, value))
            return cost

    def selected(op):
        t, e = int(op.t), op.block
        bi, cell = (9, 4) if e == 0 or (t == 5 and e == 1) else (1, 0)
        b = s.BASES[bi]
        value = sum(mass[l]*op.gs[l, b[l]]+eta[l]*op.bs[l, b[l]] for l in range(5))
        value += d[cell]*op.dg[cell, b[cell]]+op.db[cell, b[cell]]
        for count in range(2, op.cut):
            bp, cp = (7, 2) if e == 0 or (t == 5 and e == 1 and count == 2) else (6, 0)
            b = s.BASES[bp]
            initial, deep = op.qtables[count]
            pure = sum(eta[l]*initial[l, b[l]] for l in range(5))+deep[cp, b[cp]]
            value += F(4, 5**count)*(sum(eta[l]*op.g(l, count) for l in range(5))
                                          +(count-1)*pure)
        intercept = [op.g(l, op.cut)-op.slope*op.cut for l in range(5)]
        return value+op.tail1*op.slope*sum(eta)+op.tail0*sum(
            eta[l]*intercept[l] for l in range(5))+(op.tail1-op.tail0)*op.slope*F(1, 2)

    rows = []
    for t, expected in ((4, F(559961, 2572500)), (5, F(67605959, 405168750))):
        arrays = ({2: (F(2), F(2)), 3: (F(1), F(3, 2), F(3, 2))} if t == 4 else
                  {2: (F(2), F(3)), 3: (F(1), F(2), F(2)),
                   4: (F(1), F(1), F(5, 3), F(4, 3))})
        require(all(len(row) == n and min(row) >= 1 and sum(row) == t
                    for n, row in arrays.items()), 'Feasible real-threshold witness')
        values = []
        for e in range(t-1):
            op = Asymmetric(t, arrays, e)
            value = op.value(dat)
            require(value == selected(op), 'Selected branch active at the optimizer')
            values.append(value)
        tail = F(1, 10*7**(t-2))
        complete = sum(values)+tail
        # The all-one reference is used only to evaluate the separable lower
        # functional; it is not asserted to be a feasible threshold allocation.
        reference = {n: (F(1),)*n for n in range(2, t)}
        lower = sum(selected(Asymmetric(t, reference, e)) for e in range(t-1))+tail
        exposures = []
        for count in range(2, t):
            segments = []
            for e in range(count):
                rates = []
                for k in range(1, t-count+1):
                    low, high = dict(reference), dict(reference)
                    row = list(reference[count])
                    row[e] = F(k)
                    low[count] = tuple(row)
                    row[e] += 1
                    high[count] = tuple(row)
                    rate = -(selected(Asymmetric(t, high, e))-
                             selected(Asymmetric(t, low, e)))/F(36, 5*7**count)
                    rates.append(rate)
                    segments.append(rate)
                require(all(rates[j] >= rates[j+1] for j in range(len(rates)-1)),
                        'Each coordinate has decreasing segment exposures')
                exposures.append({'count': count, 'block': e, 'exposures': rates})
            lower -= F(36, 5*7**count)*sum(sorted(segments, reverse=True)[:t-count])
        require(lower == complete == expected, 'Global lower dual equals primal witness')
        rows.append({'threshold': t, 'optimizer': arrays, 'block_values': values,
                     'complete_seven_tail': tail, 'optimum': complete, 'dual_exposures': exposures})
    return {'schema': 'erdos7-optimal-seven-thresholds-v1', 'source_vertex': 404,
            'carrier': (0, 1), 'rows': rows, 'source_sha256': pins,
            'scope': 'Exact optima of the fixed source envelope over all real threshold arrays. '
                     'Not optima of actual integrals or a new global K bound; no Lean claim.'}


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = calculate(Path(__file__).resolve().parents[1])
    if args.output is not None:
        args.output.write_text(json.dumps(encode(result), indent=2)+'\n')
    print('PASS: exact global duals for thresholds4/5; all original-seven and five tails retained.')
    for row in result['rows']:
        print(str(row['threshold'])+': '+str(row['optimum']))


if __name__ == '__main__':
    main()
