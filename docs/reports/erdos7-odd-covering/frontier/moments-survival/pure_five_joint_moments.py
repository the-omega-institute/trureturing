#!/usr/bin/env python3
"""Sharp joint first/second moments of independent complete pure-five tests."""
import argparse
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/moments-survival/pure_five_joint_moments.json'
PINS = {
    'frontier/cover-geometry/full_family_five_cap_sharpness.py': '496c56e41467437a4da82282c05eca5f27dad0ced4c8c012507078e063339bde',
    'certificates/source_norms/cover-geometry/full_family_five_cap_sharpness.json': 'e02d99267f8e22953c4e52f3391a4e929f5814e30e371a2d991e02620b3e8fd5',
    'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2',
    'frontier/source-budgets/source_mass_compatibility.py': 'f65f0be22b250ab94d7da847a45b49c39355c15499f9cde8f18f267ca3365645',
    'profile-notes/065-128/75-forced27-and-complete-pure3-deletion-on-the-k-faces.md': 'bf21f845032d56fb86f86dfdecd5426e58eceac63a1c4e44d6fe0a16d7070f33',
}
SLOTS = ('P', 'A', 'B', 'Q', 'H')
FIRST = (F(0), F(2, 75), F(14, 225), F(7, 150), F(7, 150))
DENSITY = (F(0), F(2, 15), F(14, 45), F(2, 5), F(7, 30))
RATIO, CROSS = F(1, 5), F(11, 2)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable original source')
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def value(lam, counts, slot):
    c, n = DENSITY[slot], counts[slot]
    return c*((2*n+1+lam)/(1-RATIO)+2*RATIO/(1-RATIO)**2)


def envelope(lam):
    return max(F(7, 60)+F(7, 90)*lam, F(83, 900)+F(37, 450)*lam)


def exact_lines():
    rows = []
    for first, chosen in product(range(5), repeat=2):
        intercept = FIRST[first]+F(7 if chosen == first else 3, 40)*DENSITY[chosen]
        slope = FIRST[first]+DENSITY[chosen]/20
        require(intercept <= envelope(0) and intercept+slope*CROSS <= envelope(CROSS),
                'Every affine candidate lies below the first envelope through the switch')
        require(slope <= F(37, 450), 'Every candidate stays below the second envelope beyond the switch')
        rows.append({'first': SLOTS[first], 'deep': SLOTS[chosen], 'intercept': str(intercept), 'slope': str(slope)})
    require(F(7, 60)+F(7, 90)*CROSS == F(83, 900)+F(37, 450)*CROSS, 'Exact envelope switch')
    return rows


def finite_allocation_checks():
    """A separate finite optimal-control check, not the infinite proof."""
    outputs = []
    for lam in (F(0), F(2), CROSS, F(10)):
        @lru_cache(None)
        def optimum(remaining, counts):
            if remaining == 0:
                return F(0)
            return max(DENSITY[j]*(2*counts[j]+1+lam)+RATIO*optimum(
                remaining-1, tuple(n+int(k == j) for k, n in enumerate(counts))) for j in range(5))
        for first in range(5):
            counts = tuple(int(j == first) for j in range(5))
            potential = max(value(lam, counts, j) for j in range(5))
            for chosen in range(5):
                updated = tuple(n+int(j == chosen) for j, n in enumerate(counts))
                reward = DENSITY[chosen]*(2*counts[chosen]+1+lam)
                require(reward+RATIO*max(value(lam, updated, j) for j in range(5)) <= potential,
                        'Bellman inequality at the initial state of every independent first slot')
            finite = optimum(7, counts)
            require(finite <= potential, 'Exact arbitrary seven-step allocations obey the infinite potential')
            complete = (1+lam)*FIRST[first]+potential/25
            require(complete <= envelope(lam), 'Every first slot obeys the common sharp envelope')
            outputs.append({'lambda': str(lam), 'first': SLOTS[first], 'finite_discounted_max': str(finite),
                            'infinite_discounted_max': str(potential), 'complete_upper': str(complete)})
    return outputs


def actual_crt(base):
    source = module('pure_five_source', base/'frontier/source-budgets/source_mass_compatibility.py')
    repack = module('pure_five_repack', base/'frontier/cover-geometry/full_family_five_cap_sharpness.py')
    N, labels = 3, []
    for a, b in product(range(N+1), repeat=2):
        if a+b == 0:
            continue
        aa, ra, bb, rb = source.source_label(a, b, 398)
        labels.append(source.crt_label(aa, ra, bb, rb, 0, 0))
        j, aa, ra, bb, rb = repack.mixed_label(a, b)
        for e in range(1, N+1):
            labels.append(source.crt_label(aa, ra, bb, rb, e, j*7**(e-1)))
    labels += [source.crt_label(0, 0, 0, 0, e, 6*7**(e-1)) for e in range(1, N+1)]
    require(len(labels) == len({m for m, _ in labels}) == (N+1)**3-1, 'The full unchanged actual original-label family')
    period = 105**N
    alive = bytearray(b'\1')*period
    for modulus, residue in labels:
        alive[residue::modulus] = b'\0'*len(alive[residue::modulus])
    t, u = sum((F(1, 3**a) for a in range(3, N+1)), F(0)), (5+F(1, 7**N))/6
    kap, h = (1-F(1, 7**N))/(5+F(1, 7**N)), F(5, 9)-t
    b_density, q_density = h-F(1, 9)-kap*(F(1, 3)+t), h-kap*(F(4, 9)+t)
    rows = []
    for geometry in ('all_nested_B', 'first_B_nested_Q'):
        histogram = [0]*(N+1)
        for x, bit in enumerate(alive):
            if bit:
                count = sum(x % (5**b) == (3 if geometry == 'all_nested_B' or b == 1 else 20)
                            for b in range(1, N+1))
                histogram[count] += 1
        first = F(sum(k*n for k, n in enumerate(histogram)), period)/u
        second = F(sum(k*k*n for k, n in enumerate(histogram)), period)/u
        expected_first = (b_density*sum((F(1, 5**b) for b in range(1, N+1)), F(0)) if geometry == 'all_nested_B'
                          else b_density/5+q_density*sum((F(1, 5**b) for b in range(2, N+1)), F(0)))
        expected_second = (b_density*sum((F(2*b-1, 5**b) for b in range(1, N+1)), F(0)) if geometry == 'all_nested_B'
                           else b_density/5+q_density*sum((F(2*b-3, 5**b) for b in range(2, N+1)), F(0)))
        require((first, second) == (expected_first, expected_second), 'Literal actual Y and Y squared agree with the nested-cylinder formula')
        rows.append({'geometry': geometry, 'height': N, 'period': period, 'histogram': histogram,
                     'first_moment': str(first), 'second_moment': str(second)})
    require(F(14, 45)/4 == F(7, 90) and F(14, 45)*F(3, 8) == F(7, 60), 'Nested B limit realizes the first sharp line')
    require(F(14, 225)+F(2, 5)/20 == F(37, 450)
            and F(14, 225)+F(2, 5)*F(3, 40) == F(83, 900), 'Separated first B and nested Q realize the second sharp line')
    return rows


def calculate(base):
    io = module('pure_five_joint_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned source '+path)
    repack = module('pure_five_joint_repack', base/'frontier/cover-geometry/full_family_five_cap_sharpness.py')
    pins = dict(PINS)
    for path, pin in repack.PINS.items():
        require(path not in pins or pins[path] == pin, 'Consistent original-family source')
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Complete original-family input')
        pins[path] = pin
    for path in ('frontier/cover-geometry/full_family_five_cap_sharpness.py', 'certificates/source_norms/cover-geometry/full_family_five_cap_sharpness.json'):
        pins[path] = sha256(io.read_artifact_bytes(base/path)).hexdigest()
    raw, common = F(1, 2), (F(1, 3)+F(1, 9))/5+F(1, 90)
    require(raw-common == F(2, 5), 'Complete3/9 and deep-three deletion, including27 once')
    require(DENSITY == (F(0), raw-common-F(4, 15), raw-common-F(4, 45), raw-common,
                        raw-common-(F(1, 2)+F(1, 3))/5), 'Five slot-specific source/deletion density bounds')
    old_component, new_component = 3*FIRST[2]+F(2, 5)*F(11, 40), envelope(F(2))
    saving = old_component-new_component
    require((envelope(0), new_component, saving, F(374, 75)-saving) ==
            (F(7, 60), F(49, 180), F(11, 450), F(2233, 450)), 'Exact joint square and original complete-square substitution')
    return {'schema': 'erdos7-pure-five-joint-moments-v1', 'source_sha256': pins,
            'slot_order': list(SLOTS), 'first_caps': list(map(str, FIRST)), 'deep_density_caps': list(map(str, DENSITY)),
            'candidate_lines': exact_lines(), 'envelope_switch': str(CROSS),
            'sharp_lines': [{'intercept': '7/60', 'slope': '7/90'}, {'intercept': '83/900', 'slope': '37/450'}],
            'finite_allocation_checks': finite_allocation_checks(), 'actual_CRT_witnesses': actual_crt(base),
            'old_pure_five_square_with_unit_cross': str(old_component), 'new_pure_five_square_with_unit_cross': str(new_component),
            'complete_square_saving': str(saving), 'full_face_square_upper': str(F(374, 75)-saving),
            'scope': 'Ordinary all-depth theorem on both saturated actual K faces and their complete beta distributions. Sharp positive affine first/second-moment envelope of pure-five tests, with actual full-original-family limiting witnesses. The complete face-square substitution retains every other LCM category. No off-face or full52/global comparison, Lean theorem or unrestricted Erdos7 conclusion.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('pure_five_joint_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact pure-five joint-moment certificate')
    print('PASS: sharp two-line pure-five moment envelope; full face square <=2233/450.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
