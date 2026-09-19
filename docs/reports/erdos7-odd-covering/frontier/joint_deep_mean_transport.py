#!/usr/bin/env python3
"""Transport the whole mean credit with one original head and one residual."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
from types import SimpleNamespace
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/joint_deep_mean_transport.json'
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'frontier/pure_three_root_spill.py': '7fcf4015e427bf38261a636bc27607845e21566de07194fe5e63d3c9d92b405f',
    'frontier/quantitative_forced27.py': '63010b29185482dea406386e18e12635d4879641fe839e69377555042cdaada2',
    'frontier/deep_five_mean_transport.py': '8ade6cc7cf03ed27e7d6a0a6280fcf179fe5c474472951bbd4c52b9fc9b8fdaa',
    'frontier/finite_source_face_transport.py': 'aa4099317ddf1b7cca16df4916166b1399d0b6e44cbe6459dde081075db8d332',
    'frontier/whole_cost_mean_stop_loss.py': 'ce6fe161966af3c3ee10e837e4b63d40bd079db465c7b8cc9667aa67fe27ab1f',
}
ROOT = (0, 0, 1, 1, 1)
CELLS = (0, 3, 1, 4, 7)
SLOTS = (1, 2, 3, 0, 4)
FACE_ETA = (F(1, 18),)+(F(1, 9),)*4
FACE_Q = (F(0), F(1, 5), F(1, 5), F(3, 20), F(1, 5))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable input')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def layouts():
    return product(range(2), range(5), range(5), range(2), range(5), range(5), range(5))


def mean_data(sigma, dmax, root1_max, z, eta, qslots, layout):
    sigma, dmax, root1_max, z = map(F, (sigma, dmax, root1_max, z))
    eta, qslots = tuple(map(F, eta)), tuple(map(F, qslots))
    require(0 <= sigma <= F(2, 27) and 0 <= root1_max < dmax <= z <= F(3, 4)+sigma/4,
            'Actual concentrated source with a positive pure3 root gap')
    require(dmax >= F(3, 4)-sigma/2 and root1_max <= F(1, 2)+sigma/2,
            'Concentrated actual ternary availability bounds')
    require(len(eta) == len(qslots) == 5 and min(eta+qslots) >= 0
            and max(qslots) <= F(1, 5) and sum(qslots) == z,
            'Actual raw ternary and five-slot measures')
    require(len(layout) == 7 and layout[0] in (0, 1) and layout[3] in (0, 1)
            and all(layout[k] in range(5) for k in (1, 2, 4, 5, 6)), 'One original complete head')
    r3, c9, s5, r15, s15, c45, s45 = layout
    I, J, c, K = int(r3 == 0), int(r15 == 0), int(c9 == 1), int(c45 == 1)
    g = tuple(I+int(j == s5)+J*int(j == s15) for j in range(5))
    k = tuple(c+K*int(j == s45) for j in range(5))
    missing = tuple(I+J*int(j == s15)+k[j] for j in range(5))
    Mxi, Mspill, M27 = max(g), I+J, max(k)
    M, N = max(a+b for a, b in zip(g, k)), max(missing)
    ratio3 = root1_max/(dmax-root1_max)
    forced_factor = dmax/(27*(F(1, 135)-sigma/72))
    require(forced_factor >= 1, 'Every absent27 label pays the wrong-label lower gap')
    old_price3 = Mxi+Mspill*ratio3
    initial_price27 = M+max(M27*(forced_factor-1), N*ratio3)
    N0 = max(0, *(k[j]-int(c9 == 0)-int(c45 == 0 and j == s45) for j in range(5)))
    N1 = max(0, *(2*I-1+(2*J-1)*int(j == s15)+k[j] for j in range(5)))
    price3 = Mxi+I*(1+J)*ratio3
    price27 = M+max(N0*(forced_factor-1), N1*ratio3)
    old27 = old_price3+M27*forced_factor
    require(forced_factor >= 1+ratio3 and price3 <= old_price3 and price27 <= initial_price27,
            'Concentrated gaps and the retained actual head dominate the discarded-head prices')
    require(price27 <= old27, 'Joint original27 price is at most the separately bounded price')
    h0, h1 = sum(eta[:2]), sum(eta[2:])
    require(h1 > h0, 'Correct deep15 root has a positive capacity gap')
    ratio5 = h1/(h1-h0)
    M5 = 1+int(ROOT[c9] == r3)
    M15 = int(r3 == 1)+int(ROOT[c9] == 1)
    A3 = (I*z+qslots[s5]+J*qslots[s15])/90
    A27 = (c*z+K*qslots[s45])/135
    A5 = ((1+r3)*(h0, h1)[r3]+(1+ROOT[c9])*eta[c9])/100
    source_error = (F(Mxi, 270)+F(M, 135))*(z-dmax)
    old_source = (F(Mxi, 90)+F(M27, 135))*(z-dmax)
    require(source_error <= old_source, 'One27 projection also reduces the common source discrepancy')
    return {'layout': layout, 'reference': A3+A27+A5, 'pure3_reference': A3+A27,
            'deep5_reference': A5, 'source_error': source_error,
            'E27_price': price27, 'Ege4_price': price3, 'E5deep_price': F(M5),
            'E15deep_price': M15*ratio5, 'Mxi': Mxi, 'M27': M27, 'joint_supremum': M,
            'root1_missing_supremum': N, 'wrong_cell_missing_supremum': N0,
            'full_root1_missing_supremum': N1, 'root3_ratio': ratio3,
            'initial_joint_E27_price': initial_price27, 'separate_Ege4_price': old_price3,
            'forced27_factor': forced_factor, 'root5_ratio': ratio5,
            'separate_E27_price': old27, 'separate_source_error': old_source}


def mean_credit(data, E27, Ege4, E5deep, E15deep):
    defects = tuple(map(F, (E27, Ege4, E5deep, E15deep)))
    require(min(defects) >= 0, 'Four disjoint complete original-family defects')
    prices = tuple(data[k] for k in ('E27_price', 'Ege4_price', 'E5deep_price', 'E15deep_price'))
    penalty = sum(a*b for a, b in zip(prices, defects))
    affine = data['reference']-data['source_error']-penalty
    return {'capacity_penalty': penalty, 'affine_credit': affine, 'nonnegative_credit': max(affine, 0)}


def joint_residual_price(record, data):
    a1 = record['coefficients'].get(1, F(0))
    prices = (record['M'],)+tuple(a1*data[k] for k in ('E27_price', 'Ege4_price', 'E5deep_price', 'E15deep_price'))
    return max(prices)


def finite_case(forced, constructor, mode):
    source = forced.finite_source(constructor)
    A, B, height = source['A'], source['B'], source['height']
    masks, z, eta, d = source['state'], source['z'], tuple(source['eta']), source['d']
    slot_masks = [sum(1 << y for y in range(j, B, 5)) for j in SLOTS]
    qslots = tuple(F((source['pure5'] & sm).bit_count(), B) for sm in slot_masks)
    projections = {key: [F(0)]*25 for key in ('pure3', 'deep5')}
    mass27 = massge4 = mass5 = mass15 = F(0)
    # Complete the actual family behind source['pi']: pure7 source labels
    # and the shallow3/9 carriers(root1,cell1) at every e<=height.
    # They do not enter this additional mean credit or its four defects.
    actual_labels = [(a, 0, e) for a, e in product((0, 1, 2), range(1, height+1))]
    shallow = [(a, 1 if a == 1 else 3, e) for a, e in product((1, 2), range(1, height+1))]
    require(sum(F(6, 7**e) for e in range(1, height+1)) == source['pi']
            and len(shallow) == 2*height, 'Actual shallow3/9 virtual-carrier mixture gives the source concentration')
    for a, e in product(range(3, height+1), range(1, height+1)):
        residue = 3+9*(e % 3) if a == 3 else 3+3**(a-1)
        if mode == 'wrong27-and-wrong15' and (a, e) == (3, height):
            residue = 18
        if mode == 'root1-and-absent' and (a, e) == (3, height):
            residue = 1
        if mode == 'root1-and-absent' and (a, e) == (4, height):
            continue
        actual_labels.append((a, 0, e))
        u, mass = F(6, 5*7**e), F(0)
        for cell, slot in product(range(5), repeat=2):
            count = sum((masks[x] & slot_masks[slot]).bit_count()
                        for x in range(residue, A, 3**a) if x % 9 == CELLS[cell])
            value = u*F(count, A*B)
            projections['pure3'][5*cell+slot] += value
            mass += value
        if a == 3:
            mass27 += mass
        else:
            massge4 += mass
    for a, b, e in product((0, 1), range(2, height+1), range(1, height+1)):
        actual_labels.append((a, b, e))
        root = 0 if mode != 'good' and (a, b, e) == (1, height, height) else 1
        cylinder = sum(1 << y for y in range(4, B, 5**b))
        u, mass = F(6, 5*7**e), F(0)
        for cell in range(5):
            if a == 1 and ROOT[cell] != root:
                continue
            count = sum((masks[x] & cylinder).bit_count() for x in range(CELLS[cell], A, 9))
            value = u*F(count, A*B)
            projections['deep5'][5*cell+4] += value
            mass += value
        if a == 0:
            mass5 += mass
        else:
            mass15 += mass
    require(len(set(actual_labels)) == len(actual_labels), 'Pairwise distinct original exponent triples')
    dmax, R = max(d), max(d[2:])
    defects = (dmax/135-mass27, dmax/270-massge4, sum(eta)/100-mass5, sum(eta[2:])/100-mass15)
    require(min(defects) >= 0, 'All absent labels and infinite tails stay in the four complete capacities')
    total = [a+b for a, b in zip(projections['pure3'], projections['deep5'])]
    positive = checks = 0
    minimum_margin, minimum_positive, witness = None, None, None
    for layout in layouts():
        data = mean_data(source['sigma'], dmax, R, z, eta, qslots, layout)
        lower = mean_credit(data, *defects)['nonnegative_credit']
        r3, c9, s5, r15, s15, c45, s45 = layout
        observed = sum(value*(int(ROOT[c] == r3)+int(c == c9)+int(j == s5)
                              +int(ROOT[c] == r15 and j == s15)+int(c == c45 and j == s45))
                       for (c, j), value in zip(product(range(5), repeat=2), total))
        require(observed >= lower, 'Whole actual virtual mean credit exceeds its joint lower bound')
        checks += 1
        margin = observed-lower
        minimum_margin = margin if minimum_margin is None else min(minimum_margin, margin)
        if lower > 0:
            positive += 1
            if minimum_positive is None or lower < minimum_positive:
                minimum_positive, witness = lower, layout
    require(checks == 12500 and positive > 0, 'Complete original-head inventory includes strictly positive off-face credits')
    return {'mode': mode, 'source_height': height, 'sigma': source['sigma'], 'z': z,
            'dmax': dmax, 'root1_max': R, 'eta': eta, 'qslots': qslots,
            'present_seven_original_labels': len(actual_labels), 'uncredited_shallow_labels': shallow,
            'pure7_residue_rule': '6*7^(e-1)', 'mixed7_residue_rule': '0 for every label',
            'complete_defects': defects,
            'head_checks': checks, 'positive_credits': positive, 'minimum_margin': minimum_margin,
            'minimum_positive_credit': minimum_positive, 'positive_witness': witness}


def calculate(base):
    io = module('joint_mean_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    forced = module('joint_mean_forced27', base/'frontier/quantitative_forced27.py')
    constructor = module('joint_mean_source', base/'frontier/source_mass_compatibility.py')
    require(sha256((base/'frontier/source_mass_compatibility.py').read_bytes()).hexdigest()
            == forced.PINS['frontier/source_mass_compatibility.py'], 'Inherited actual source constructor')
    finite = module('joint_mean_finite', base/'frontier/finite_source_face_transport.py')
    old = module('joint_mean_face', base/'frontier/whole_cost_mean_stop_loss.py')
    proxy = SimpleNamespace(bridge=SimpleNamespace(ETA=FACE_ETA, ROOT=ROOT))
    face_count = 0
    for layout in layouts():
        data = mean_data(0, F(3, 4), F(1, 2), F(3, 4), FACE_ETA, FACE_Q, layout)
        expected = sum(old.MeanHead.correction_parts(proxy, layout))
        require(mean_credit(data, 0, 0, 0, 0)['affine_credit'] == expected, 'Exact109 whole correction for the same original head')
        face_count += 1
    price_checks = []
    for sigma in (F(0), F(1, 27), F(2, 27)):
        strict = further = deep = source_gain = 0
        saving, example = F(0), None
        record = finite.prepare({1: F(1), 3: F(1, 4)})
        for layout in layouts():
            data = mean_data(sigma, F(3, 4), F(1, 2), F(3, 4), FACE_ETA, FACE_Q, layout)
            gain = data['separate_E27_price']-data['E27_price']
            strict += int(gain > 0)
            further += int(data['E27_price'] < data['initial_joint_E27_price'])
            deep += int(data['Ege4_price'] < data['separate_Ege4_price'])
            source_gain += int(data['Mxi']+data['M27'] > data['joint_supremum'])
            if gain > saving:
                saving, example = gain, layout
            L = joint_residual_price(record, data)
            # A linear price reaches its simplex maximum at one defect coordinate.
            require(all(L >= v for v in (record['M'], data['E27_price'], data['Ege4_price'],
                                         data['E5deep_price'], data['E15deep_price'])), 'One residual pays every coordinate once')
        price_checks.append({'sigma': sigma, 'head_checks': 12500, 'strict_price_improvements': strict,
                             'maximum_price_saving': saving, 'maximizing_example': example,
                             'additional_full_head_improvements': further, 'deeper_family_improvements': deep,
                             'strict_source_coefficient_improvements': source_gain})
    cases = [finite_case(forced, constructor, mode) for mode in ('good', 'wrong27-and-wrong15', 'root1-and-absent')]
    return {'schema': 'erdos7-joint-deep-mean-transport-v1', 'source_sha256': PINS,
            'same_head_face_recoveries': face_count, 'joint_price_comparisons': price_checks,
            'actual_finite_families': cases,
            'scope': 'Complete off-face mean correction and a shared finite residual interface. Ordinary proof retains all original exponent tails. Full tail/cost optimization and unrestricted Erdos7 remain unresolved; no new global constant or Lean result.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    require(sha256((args.base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('joint_mean_writer', args.base/'certificate_io.py')
    result = encode(calculate(args.base))
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Canonical whole mean-transport certificate')
    print('PASS:12500 exact face recoveries,37500 joint-price checks and37500 actual off-face head inequalities.')
    print('Whole mean credit with one defect budget; no complete off-face numerator or new global K claimed.')


if __name__ == '__main__':
    main()
