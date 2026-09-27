#!/usr/bin/env python3
"""Insert complete pure3 deletion into the disjoint pure5 square pair group.

Reuse the published all-layout rational slack; do not rerun its enumeration.
All pair ownership and uniform original-label geometry are in the proof.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/endpoint-bounds/endpoint_square_complete_pure3_deletion.json'
PINS = {
    "certificate_io.py": "2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b",
    "frontier/endpoint-bounds/endpoint_square_positive5.py": "e6d4a2ae2ac9f369048603d328da7e73cb719e9a622c2a6633ddd61e5609b00d",
    "certificates/source_norms/endpoint-bounds/endpoint_square_positive5.json": "feb9333e4714f3408029d9e24711fb2886d016c0c4265c0f039ab99419b99405",
    "frontier/endpoint-bounds/endpoint_linear_complete_pure3_deletion.py": "c0bba2c21ed9c1d6236bfee13ff2510f71b40b44bf63600f09be3b2807897bd5",
    "certificates/source_norms/endpoint-bounds/endpoint_linear_complete_pure3_deletion.json": "7e5b2c9d2244a9aad0b1f3e1850a52bb1a1a1e7ffbe49cbf7bd42b8017bc2cfc"
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable input')
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('square_complete_pure3_io', base/'certificate_io.py')
    read = lambda p: json.loads(io.read_artifact_bytes(base/p))
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    old = read('certificates/source_norms/endpoint-bounds/endpoint_square_positive5.json')
    geometry = read('certificates/source_norms/endpoint-bounds/endpoint_linear_complete_pure3_deletion.json')
    for record in (old, geometry):
        require(record['source_vertex'] == 404 and record['carrier'] == [0, 1], 'Same actual endpoint')
        for path, pin in record['source_sha256'].items():
            require(path not in used or used[path] == pin, 'Consistent inherited pin')
            require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Inherited input: '+path)
            used[path] = pin
    V = [[F(x) for x in row] for row in old['descendant5_cell_caps']]
    columns = [sum(row[j] for row in V) for j in range(5)]
    require(columns == list(map(F, ('0', '1/9', '5/18', '4/9', '5/18'))), 'Existing descendant-five columns')
    deletion = F(geometry['five_complement_deletion_coefficient'])
    revised = [F(0)]+[c-deletion for c in columns[1:]]
    require(deletion == F(1, 90) and max(revised) == F(13, 30), 'Same complete product-section deletion in every nonzero slot')
    r = F(1, 5)
    tail_mass = r*r/(1-r)
    tail_pair = r*r*(1+r)/(1-r)**2
    require((tail_mass, tail_pair) == (F(old['tail_mass']), F(old['tail_self_pair_weight'])) == (F(1, 20), F(3, 40)), 'Complete first and ordered-pair tails')
    BF_gain, FF_gain = 2*deletion*tail_mass, deletion*tail_pair
    gain = BF_gain+FF_gain
    old_constant = F(old['new_added_pair_constants'][0])
    new_constant = F(13, 30)*tail_pair+2*F(1, 18)*tail_mass-2*deletion*tail_mass
    require((BF_gain, FF_gain, gain) == (F(1, 900), F(1, 1200), F(7, 3600)), 'Disjoint BF and FF pair credits')
    require(new_constant == old_constant-gain == F(133, 3600), 'Complete pure5 pair group, retaining all TF intersections')
    oldQ, K, Rstar, s0 = (F(old[k]) for k in ('full_square_upper', 'common_layout_threshold', 'raw_expanded_head_upper', 'minimum_quadratic_slack'))
    require(old['layout_checks'] == 12500 and min(K, Rstar, s0) > 0, 'Published exhaustive positive rational slack')
    slack_gain = F(2, 5)*s0/(F(5, 2)*K+Rstar)
    simpleQ, Q = oldQ-gain, oldQ-gain-slack_gain
    require(simpleQ == F(16409, 3600) and Q < F(1139, 250), 'Uniform improved square below4.556')
    D = F(old['surviving_mass'])
    require(D == F(geometry['mass']) == F(3, 20), 'Same actual surviving mass')
    return {'schema': 'erdos7-endpoint-square-complete-pure3-deletion-v1', 'source_vertex': 404, 'carrier': [0, 1],
            'source_sha256': used, 'mass': D, 'old_square_upper': oldQ,
            'descendant5_old_column_caps': columns, 'descendant5_new_column_caps': revised,
            'complete_depth_tail': tail_mass, 'complete_ordered_pair_tail': tail_pair,
            'BF_pair_gain': BF_gain, 'FF_pair_gain': FF_gain, 'new_source_gain': gain,
            'old_pure5_pair_constant': old_constant, 'new_pure5_pair_constant': new_constant,
            'retained_layout_threshold': K, 'retained_raw_maximum': Rstar,
            'retained_quadratic_slack': s0, 'converted_existing_slack_gain': slack_gain,
            'square_without_slack_conversion': simpleQ, 'full_square_upper': Q,
            'barrier': 45, 'signed_square_margin': 45*D-Q,
            'scope': 'Uniform actual404 endpoint square using only disjoint BF/FF pair replacements and the published12500-layout minimum slack. TF,FG,G and all positive-seven groups unchanged. No globalK or Lean claim.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('square_complete_pure3_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact complete pure3 square certificate')
    if args.output is not None:
        io.write_certificate_text(args.output, json.dumps(result, indent=2)+'\n')
    print('PASS:disjoint BF/FF complete pair gains, source columns and retained rational layout slack.')
    print('Uniform endpoint square '+str(float(F(result['full_square_upper'])))+'; source gain7/3600 plus existing-slack conversion.')


if __name__ == '__main__':
    main()
