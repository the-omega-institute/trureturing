#!/usr/bin/env python3
"""A complete clipped identity-load interface on the broad five-slot slab.

The ordinary proof supplies the measure inequality. Exact evaluation of
the established source operator retains both full prime-exponent tails.
No net improvement over the existing direction40 margin is inferred.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/endpoint-bounds/broad_clipped_identity.json'
PINS = {
    "certificate_io.py": "2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b",
    "verify_joint_frontier.py": "0b5cd35851d36f3af83aee19e02267cb05abc8bf07611a12083fca6f3d9bd765",
    "frontier/endpoint-bounds/broad_five_slot_tradeoff.py": "aa930dbc975c4a6a10f25e32f9da195dfc3d8a55089b2b59eea6eb7598a011d1",
    "certificates/source_norms/endpoint-bounds/broad_five_slot_tradeoff.json": "fef05428a73f6328ac2b1eef6a76440a7d52b31b13ba2adca9be23b2e627659f",
    "frontier/source-budgets/global_k_face_gain.py": "824d8e3d245484674c0bcb4c5446a2e4d6710be64cb705558f3d4c39613341c9",
    "certificates/source_norms/source-budgets/global_k_face_gain.json": "de7dff81b092a5f2b917094063ca3905442016040fa9de61d75f01108a0ff591"
}
CUT = 40


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable module')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


def calculate(base):
    require(PINS and sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('broad_identity_io', base/'certificate_io.py')
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    source = module('broad_identity_source', base/'verify_joint_frontier.py')
    read = lambda path: json.loads(io.read_artifact_bytes(base/path))
    geometry = read('certificates/source_norms/endpoint-bounds/broad_five_slot_tradeoff.json')
    for path, pin in geometry['source_sha256'].items():
        require(path not in used or used[path] == pin, 'Consistent inherited input')
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Inherited source: '+path)
        used[path] = pin
    root_tail = F(1, 3**3)/(1-F(1, 3))
    five_tail = F(1, 5)/(1-F(1, 5))
    ternary_sum = F(5, 9)+F(1, 3)+F(1, 9)+root_tail
    column_factor = F(1, 5)+five_tail
    column_load = ternary_sum*column_factor
    gap = F(397, 36000)
    transfer = column_load/gap
    require((ternary_sum, column_factor, column_load, transfer)
            == (F(19, 18), F(9, 20), F(19, 40), F(17100, 397)), 'Complete independent-label column cap')
    require(transfer >= CUT > 0, 'One common deficiency coefficient also pays bounded actual deletion error')
    vertex = list(source.vertices())[1]
    dat = source.data(vertex)
    require(vertex == ((F(0),)*5, (F(0),)*2, (F(0),)*5, (F(0),)*5, F(1)), 'Only fixed source3/9 exclusions retained')
    require(dat[:4] == ((F(1),)*5, (F(1, 9),)*5, (F(1, 9),)*5, F(5, 9)), 'Dominating effective9 raw source')
    tail = source.raw35(F(CUT), dat)
    require(tail == F(351520265979651248437376109626376737817577,
                       58972439045013398092123679816722869873046875000), 'Exact complete clipped tail')
    require(F(0) < tail < F(3, 500000), 'Strict rational size comparison, no tail truncation')
    global_data = read('certificates/source_norms/source-budgets/global_k_face_gain.json')
    weight = F(global_data['identity_cost_coefficient'])
    mass_coefficient = F(global_data['new_mass_coefficient'])
    absorption = mass_coefficient-weight*transfer
    require(absorption > 0, 'Current signed mass coefficient exceeds this interface penalty')
    return {'schema': 'erdos7-broad-clipped-identity-v1', 'source_sha256': used,
            'slab_deficit_upper': F(1, 18), 'best_slot_loss_upper_strict': F(1, 12000),
            'slot_gap_lower': gap, 'complete_ternary_column_factor': ternary_sum,
            'complete_five_intersection_factor': column_factor, 'column_load_upper': column_load,
            'cutoff': CUT, 'common_deficiency_coefficient': transfer,
            'dominating_source_vertex': 1, 'dominating_source_data': dat,
            'complete_clipped_tail': tail, 'tail_rational_upper': F(3, 500000),
            'identity_cost_coefficient': weight, 'current_signed_mass_coefficient': mass_coefficient,
            'residual_mass_coefficient_after_penalty': absorption, 'weighted_tail': weight*tail,
            'scope': 'Complete actual identity-load inequality on the small-best-slot-loss branch of the broad slab. Retains one common cap/union deficiency, the old3/9 virtual carriers and all exponent tails. Source optimization relative to old direction40 remains open; no new global K or Lean result.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('broad_identity_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact clipped identity certificate')
    if args.output is not None:
        io.write_certificate_text(args.output, json.dumps(result, indent=2)+'\n')
    print('PASS: complete original-label column cap, clipped full tail and one common deficiency coefficient.')
    print('Tail '+str(float(F(result['complete_clipped_tail'])))+'; coefficient '
          +str(float(F(result['common_deficiency_coefficient'])))+'. No global K replacement claimed.')


if __name__ == '__main__':
    main()
