#!/usr/bin/env python3
"""Check the finite aligned source row modulus (no LP and no re-propagation).

The published 306 zero-column restoration and the 315/316 model facts are
consumed by their source-bound certificates.  This helper checks only the new
row-budget arithmetic and domain guards.
"""
from argparse import ArgumentParser
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import importlib.util
import json
import sys

sys.dont_write_bytecode = True

CERTIFICATE = 'certificates/source_norms/j-source/j_aligned_source_row_transport.json'
INPUTS = (
    'certificates/source_norms/j-source/j_actual_rows_zero_restoration.json',
    'certificates/source_norms/j-source/j_aligned_retained375_heavy553_heads.json',
    'certificates/source_norms/j-source/j_aligned_retained375_h4_heads.json',
    'certificates/source_norms/j-source/j_aligned_quadratic_complete_heads.json',
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load_io(base):
    spec = importlib.util.spec_from_file_location('aligned_row_transport_io', base / 'certificate_io.py')
    require(spec is not None and spec.loader is not None, 'Readable canonical certificate IO')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(key): encode(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(item) for item in value]
    return value


def check_inputs(base, io):
    documents = {}
    hashes = {}
    for relative in INPUTS:
        path = base / relative
        raw = io.read_artifact_bytes(path)
        hashes[relative] = sha256(raw).hexdigest()
        documents[relative] = json.loads(raw, object_pairs_hook=io._unique)

    restoration = documents[INPUTS[0]]
    require(restoration['schema'] == 'erdos7-j-actual-rows-zero-restoration-v1',
            'Pinned 306 restoration certificate schema')
    require(restoration['zero_columns'] == 4634 and restoration['zero_rows'] == 2645,
            'Published 306 zero-column counts')
    require(F(restoration['maximum_column_bound']) == 17,
            'Published maximum restored-column coefficient')
    require(F(restoration['sum_column_bounds']) == F(56866, 5),
            'Published sum of restored-column coefficients')

    heavy = documents[INPUTS[1]]
    h4 = documents[INPUTS[2]]
    require(heavy['schema'] == h4['schema'] == 'erdos7-aligned-retained375-final-cover-v1',
            'Published 315 certificate schemas')
    require(heavy['model'] == h4['model'], 'Heavy and H4 share the exact 315 model')
    model315 = heavy['model']
    require(model315['variables'] == 12941 and model315['inequalities'] == 30454
            and model315['equalities'] == 23, 'Complete 315 model dimensions')
    require(model315['old_model'] == restoration['model'],
            '315 predecessor is the exact 306 restoration model')
    require(model315['changed_inequality_matrix_rows'] == [17, 22]
            and model315['changed_inequality_rhs_rows'] == [14, 17, 22]
            and model315['changed_original_equality_rhs_rows'] == [4]
            and model315['added_fixed_H_equalities'] == [20, 21, 22],
            'Published 315 row changes and fixed H equalities')
    for document in (heavy, h4):
        zero = document['zero_induction']
        require(zero['induction_rows'] == 2645 and zero['certified_zero_columns'] == 4634
                and zero['remaining_columns'] == 8307, 'Published 315 zero-induction facts')

    quadratic = documents[INPUTS[3]]
    require(quadratic['schema'] == 'erdos7-aligned-quadratic-complete-heads-v1',
            'Published 316 certificate schema')
    model316 = quadratic['model']
    require(model316['variables'] == 12941 and model316['inequalities'] == 30479
            and model316['equalities'] == 23, 'Complete 316 model dimensions')
    require(model316['actual375_predecessor'] == model315,
            '316 embeds the complete 315 model')
    zero316 = quadratic['zero_induction']
    require(zero316['induction_rows'] == 2645 and zero316['certified_zero_columns'] == 4634
            and zero316['remaining_columns'] == 8307,
            'Published 316 inherited zero-induction facts')
    require(len(zero316['new_explicit_E5_zero_columns']) == 11,
            'Published 316 explicit E5 zero-column list')
    return documents, hashes


def calculate(base):
    io = load_io(base)
    documents, hashes = check_inputs(base, io)

    delta_max, epsilon_max = F(1, 1000), F(1, 10000)
    a_min = F(1, 27) - 5 * delta_max / 72
    lambda_over_a = 1 / (72 * a_min)
    chi = F(3, 4) + lambda_over_a
    q_l1 = F(5, 4) + 2 * lambda_over_a

    # Domain guards used by the source135/source405 placement and the H gap.
    require(lambda_over_a == F(600, 1597), 'Corrected literal135 overlap ratio')
    require(epsilon_max < F(17, 6750), 'H-deficit good-carrier guard')
    require(5 * epsilon_max + delta_max / 72 < F(1, 405),
            '405 cannot occupy H')
    require(delta_max / 72 < F(1, 2025), '405 cannot occupy Q')
    require(F(1, 3) - delta_max / 18 - (F(1, 6) + delta_max / 18) >= F(1, 27),
            'Deep alpha wrong-root projection guard')
    require(1 + 2 * F(108, 17) < 14, 'Pure b=1 full-variation constant')
    require(1 + 2 * F(71988, 7997) < 20, 'Alpha b=1 full-variation constant')

    # Each pair (d,e) records residual <= d*delta + e*epsilon_*.
    row_budgets = {
        'raw25-total-positive-excess': (F(1, 24) + F(5, 9) * chi + F(5, 72), F(5)),
        'raw-three-groups': (F(1), F(0)),
        'raw-total-equality': (F(1, 2), F(0)),
        'survivor-total-equality': (F(53, 72), F(1)),
        'same-positive-density-error': (F(1), F(20)),
        'E3-root1-zero-rows': (F(1, 60), F(3)),
        'E3-root0-slot-equalities': (F(1, 45) + q_l1 / 90, F(4)),
        'E5-cell-equalities': (F(1, 450), F(5)),
        'marked27-81': (F(901, 900), F(25)),
        'marked25-75': (F(1) + F(7, 180) + (F(1, 4) + lambda_over_a) / 90, F(27)),
        'pretable27-81-135': (chi / 27, F(0)),
        'descendants25-75-125-225': (F(1, 450), F(0)),
        'descendant375': (F(1, 2250), F(0)),
        'own25-125': (F(2), F(1)),
        'own27-81': (F(5), F(20)),
        'three-root1-H-equalities-joint-deficit': (F(1, 90), F(5)),
        'twenty-E5-off-Q-rows-joint-mass': (F(0), F(13)),
        'exact-normalization-CRT-partition-unit-own75-135-225-375-Hsharp': (F(0), F(0)),
    }
    for name, (delta_price, epsilon_price) in row_budgets.items():
        require(delta_price <= 5 and epsilon_price <= 30,
                'Uniform complete row bound: ' + name)
    require(row_budgets['raw25-total-positive-excess'][0] <= 1,
            'Sharper aggregate raw-cap excess used by the prefix interface')
    require(F(1, 18) + delta_max / 72 + F(1, 36) + F(2, 9) <= 1,
            'Sum of all three raw-group positive excesses')

    # The source embedding and all measure inequalities are ordinary
    # mathematics in the companion note; this helper checks their rational
    # interface only.  The finite matrix bound is the common modulus below.
    modulus = {'delta': 5, 'epsilon_star': 30}
    return encode({
        'schema': 'erdos7-aligned-source-row-transport-v1',
        'source_sha256': hashes,
        'domain': {
            'delta_max': delta_max, 'epsilon_star_max': epsilon_max,
            'lambda_over_a': lambda_over_a, 'chi_upper': chi,
            'q_slot_l1_upper': q_l1,
        },
        'row_budgets': row_budgets,
        'uniform_row_modulus': modulus,
        'consumed_models': {
            str(number): {key: documents[INPUTS[index]]['model'][key]
                          for key in ('variables', 'inequalities', 'equalities', 'rows_sha256')}
            for number, index in ((306, 0), (315, 1), (316, 3))
        },
        'published_model_relations': ['315.old_model=306.model',
                                      '316.actual375_predecessor=315.model'],
        'consumed_zero_restoration': {
            'zero_columns': documents[INPUTS[0]]['zero_columns'],
            'zero_rows': documents[INPUTS[0]]['zero_rows'],
            'maximum_column_bound': documents[INPUTS[0]]['maximum_column_bound'],
            'sum_column_bounds': documents[INPUTS[0]]['sum_column_bounds'],
        },
        'scope': 'New source row arithmetic only; consumes published zero restoration and 315/316 model facts. No LP, source scan, measure embedding, tail transport, full prefix transport, numerical radius, or 403 claim.',
    })


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--certificate', type=Path,
                        default=None, help='Certificate path for --check or --write')
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    require(not (args.write and args.check), 'Choose --write or --check')
    base = args.base.resolve()
    io = load_io(base)
    result = calculate(base)
    path = args.certificate or (base / CERTIFICATE)
    if args.write:
        io.write_certificate_text(path, json.dumps(result, indent=2) + '\n')
    else:
        require(path.exists(), 'Use --write before --check for a new certificate')
        expected = json.loads(io.read_artifact_bytes(path), object_pairs_hook=io._unique)
        require(result == expected, 'Regenerated source-row certificate differs')
    print('PASS: aligned source row arithmetic; common modulus 5*delta+30*epsilon_*')
    print('Consumed published 306 restoration and 315/316 model facts; no LP.')


if __name__ == '__main__':
    main()
