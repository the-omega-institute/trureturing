#!/usr/bin/env python3
"""Exact explicit actual-J neighborhood from committed same-source certificates.

Read and price existing dual banks with their official codec, transport the
fixed299 consumer coefficients, and verify a complete rational radius budget.
No optimizer, source-layout scan, or Lean verification is performed.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import gc
import importlib.util
import json
import sys
import time
sys.dont_write_bytecode = True

CERTIFICATE = 'certificates/source_norms/j-geometry/j_explicit_actual_neighborhood.json'
TARGET = 'certificates/source_norms/j-geometry/j_face_heavy_positive175189_complete_moment_cost_comparison.json'
RESTORATION = 'certificates/source_norms/j-geometry/j_actual_rows_zero_restoration.json'
HEAVY = 'certificates/source_norms/j-geometry/j_face_retained375_heavy_heads.json'
SCHEMA = 'erdos7-j-explicit-actual-neighborhood-v1'
PINS = {
    'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2',
    TARGET: '5d85a05b5741c599bde83fc28921de3af41ccdd26fb69de8521439ca03f5cad4',
    RESTORATION: '83ece9ee32550f166c2fd741c46fa010861ac790abc1245b56c01cd9aa5f2b06',
    'frontier/retained-transport/retained135_heavy_comparison.py': '16decabc92c504ef15a12ce7efff65786625d79dd3608049f182b1d355cdde36',
    'frontier/j-geometry/j_face_coupled_seven_heads.py': '375b207dad898b55ea0780277d47a94a4ebadd151dff798d86953d9f102c205a',
    'frontier/source-budgets/joint_selected_source_comparison.py': '27e01b28ef759fea1a3e8cb7ac336f71211fdd4fa9fd589c6270443ad9ec9355',
    'frontier/retained-transport/retained_deletion_heavy_comparison.py': 'bd8e4a4308df347e9303efca411014e90282b9bb8ecd8ad9b6dc87f8af1d4a66',
    'frontier/j-geometry/j_face_joint_selected_heads.py': '9b106a0b397b8974e3ac56932d84e7bc1f8d79c9ef3f18eebcde71a55f7a3c2e',
    'frontier/j-geometry/j_actual_rows_zero_restoration.py': '93314427295443d65fba5df010041b57f0c184e5f04f9c22efbcffa7f90379d0',
}
MODELS = {(876, 587, 16): '67a917e9001e85289eb2e26cfb974a851fce0810e9cc4970885e5b705be0e5ed', (3306, 6354, 18): '835e4518f33d0acb6ef02f8a045d1610785a9bb04ed13de156d1192d618d706e', (6531, 11211, 19): '9f571ed4977b916e2a0823e5e7262eb333717301ac85a30f6c96671ebc9465ce', (12941, 30454, 20): 'e591c59f8891f6647f0e21f303cd3be9ca661f1d5b48ebd0625c2de85cfa32d0', (32151, 56133, 22): '4da5961945a50079d14a49fc0017409abeba79624086971f2c0747d63e8e494d'}

def require(ok, message):
    if not ok:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'loadable existing provider')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result




def record_paths(value, path=()):
    """Inventory record locations only; never decode any bank here."""
    if isinstance(value, dict):
        if value.get('codec') == 'exact-rational-table-rle-duals-v1':
            yield ('encoded', path)
            return
        if 'nonzero_inequality_duals' in value and 'equality_duals' in value:
            yield ('record', path)
            return
        for key, child in value.items():
            yield from record_paths(child, path+(key,))
    elif isinstance(value, list):
        for index, child in enumerate(value):
            yield from record_paths(child, path+(index,))


def ceiling(value):
    return -(-value.numerator//value.denominator)


def price(bank, inequalities, equalities):
    cache = {'0': F(0)}
    def rational(value):
        if value not in cache:
            cache[value] = F(value)
            require(str(cache[value]) == value, 'canonical exact rational price')
        return cache[value]
    best = F(-1)
    witness = None
    entries = 0
    for key, record in bank.items():
        left, right = record['nonzero_inequality_duals'], record['equality_duals']
        require(len(right) == equalities and all(str(int(k)) == k and 0 <= int(k) < inequalities for k in left),
                'complete original row-price dimensions')
        counts = Counter(left.values())
        require(all(rational(value) >= 0 for value in counts), 'inequality prices remain nonnegative')
        norm = sum((count*rational(value) for value, count in counts.items()), F(0))
        norm += sum((count*abs(rational(value)) for value, count in Counter(right).items()), F(0))
        entries += len(left)+sum(value != '0' for value in right)
        if norm > best or norm == best and (witness is None or key < witness):
            best, witness = norm, key
    require(best >= 0, 'nonempty finite source bank')
    return {'dual_count': len(bank), 'nonzero_price_entries': entries,
            'maximum_L1': str(best), 'ceiling_maximum_L1': ceiling(best),
            'maximizing_key': witness, 'distinct_price_rationals': len(cache)}


def normalized_row(row):
    return tuple(sorted((int(k), str(F(v))) for k, v in row.items() if F(v)))


def map_small_model(small, base):
    j = module('j_inventory_source_tables', base/'frontier/j-geometry/j_face_coupled_seven_heads.py')
    raw = module('j_inventory_raw', base/'frontier/source-budgets/joint_selected_source_comparison.py')
    retained = module('j_inventory_retained', base/'frontier/retained-transport/retained_deletion_heavy_comparison.py')
    core = module('j_inventory_core', base/'frontier/j-geometry/j_face_joint_selected_heads.py')
    large = core.make_lp(j, raw, retained)
    old_rows = {(normalized_row(row), str(rhs)): index for index, (row, rhs) in enumerate(zip(large.rows, large.rhs))}
    old_eqs = {(normalized_row(row), str(rhs)): index for index, (row, rhs) in enumerate(zip(large.equalities, large.erhs))}
    def mapped(row):
        answer = {}
        for k, value in row.items():
            k, value = int(k), F(value)
            if k < 25:
                columns = [16*k+m for m in range(16)]
            elif k < 50:
                columns = [425+16*(k-25)+m for m in range(16)]
            elif k < 75:
                columns = [825+k-50]
            elif k < 100:
                columns = [850+k-75]
            else:
                require(k == 100, 'the same normalized late coordinate')
                columns = [875]
            for column in columns:
                answer[column] = answer.get(column, F(0))+value
        return answer
    inequality_map = []
    for row, rhs in zip(small['inequality_rows'], small['inequality_rhs']):
        signature = normalized_row(mapped(row)), str(F(rhs))
        require(signature in old_rows, 'every101-model inequality is an original244 row after aggregation')
        inequality_map.append(old_rows[signature])
    equality_map, extras = {}, []
    for index, (row, rhs) in enumerate(zip(small['equality_rows'], small['equality_rhs'])):
        signature = normalized_row(mapped(row)), str(F(rhs))
        if signature in old_eqs:
            equality_map[str(index)] = old_eqs[signature]
        else:
            extras.append(index)
    require(extras == [0, 1, 2, 14, 15, 16, 17, 18], 'only three raw group totals and five fixed-H totals are extra')
    require([small['equality_rhs'][i] for i in extras] ==
            ['1/24', '1/12', '1/8', '1/90', '1/45', '1/45', '1/45', '1/45'],
            'exact additional nominal masses')
    return {'inequality244_row_indices': inequality_map,
            'equality244_row_indices': equality_map,
            'additional_group_equality_indices': [0, 1, 2],
            'additional_H_equality_indices': [14, 15, 16, 17, 18],
            'group_absolute_residual': 'delta/2',
            'H_absolute_residual': 'ell+delta/45 <= 6t',
            'all_rows_uniform_residual': '100t'}


def exact_json(raw):
    def pairs(items):
        out = {}
        for key, value in items:
            require(key not in out, 'No duplicate JSON key: '+key)
            out[key] = value
        return out
    def nonexact(value):
        raise ValueError('Nonexact JSON number: '+value)
    return json.loads(raw, object_pairs_hook=pairs, parse_float=nonexact,
                      parse_constant=nonexact)


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(key): encode(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(item) for item in value]
    return value


def unbatch(parts):
    out = []
    for part in parts:
        require(part['start'] == len(out) and
                part['stop'] == len(out)+len(part['rows']),
                'Contiguous complete established certificate rows')
        out.extend(part['rows'])
    return out


def recognized_model(value):
    model = value['model']
    dimensions = tuple(model[key] for key in ('variables', 'inequalities', 'equalities'))
    require(dimensions in MODELS and model['rows_sha256'] == MODELS[dimensions],
            'Same original actual-row matrix')
    return model, dimensions


def price_inventory(base, source, restored, pins, read):
    codec = module('actual_neighborhood_codec', base/'frontier/retained-transport/retained135_heavy_comparison.py')
    paths = sorted(path for path in source['source_sha256']
                   if path.startswith('certificates/') and 'j_face_' in path)
    require(len(paths) == 53 and HEAVY in paths, 'All 53 pinned J source certificates')
    records, classified, models = [], [], {}
    small_mapping = None
    historical = []
    logical_bytes = 0
    covering = None
    seeds = None
    for path in paths:
        raw = read(path)
        value = exact_json(raw)
        logical_bytes += len(raw)
        locations = list(record_paths(value))
        count = 0
        if not locations:
            classified.append({'source': path, 'classification': 'no-source-duals',
                               'logical_bytes': len(raw), 'sha256': pins[path], 'bank_count': 0})
            del value, raw
            continue
        if path == HEAVY:
            require(set(locations) == {
                ('encoded', ('proof_data', 'encoded_covering_duals')),
                ('encoded', ('proof_data', 'encoded_prefix_seed_duals'))},
                'Exactly the two original 298 encoded banks')
            model, dimensions = recognized_model(value)
            require(model == restored['model'], 'Restoration uses the identical original 298 matrix')
            nodes = unbatch(value['proof_data']['covering_node_batches'])
            require(len(nodes) == restored['covering_node_count'] == 1177,
                    'All original covering nodes')
            for field, price_key, witness_key, expected in (
                    ('encoded_covering_duals', 'maximum_covering_price', 'maximum_covering_key', 981),
                    ('encoded_prefix_seed_duals', 'maximum_seed_price', 'maximum_seed_key', 50)):
                bank = codec.decode_dual_bank(value['proof_data'][field],
                    inequality_count=dimensions[1], equality_count=dimensions[2])
                require(len(bank) == expected, 'Whole original 298 bank count')
                if field == 'encoded_covering_duals':
                    require({node['dual_id'] for node in nodes} == set(bank),
                            'All original covering nodes have precisely these duals')
                result = price(bank, dimensions[1], dimensions[2])
                require(F(result['maximum_L1']) == F(restored[price_key]),
                        'Repriced 298 maximum equals pinned 306 value')
                key = restored[witness_key]
                require(key in bank and
                        price({key: bank[key]}, dimensions[1], dimensions[2])['maximum_L1'] == result['maximum_L1'],
                        'Pinned 306 maximizing record really attains the maximum')
                result.update(source=path, sha256=pins[path], bank_field='proof_data/'+field,
                              dimensions=list(dimensions), rows_sha256=model['rows_sha256'])
                records.append(result)
                count += 1
                if field == 'encoded_covering_duals':
                    covering = result
                else:
                    seeds = result
                del bank
            classification = 'covering-and-prefix-seed-banks'
        else:
            if 'encoded_rational_duals' in value:
                require(locations == [('encoded', ('encoded_rational_duals',))],
                        'No unaccounted nested source dual bank')
                model, dimensions = recognized_model(value)
                bank = codec.decode_dual_bank(value['encoded_rational_duals'],
                    inequality_count=dimensions[1], equality_count=dimensions[2])
                require(len(bank) == value['distinct_dual_count'], 'Every declared retained dual decoded')
                bank_field = 'encoded_rational_duals'
                classification = 'encoded-historical-bank'
            elif 'rational_duals' in value:
                require(all(kind == 'record' and len(where) == 2 and where[0] == 'rational_duals'
                            for kind, where in locations), 'No unaccounted nested uncompressed source dual')
                model, dimensions = recognized_model(value)
                bank = value['rational_duals']
                require(len(bank) == value['distinct_dual_count'] == len(locations),
                        'Entire uncompressed canonical bank')
                bank_field = 'rational_duals'
                classification = 'uncompressed-historical-bank'
            else:
                require(locations == [('record', ('exact_retained_head_dual',))],
                        'Only known 101-model inline dual')
                model = value['joint_source_model']
                dimensions = tuple(model[key] for key in
                                   ('nonnegative_variable_count', 'inequality_count', 'equality_count'))
                require(dimensions == (101, 66, 19), 'Complete original retained-square matrix')
                require(len(model['inequality_rows']) == len(model['inequality_rhs']) == 66 and
                        len(model['equality_rows']) == len(model['equality_rhs']) == 19,
                        'Complete row lists before aggregation mapping')
                mapping = map_small_model(model, base)
                if small_mapping is not None:
                    require(mapping == small_mapping, 'Both inline sources share the same 101-row mapping')
                small_mapping = mapping
                bank = {'exact_retained_head_dual': value['exact_retained_head_dual']}
                bank_field = 'exact_retained_head_dual'
                classification = 'mapped101-inline-dual'
            result = price(bank, dimensions[1], dimensions[2])
            result.update(source=path, sha256=pins[path], bank_field=bank_field,
                          dimensions=list(dimensions), rows_sha256=model.get('rows_sha256'))
            records.append(result)
            historical.append(result)
            count = 1
            signature = '/'.join(map(str, dimensions))
            if signature not in models or F(result['maximum_L1']) > F(models[signature]['maximum_L1']):
                models[signature] = {key: result[key] for key in
                                     ('source', 'maximum_L1', 'ceiling_maximum_L1', 'maximizing_key')}
            del bank
        classified.append({'source': path, 'classification': classification,
                           'logical_bytes': len(raw), 'sha256': pins[path], 'bank_count': count})
        del raw, value
        gc.collect()
    require(len(classified) == len(paths) and len({row['source'] for row in classified}) == len(paths),
            'Every pinned J certificate classified exactly once')
    require(len(historical) == 23 and sum(row['dual_count'] for row in historical) == 22850,
            'Complete historical inventory counts')
    require(len(records) == 25 and sum(row['dual_count'] for row in records) == 23881,
            'All historical, covering and prefix-seed duals priced')
    require(small_mapping is not None and len(models) == 6 and covering and seeds,
            'All five standard matrices, mapped 101 matrix, covering and seeds included')
    largest = max(historical, key=lambda row: F(row['maximum_L1']))
    complete_maximum = max(F(row['maximum_L1']) for row in records)
    return {'source_certificate_count': len(paths), 'total_logical_bytes': logical_bytes,
            'source_classification': classified, 'priced_bank_count': len(records),
            'priced_source_count': sum(row['bank_count'] > 0 for row in classified),
            'priced_dual_count': sum(row['dual_count'] for row in records),
            'historical_bank_count': len(historical), 'historical_dual_count': 22850,
            'historical_maximum_L1': largest['maximum_L1'],
            'historical_ceiling_maximum_L1': largest['ceiling_maximum_L1'],
            'historical_maximizing_source': largest['source'],
            'historical_maximizing_key': largest['maximizing_key'],
            'per_original_matrix_historical_maxima': models,
            'maximum_L1': complete_maximum, 'ceiling_maximum_L1': ceiling(complete_maximum),
            'source_banks': records, 'small101_row_mapping': small_mapping,
            'covering_node_count': 1177, 'covering_dual_count': covering['dual_count'],
            'prefix_seed_dual_count': seeds['dual_count'],
            'scope': 'Containing price inventory for all pinned original banks; original dual feasibility is consumed from their pinned certificates, not recomputed.'}


def restored_price(restored):
    pairs = unbatch(restored['column_bound_batches'])
    bounds = {int(column): F(bound) for column, bound in pairs}
    require(len(pairs) == len(bounds) == restored['zero_columns'] == 4634,
            'All and only the 4634 original restored columns')
    require(restored['zero_rows'] == 2645 and
            all(0 <= column < 12941 and bound > 0 for column, bound in bounds.items()),
            'Original zero induction domain')
    require(max(bounds.values()) == F(restored['maximum_column_bound']) == 17 and
            sum(bounds.values()) == F(restored['sum_column_bounds']) == F(56866, 5),
            'Exact aggregate bounds of pinned restoration result')
    categories = {}
    def put(column, kind, q, n):
        require(column not in categories and 0 <= column < 12941, 'Unique physical objective coordinate')
        categories[column] = '/'.join(map(str, (kind, q, n)))
    for cell in range(25):
        for mask in range(16):
            column = 16*cell+mask
            q = mask.bit_count()
            put(column, 'X', q, 0)
            put(425+column, 'Y', q, 0)
            for state in range(1, 8):
                n = state.bit_count()
                put(876+400*(state-1)+column, 'OU', q, n)
                put(3676+400*(state-1)+column, 'OV', q, n)
            for state in range(8):
                n = state.bit_count()
                put(6531+400*state+column, 'NU', q, n)
                put(9731+400*state+column, 'NV', q, n)
    require(len(categories) == 12800, 'All physical objective columns')
    for column in set(range(12941))-set(categories):
        categories[column] = 'profile/0/0'
    caps = {category: F(value) for category, value in restored['objective_specification_caps'].items()}
    require(set(caps) == set(categories.values()), 'No missing or surplus objective category')
    uniform_coefficient = F(restored['original_objective_coefficient_bound'])
    require(uniform_coefficient == 14*F(403, 8) and
            all(0 <= cap <= uniform_coefficient for cap in caps.values()),
            'All category caps lie in the original complete objective envelope')
    weighted = sum(bounds[column]*caps[categories[column]] for column in bounds)
    uniform = uniform_coefficient*sum(bounds.values())
    require(weighted == F(restored['restoration_price']) and
            uniform == F(restored['uniform_restoration_price']) and 0 < weighted <= uniform,
            'Exact category restoration recomputed from all removed columns')
    return {'restored_column_count': len(bounds), 'induction_row_count': restored['zero_rows'],
            'maximum_column_bound': max(bounds.values()), 'sum_column_bounds': sum(bounds.values()),
            'physical_column_count': 12800, 'original_column_count': 12941,
            'objective_category_count': len(caps), 'objective_coefficient_bound': uniform_coefficient,
            'uniform_restoration_price': uniform, 'restoration_price': weighted,
            'ceiling_restoration_price': ceiling(weighted),
            'scope': 'Consumes the pinned 306 zero-induction theorem and recomputes its full column-category weighted aggregate.'}


def consumer(source):
    names = [row['name'] for row in source['basis']]
    require(len(names) == len(set(names)) == 34, 'Original 34 basis functions')
    bounds = {row['name']: F(row['upper']) for row in source['basis']}
    targets = {row['name']: {key: F(value) for key, value in row['coefficients'].items()}
               for row in source['proof_data']}
    results = {row['name']: row for row in source['results']}
    require(len(targets) == len(source['proof_data']) == len(results) == len(source['results']) == 59 and
            set(targets) == set(results), 'All 59 original envelope coefficient vectors')
    for name, vector in targets.items():
        require(set(vector) <= set(names), 'Only original named source observations')
        require(all(value >= 0 for key, value in vector.items() if key != 'mass'),
                'Every original nonmass envelope coefficient is nonnegative')
        require(sum(value*bounds[key] for key, value in vector.items()) == F(results[name]['upper']),
                'Recomputed original envelope upper '+name)
    def linear(*terms):
        out = {key: F(0) for key in names}
        for scale, vector in terms:
            for key, value in vector.items():
                out[key] += scale*value
        return out
    mass = {'mass': F(1)}
    alpha = F(source['count_law']['remaining_hinge1_coefficient'])
    beta = F(source['count_law']['whole_constant_coefficient'])
    tail = linear((alpha, targets['mean']), (beta-alpha, mass))
    den = linear((F(1), mass), (-F(1, 6), targets['hinge4']), (-F(1, 7), tail),
                 *((-F(1, 7), targets['AP11-'+str(index)]) for index in range(4)))
    require(len(source['cost_weights']) == 52, 'Complete original 52 cost weights')
    num = linear((F(source['signed_mass_coefficient']), mass),
                 (F(source['complete_square_weight']), targets['square']),
                 *((F(weight), targets['cost-'+str(index)])
                   for index, weight in enumerate(source['cost_weights'])))
    offset = F(source['offset'])
    margin = linear((403-offset, den), (-F(1), num))
    evaluate = lambda vector: sum(vector[key]*bounds[key] for key in names)
    E, N, G = map(evaluate, (den, num, margin))
    require((E, N, G) == tuple(F(source['comparison_upper'][key]) for key in
            ('denominator', 'numerator', 'target403_numerator_margin')),
            'Exact original denominator, numerator and 403-margin identities')
    require(min(E, N, G) > 0, 'Original strict face signs')
    require(all(den[key] <= 0 and margin[key] <= 0 and num[key] >= 0
                for key in names if key != 'mass'), 'Safe directions after combining signed mass')
    used = [key for key in names if den[key] or margin[key]]
    require(len(used) == 18 and set(used) ==
            {key for vector in targets.values() for key, value in vector.items() if value},
            'Exactly the same 18 observations in all envelopes and complete consumer')
    losses = lambda vector: {key: (abs(vector[key]) if key == 'mass' else -vector[key]) for key in used}
    EL, GL = losses(den), losses(margin)
    return {'basis_count': len(names), 'envelope_count': len(targets),
            'source_observations': used, 'unused_basis_observations': [key for key in names if key not in used],
            'basis_bounds': bounds, 'original_envelope_coefficients': targets,
            'denominator_coefficients': den, 'numerator_coefficients': num, 'margin403_coefficients': margin,
            'denominator_error_prices': EL, 'margin403_error_prices': GL,
            'face_denominator': E, 'face_numerator': N, 'face403_margin': G,
            'offset': offset, 'mass_hypothesis': 'abs(S-3/20)<=t',
            'nonmass_hypothesis': 'Each original own-load observation is <= its original bound plus the common error; original independent test labels are retained.'}


def basis_expansions(source, used):
    quadratic = {
        'square': (F(1), {1: F(1)}, F(2), 1),
        'cost48': (F(0), {3: F(5)}, F(2), 3),
        'cost49': (F(0), {2: F(31, 16), 3: F(17, 16)}, F(2), 2),
        'factorial2': (F(0), {}, F(1), 2),
        'factorial3': (F(0), {}, F(1), 3),
        'factorial5': (F(0), {}, F(1), 5),
    }
    out = {}
    for row in source['basis']:
        name = row['name']
        if name not in used:
            continue
        low = list(map(F, row['low_load_values']))
        poly = tuple(map(F, row['tail_polynomial']))
        require(len(low) == 8 and len(poly) == 3, 'Complete original low-load and tail presentation')
        if name in quadratic:
            constant, hinges, factor, threshold = quadratic[name]
            classification = 'quadratic-hinge-factorial'
        else:
            require(poly[2] == 0, 'All remaining active observations have affine tails')
            values = {index+1: value for index, value in enumerate(low)}
            values[9] = poly[0]+9*poly[1]
            constant = values[1]
            hinges = {1: values[2]-values[1]}
            for index in range(2, 9):
                hinges[index] = values[index+1]-2*values[index]+values[index-1]
            hinges = {index: value for index, value in hinges.items() if value}
            factor, threshold = F(0), 1
            classification = 'affine-hinge'
        require(constant >= 0 and factor >= 0 and
                all(1 <= index <= 8 and value >= 0 for index, value in hinges.items()),
                'Nonnegative own-hinge coefficients with thresholds at most eight')
        slope = sum(hinges.values(), F(0))
        require(slope <= F(403, 8), 'Every active affine-hinge slope is within the common cap')
        def observation(load):
            return constant+sum(value*max(load-index, 0) for index, value in hinges.items()) + \
                   factor*max(load-threshold, 0)*max(load-threshold+1, 0)/2
        require([observation(load) for load in range(1, 9)] == low,
                'Exact original own-load values '+name)
        expected = (constant-sum(index*value for index, value in hinges.items())+
                    factor*threshold*(threshold-1)/2,
                    slope+factor*F(1-2*threshold, 2), factor/2)
        require(expected == poly, 'Exact polynomial identity for the entire tail '+name)
        out[name] = {'kind': classification, 'constant': constant, 'hinge_coefficients': hinges,
                     'hinge_slope': slope, 'factorial_weight': factor, 'factorial_threshold': threshold,
                     'low_load_values': low, 'tail_polynomial': poly}
    require(set(out) == set(used) and len(out) == 18 and
            sum(row['kind'] == 'affine-hinge' for row in out.values()) == 12,
            'All twelve affine and six quadratic active functions expanded')
    require(max(row['hinge_slope'] for row in out.values()) == F(403, 8),
            'Common slope cap is attained by the actual heavy cost observation')
    for name in quadratic:
        row = out[name]
        A, f, a = row['hinge_slope'], row['factorial_weight'], row['constant']
        require(256*A+615*f+a <= 2600 and A+6*f <= 17 and f/2 <= 1,
                'Complete quadratic-prefix and tail coefficients contained '+name)
    return out


def radius(inventory, restoration, sensitivity, expansions):
    D = F(inventory['ceiling_maximum_L1'])
    Z = F(restoration['ceiling_restoration_price'])
    A = max(row['hinge_slope'] for row in expansions.values())
    require((D, Z, A) == (F(128923), F(484473), F(403, 8)),
            'Recomputed common exact source price and slope caps')
    require(A >= 17 and 256*A >= 2600 and A >= F(5, 4),
            'Common modulus contains quadratic, affine, mean and mass terms')
    EL, GL = sensitivity['denominator_error_prices'], sensitivity['margin403_error_prices']
    E, N, G = (sensitivity[key] for key in ('face_denominator', 'face_numerator', 'face403_margin'))
    num = sensitivity['numerator_coefficients']
    budget = F(3, 10**6)
    require(budget*sum(EL.values()) < E/2 and budget*sum(GL.values()) < G/2,
            'Declared common observation budget preserves both strict half margins')
    records = []
    selected = None
    geometric3, geometric5 = F(3, 2), F(5, 4)
    weighted3, weighted5 = F(3), F(15, 8)
    require(geometric3*geometric5 == F(15, 8) and weighted3*weighted5 == F(45, 8),
            'Complete two-coordinate geometric sums')
    for exponent in range(3, 41):
        t = F(1, 10**exponent)
        L = 1
        while F(1, 3**L) > t:
            L += 1
        b1_interior = 100*t*(L*L-1)
        b1_strip3 = geometric3*geometric5*F(1, 3**L)
        b1_strip5 = geometric3*geometric5*F(1, 5**L)
        b1 = b1_interior+b1_strip3+b1_strip5
        tail3 = F(3*(L+1), 3**L)
        tail5 = F(5*(4*L+3), 8*5**L)
        require(tail3-F(3*(L+2), 3**(L+1)) == F(2*L+1, 3**L) and
                tail5-F(5*(4*L+7), 8*5**(L+1)) == F(2*L+1, 5**L),
                'Exact complete weighted geometric-strip recurrence')
        b2_interior = 100*t*L**4
        b2_strip3, b2_strip5 = weighted5*tail3, weighted3*tail5
        b2 = b2_interior+b2_strip3+b2_strip5
        error = 100*(D+Z)*t+A*(256*t+b1)+b2
        require(error >= t, 'Common observation error also contains the mass discrepancy')
        eloss = EL['mass']*t+sum(value*error for name, value in EL.items() if name != 'mass')
        gloss = GL['mass']*t+sum(value*error for name, value in GL.items() if name != 'mass')
        nloss = abs(num['mass'])*t+sum(value*error for name, value in num.items() if name != 'mass')
        passed = error <= budget and eloss < E/2 and gloss < G/2
        row = {'decimal_exponent': exponent, 'radius': t, 'geometric_box_side': L,
               'B1_interior': b1_interior, 'B1_full_strip3': b1_strip3, 'B1_full_strip5': b1_strip5,
               'B1_upper': b1, 'B2_interior': b2_interior, 'B2_full_strip3': b2_strip3,
               'B2_full_strip5': b2_strip5, 'B2_upper': b2,
               'common_observation_error': error, 'denominator_loss': eloss,
               'margin403_loss': gloss, 'numerator_loss': nloss, 'passed': passed}
        if passed:
            row.update(denominator_lower=E-eloss, margin403_lower=G-gloss,
                       numerator_upper=N+nloss,
                       comparison_upper=sensitivity['offset']+(N+nloss)/(E-eloss))
            require(row['comparison_upper'] < 403, 'Direct complete ratio is strictly below 403')
            selected = row
            records.append(row)
            break
        records.append(row)
    require(selected is not None and selected['decimal_exponent'] == 14,
            'First passing member of the declared decimal candidate sequence')
    require(selected['denominator_lower'] > F(858491237, 10**10) and
            selected['margin403_lower'] > F(58632524, 10**10) and
            selected['comparison_upper'] < F(402931703, 10**6) and
            selected['comparison_upper'] < F(402931702827, 10**9),
            'Exact outward decimal presentation bounds')
    return {'finite_price_bound': D, 'zero_restoration_bound': Z, 'maximum_hinge_slope': A,
            'common_error_formula': '100(D+Z)t+A(256t+B1(100t))+B2(100t)',
            'B1_definition': 'sum_(a,b>=0,a+b>0) min(e,3^(-a)5^(-b))',
            'B2_definition': 'sum_(a,b>=0)(2a+1)(2b+1) min(e,3^(-a)5^(-b))',
            'B1_full_geometric_sum_with_unit': F(15, 8), 'B2_full_geometric_sum': F(45, 8),
            'strip_domain': 'Interior 0<=a,b<L; both complete strips a>=L and b>=L are included. Their overlap is counted twice for an upper bound.',
            'declared_common_observation_budget': budget,
            'candidate_decimal_exponents': {'first': 3, 'last_allowed': 40, 'stop_at_first_pass': True},
            'tested_candidates': records, 'selected': selected,
            'same_source_domain': '136 actual-source hypotheses; delta>=0, q_J>=1-delta, rho=S-S0>=0, t=delta+rho<=1/10^14; one raw source and its survivor, common theta in [1/135,1/90], all original independent test labels and full infinite tails.',
            'radius_interpretation': 'The bound is for delta+rho, not a box with delta and rho each at the radius. Monotonicity of B1 and B2 extends the endpoint bound to every smaller t, including zero.',
            'scope': 'Explicit local same-source 299 comparison under the actual-row, analytic-prefix and quadratic-tail transport lemmas. No optimizer or source-layout scan, no Lean claim, and no unrestricted Erdos7 conclusion.'}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'],
            'Pin the official artifact reader before importing it')
    io = module('actual_neighborhood_io', base/'certificate_io.py')
    pins = dict(PINS)
    checked = set()
    def read(path):
        require(path in pins, 'Every runtime source has a logical-byte pin')
        relative = Path(path)
        require(not relative.is_absolute() and '..' not in relative.parts,
                'Source closure remains inside the official report base')
        raw = io.read_artifact_bytes(base/path)
        require(sha256(raw).hexdigest() == pins[path], 'Pinned mathematical source '+path)
        checked.add(path)
        return raw
    source = exact_json(read(TARGET))
    restored = exact_json(read(RESTORATION))
    for extra in (source['source_sha256'], restored['source_sha256']):
        for path, digest in extra.items():
            require(path not in pins or pins[path] == digest, 'Consistent mathematical source closure '+path)
            pins[path] = digest
    for path in sorted(pins):
        if path not in checked and not path.startswith('certificates/'):
            read(path)
    sensitivity = consumer(source)
    expansions = basis_expansions(source, sensitivity['source_observations'])
    restoration = restored_price(restored)
    inventory = price_inventory(base, source, restored, pins, read)
    integrated = radius(inventory, restoration, sensitivity, expansions)
    for path in sorted(set(pins)-checked):
        read(path)
    require(checked == set(pins), 'The full source closure is pinned and read')
    out = {'schema': SCHEMA, 'source_sha256': dict(sorted(pins.items())),
           'source_pin_count': len(pins), 'dual_price_inventory': inventory,
           'restoration': restoration, 'consumer': sensitivity,
           'active_own_load_expansions': expansions, 'explicit_neighborhood': integrated,
           'scope': 'Exact arithmetic certificate with original codec and original independent own-load labels. The source transport proofs are ordinary mathematical inputs; no Lean verification or unrestricted covering theorem is asserted.'}
    return encode(out), io


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--certificate', type=Path)
    parser.add_argument('--output', type=Path)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    require(not args.output or args.write, '--output requires --write')
    require(not args.write or args.certificate is None, '--certificate is only for checking')
    start = time.monotonic()
    result, io = calculate(args.base.resolve())
    if args.write:
        path = args.output if args.output else args.base/CERTIFICATE
        io.write_certificate_text(path, json.dumps(result, indent=2)+'\n')
        action = 'WRITE'
    else:
        path = args.certificate if args.certificate else args.base/CERTIFICATE
        expected = exact_json(io.read_artifact_bytes(path))
        require(json.dumps(expected, sort_keys=True, separators=(',', ':')) ==
                json.dumps(result, sort_keys=True, separators=(',', ':')),
                'Entire deterministic typed result equals the stored certificate; no extra fields')
        action = 'CHECK'
    chosen = result['explicit_neighborhood']['selected']
    print('PASS '+action+' '+str(path)+'; sources='+str(result['dual_price_inventory']['source_certificate_count'])+
          '; priced_duals='+str(result['dual_price_inventory']['priced_dual_count'])+
          '; radius='+chosen['radius']+'; wall_seconds='+str(round(time.monotonic()-start, 3)), flush=True)


if __name__ == '__main__':
    main()
