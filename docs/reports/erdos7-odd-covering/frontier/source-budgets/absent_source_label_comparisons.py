#!/usr/bin/env python3
"""Complete effective9 comparisons for specified absent original source labels."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import combinations
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/source-budgets/absent_source_label_comparisons.json'
PINS = {
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    'frontier/source-budgets/ineffective15_complete_source_comparison.py': 'd480e7165bad0808f43eeb2998785f92c25d7e3e315b06d9479f48e2af88b3bd',
}
SOURCE_LABELS = (27, 15, 45, 135, 25)
CASES = tuple((label,) for label in SOURCE_LABELS) + tuple(
    case for size in range(2, 5) for case in combinations(SOURCE_LABELS[:4], size))
MINIMAL_SUFFICIENT_CASES = ((15,), (27, 45), (27, 135), (45, 135))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable source provider '+str(path))
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


def digest(value):
    return sha256(json.dumps(encode(value), separators=(',', ':')).encode()).hexdigest()


def source_rules():
    pure3 = F(1, 27)/(1-F(1, 3))
    pure5 = F(1, 5)/(1-F(1, 5))
    late = pure3*pure5
    caps = {27: 9*(pure3-F(1, 27)), 15: pure5-F(1, 5), 45: pure5-F(1, 5),
            135: late-F(1, 135), 25: 1-(pure5-F(1, 25))}
    require(caps == {27: F(1, 6), 15: F(1, 20), 45: F(1, 20),
                     135: F(7, 1080), 25: F(79, 100)}, 'Complete absent-label geometric budgets')
    old = (F(1, 2), F(1, 4), F(1, 4), F(1, 72))
    rules = {label: (i, caps[label]/old[i]) for i, label in enumerate(SOURCE_LABELS[:4])}
    rules[25] = (4, (1-caps[25])/(1-F(3, 4)))
    return caps, rules


def original_core_errors(data, previous):
    core = data['load']('frontier/cover-geometry/ap_schedule_core.py')
    kc = data['load']('verify_killed_core_continuity.py')
    pure = data['read']('certificates/pure_root_profile_certificate.json')
    old53 = data['old53']
    inputs, rows = core.core_errors(kc, pure['source_inputs'], F(old53['Gamma13']),
                                   F(old53['rho']), F(old53['T13_81']), F(old53['bound']))
    require(previous.encode(inputs) == old53['source_inputs'] and len(rows) == 2,
            'Same original global source constants and both complete core interfaces')
    exponents = {3: (1, 0), 5: (0, 1), 9: (2, 0), 15: (1, 1),
                 25: (0, 2), 27: (3, 0), 45: (2, 1), 135: (3, 1)}
    result = []
    for i, (row, old) in enumerate(zip(rows, old53['core_errors'])):
        require(all(previous.encode(value) == old[key] for key, value in row.items()),
                'Every original complete core error term is unchanged')
        box = dict(row['box'])
        require(all(3**a*5**b == label and a <= box[3] and b <= box[5]
                    for label, (a, b) in exponents.items()),
                'Both retained forbidden-label boxes preserve3,5,9 and every restricted source label')
        require(row['total'] == row['mask']+row['incoming']+row['test'] > 0,
                'All source-law,forbidden-mask and independent-test tail errors are included')
        result.append({'core_index': i, 'box': row['box'], 'current': row['current'],
                       'original_source_inputs': inputs, 'mask_error': row['mask'],
                       'incoming_error': row['incoming'], 'whole_test_tail_error': row['test'],
                       'complete_error': row['total'], 'test_labels': row['test_labels'],
                       'forbidden_label_count_upper': row['forbidden_label_count_upper'],
                       'retained_source_labels': list(exponents)})
    return result


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'],
            'Pinned logical certificate reader')
    io = module('absent_source_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned direct source '+path)
    previous = module('absent_source_complete_provider',
                      base/'frontier/source-budgets/ineffective15_complete_source_comparison.py')
    data = previous.reconstruct(base)
    original = previous.original_endpoints(data)
    pins = dict(data['pins'])
    for path, pin in PINS.items():
        require(path not in pins or pins[path] == pin, 'Consistent complete source '+path)
        pins[path] = pin
    vertices, endpoints = original['vertices'], original['endpoints']
    q, reference, offset, slope = (original[k] for k in ('q', 'reference', 'offset', 'numerator_slope'))
    coefficient = original['mass_coefficient']
    require(len(vertices) == 1296 and len(endpoints) == 23328 and q == F(23, 42)
            and coefficient == q*(reference-offset)-slope > 0,
            'Complete original product source,common carriers and signed reference target')
    require(all(gap >= 0 and payment > 0 for pair in endpoints.values() for gap, payment in pair),
            'Both original mass endpoints retain every positive denominator and full reference margin')
    vertex_index = {v: i for i, v in enumerate(vertices)}
    caps, rules = source_rules()
    core_rows = original_core_errors(data, previous)
    results = []
    for case in CASES:
        current = [tuple(value for pair in endpoints[i, j] for value in pair)
                   for i in range(1296) for j in range(18)]
        for label in case:
            factor, weight = rules[label]
            numerator, denominator = weight.numerator, weight.denominator
            anchor = []
            for v in vertices:
                zero = list(v)
                zero[factor] = F(1) if factor == 4 else tuple(F(0) for _ in v[factor])
                anchor.append(vertex_index[tuple(zero)])
            contracted = []
            for k, row in enumerate(current):
                other = current[18*anchor[k//18]+k%18]
                contracted.append(tuple((numerator*x+(denominator-numerator)*y)/denominator
                                        for x, y in zip(row, other)))
            current = contracted
        thresholds = [max(reference-row[2*s]/row[2*s+1] for row in current) for s in (0, 1)]
        target = max(thresholds)
        signed = q*(target-offset)-slope
        selected = int(signed < 0)
        require(target > offset, 'Positive coefficient of the original true concave survival margin')
        controllers, margins, mixed = [], [], []
        for k, (glo, elo, ghi, ehi) in enumerate(current):
            i, j = divmod(k, 18)
            require(0 < elo <= ehi and q*(ghi-glo) == coefficient*(ehi-elo),
                    'Each contraction preserves its own original signed mass interval and payment')
            low, high = glo-(reference-target)*elo, ghi-(reference-target)*ehi
            require(low >= 0 and high >= 0 and (high <= low if selected else low <= high),
                    'Both mass endpoints hold and the selected side has the true coefficient sign')
            margin = (low, high)[selected]
            margins.append(margin)
            if margin == 0:
                controllers.append((i, j))
            mixed.append((i, j, ((glo, elo), (ghi, ehi))))
        require(len(mixed) == 23328 and min(margins) == 0 and thresholds[selected] == target,
                'All source/carrier pairs and complete sign-selected controllers')
        sufficient = [cs for cs in MINIMAL_SUFFICIENT_CASES if set(cs) <= set(case)]
        require(bool(sufficient) == (target < 403),
                'The four minimal sufficient restrictions cover exactly the successful listed cases')
        core_comparisons = []
        for row in core_rows:
            error = row['complete_error']
            margin = 403-target-error
            require((margin > 0) == (target < 403),
                    'Every successful case survives each whole original core error; failed cases remain recorded')
            core_comparisons.append({'core_index': row['core_index'], 'comparison_plus_error': target+error,
                                     'strict403_margin': margin, 'strictly_below403': margin > 0})
        results.append({'absent_forbidden_labels': case,
                        'factor_retention_weights': {str(label): rules[label][1] for label in case},
                        'lower_endpoint_threshold': thresholds[0], 'upper_endpoint_threshold': thresholds[1],
                        'complete_target': target, 'signed_mass_coefficient': signed,
                        'selected_mass_endpoint': 'upper' if selected else 'lower',
                        'strictly_below403': target < 403, 'gap_below403': 403-target,
                        'source_carrier_records': len(mixed), 'selected_endpoint_minimum_margin': min(margins),
                        'selected_endpoint_controllers': controllers, 'mixed_table_sha256': digest(mixed),
                        'containing_sufficient_absence_cases': sufficient, 'core_comparisons': core_comparisons})
    require(len(results) == 16 and sum(r['strictly_below403'] for r in results[:5]) == 1
            and results[1]['strictly_below403'] and all(r['strictly_below403'] for r in results[5:]),
            'Complete five singleton and eleven multiple-absence outcomes')
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Stable final input '+path)
    return encode({'schema': 'erdos7-absent-source-label-comparisons-v1', 'source_sha256': pins,
                   'original_source_profile_sha256': data['original_row_hash'],
                   'allocation_statistics': data['allocation_statistics'],
                   'all_original_endpoint_rows_sha256': digest(original['original_endpoints']),
                   'all_original_correction_rows_sha256': digest(original['component_rows']),
                   'original_reference_target': reference, 'original_offset': offset,
                   'survival_mass_coefficient': q, 'numerator_slope': slope,
                   'original_signed_mass_coefficient': coefficient,
                   'correction_formula': 'AC*Q_full+G_full+cG*m_g-R81',
                   'source_factor_names': ['deficit', 'alpha', 'beta', 'late', 'z'],
                   'absent_label_source_caps': caps,
                   'minimal_sufficient_absence_cases': MINIMAL_SUFFICIENT_CASES,
                   'additional_minimal_absence_pairs': MINIMAL_SUFFICIENT_CASES[1:],
                   'source_cases': len(results), 'source_carrier_record_checks': len(results)*23328,
                   'mass_endpoint_checks': len(results)*46656,
                   'original_complete_core_errors': core_rows, 'results': results,
                   'branch_preservation': 'The retained forbidden families contain exactly the same original3,5,9,15,25,27,45,135 labels when present. Effective9 and each listed absence restriction persist. No numerical source-budget restriction or ineffective-label generalization is assumed preserved.',
                   'scope': 'Ordinary complete source inequalities for the sixteen specified absent-label restrictions inside the effective9 source branch, with every independent original test and complete exponent tail retained. The two complete core-error comparisons apply to these preserved absent-label branches. The three additional minimal pairs are27+45,27+135,45+135; other successful rows lie inside the missing15 or a listed pair domain. No absence-free global403 result, actual attainment, later-prime continuation, Lean endpoint or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--certificate', type=Path, help='Read-only comparison certificate; default is the report certificate')
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--check', action='store_true')
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--output', type=Path)
    args = parser.parse_args()
    require(args.certificate is None or not (args.write or args.output is not None),
            'An explicit read-only certificate is not a generation destination')
    result = calculate(args.base)
    io = module('absent_source_writer_io', args.base/'certificate_io.py')
    if args.write or args.output is not None:
        io.write_certificate_text(args.output if args.output is not None else args.base/CERTIFICATE,
                                  json.dumps(result, indent=2)+'\n')
    else:
        certificate = args.certificate if args.certificate is not None else args.base/CERTIFICATE
        stored = json.loads(io.read_artifact_bytes(certificate), object_pairs_hook=io._unique)
        require(stored == result, 'Every complete absent-label source and core comparison recomputes exactly')
    print('PASS16 complete source restrictions,373248 source/carrier records and746496 signed mass endpoints')
    print('PASS three additional minimal absence pairs and both original complete core-error criteria')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
