#!/usr/bin/env python3
"""Independent exact audit of central-cell count-envelope obstruction (Report 687).

Reconstructs signed matching polynomials by enumerating disjoint edge sets,
not by importing a recurrence or a producer. The candidate is JSON data only.
"""
import argparse
from collections import Counter, defaultdict
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path


_DEFAULT_INPUT_PATHS = {'clustered_global_phase_fixture.json': '../clustered_global_phase_fixture.json', 'remaining33_global_root_exclusion_certificate.json': '../remaining33_global_root_exclusion_certificate.json'}

def _resolve_input_path(directory, name):
    if directory is not None:
        return directory / name
    return Path(__file__).resolve().parent / _DEFAULT_INPUT_PATHS.get(name, name)

HERE = Path(__file__).resolve().parent
EXPECTED_INPUTS = {
    'clustered_global_phase_fixture.json': '4bc215b032c910224a3a23ed76edaf1e32dc8e243fe5ba474e129a1cee63e6b6',
    'clustered_q7_q11_retention_obstruction.json': '89b89676db47826d4c647692527da0656a1f6784d6d38feaca7081f1ad61c028',
    'remaining33_global_root_exclusion_certificate.json': '36e1be912a058df44a9ce3b13c89d97574620176b921e037568ceb96dd0f87d4',
}
COUNTS = Counter()

def check(name, condition):
    COUNTS[name] += 1
    if not condition:
        raise ValueError('Audit failure: ' + name)

def product_fraction(values):
    out = F(1)
    for value in values:
        out *= value
    return out

def digest(path):
    return sha256(path.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--directory', type=Path, default=None)
    parser.add_argument('--candidate', type=Path)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    candidate_path = args.candidate or _resolve_input_path(args.directory, 'coherent_star_allfields_obstruction_verify.json')
    candidate = json.loads(candidate_path.read_text())
    inputs = {}
    for name, expected in EXPECTED_INPUTS.items():
        path = _resolve_input_path(args.directory, name)
        check('canonical_input_hash', digest(path) == expected)
        inputs[name] = json.loads(path.read_text())
    fixture = inputs['clustered_global_phase_fixture.json']['actual_originals']
    check('101_originals', len(fixture) == 101)
    originals = {row['modulus']: row['residue'] for row in fixture}
    check('101_distinct_originals', len(originals) == 101)
    for modulus, residue in originals.items():
        check('odd_reduced_original', modulus > 1 and modulus % 2 == 1 and 0 <= residue < modulus)
    for modulus, residue in [(3,2),(9,1),(5,4),(25,1),(15,0)]:
        check('central_geometry_from_actual_originals', originals[modulus] == residue)
    Q = (7,11,13,17,19)
    D = (3,5,15,9,25,45,75,225)
    for q, d in product(Q, D):
        check('actual_phase81', originals[q*d] % d == 81 % d)

    # Derive cells by excluding the five actual central congruence classes.
    # The two allowed mod-3 roots and four allowed mod-5 roots are root-major.
    cells = []
    for left in range(6):
        x3 = 3*(left % 3) + left//3
        for right in range(20):
            x5 = 5*(right % 5) + right//5
            x = (100*x3 + 126*x5) % 225
            check('crt_cell_reconstruction', x % 9 == x3 and x % 25 == x5)
            if all(x % m != originals[m] for m in (3,9,5,25,15)):
                cells.append((left,right,x3,x5,x))
    check('80_actual_live_cells', len(cells) == 80)
    check('live_cell_set', [(l,m) for l,m,*_ in cells] == [(l,m) for l in (0,1,2,4,5) for m in range(20) if m != 5 and not(l<3 and m<5)])

    r = {q:F(1,q-1) for q in Q}
    a = {q:F(1,q*(q-2)) for q in Q}
    B = {q:1-r[q]-(3 if q==7 else 2)*a[q] for q in Q}
    check('B7', B[7] == F(157,210))
    beta = {(p,q):a[p]*r[q]+r[p]*a[q]+2*r[p]*r[q] for p,q in combinations(Q,2)}
    matchings = {}
    # A graph on five vertices has at most two disjoint edges.
    for T in range(32):
        vertices = tuple(q for i,q in enumerate(Q) if not(T & (1<<i)))
        edges = list(combinations(vertices,2))
        sets = [()]
        sets.extend((edge,) for edge in edges)
        sets.extend((e,f) for e,f in combinations(edges,2) if len(set(e+f)) == 4)
        matchings[T] = (vertices,sets)
        for matching in sets:
            check('enumerated_disjoint_matching', len({q for edge in matching for q in edge}) == 2*len(matching))
    check('26_five_vertex_matchings', len(matchings[0][1]) == 26)

    H = {}
    cell_data = []
    signatures = Counter()
    for left,right,x3,x5,x in cells:
        counts = tuple(sum(x % d == originals[q*d] % d for d in D) for q in Q)
        signatures[counts] += 1
        Z = {q:max(F(0),B[q]-r[q]*n) for q,n in zip(Q,counts)}
        admissible = Z[7] > 0
        if counts not in H:
            table = []
            for T in range(32):
                vertices, sets = matchings[T]
                value = F(0)
                if admissible:
                    for matching in sets:
                        covered = {q for edge in matching for q in edge}
                        value += ((-1)**len(matching)
                            *product_fraction(beta[edge] for edge in matching)
                            *product_fraction(Z[q] for q in vertices if q not in covered))
                table.append(value)
            H[counts] = table
        table = H[counts]
        for T,value in enumerate(table):
            check('positive_admissible_or_zero_discarded_response', value > 0 if admissible else value == 0)
        check('admissibility_exact', admissible == (counts[0] in (0,1,2,3)))
        cell_data.append({'cell':(left,right),'physical':(x3,x5),'counts':counts,'admissible':admissible,'H':table})
    check('74_admissible_cells', sum(row['admissible'] for row in cell_data) == 74)
    check('six_count_signatures', signatures == Counter({(0,)*5:30,(1,)*5:26,(2,)*5:12,(3,)*5:6,(5,)*5:5,(8,)*5:1}))
    expected_distribution = [[list(k),v] for k,v in sorted(signatures.items())]
    check('candidate_count_distribution', expected_distribution == candidate['count_distribution'])

    # Full/root/leaf/deep menus, with generic deep normalizations.
    left_leaves = (0,1,2,4,5)
    right_leaves = tuple(i for i in range(20) if i != 5)
    left_menus = ((0,),(0,1),left_leaves,left_leaves)
    right_menus = ((0,),(0,1,2,3),right_leaves,right_leaves)
    def coordinate_weight(exp, label, value, prime):
        ordinary = F((2 if prime==3 else 4)-(value==(4 if prime==3 else 10)), 9 if prime==3 else 75)
        if exp == 0:
            return ordinary
        if exp == 1:
            return ordinary if value//prime == label else F(0)
        if exp == 2:
            return ordinary if value == label else F(0)
        return (F(1) if prime==3 else F(4,5)) if value == label else F(0)
    selectors = {}
    for e3,e5 in product(range(4),repeat=2):
        mode = 4*e3+e5
        selectors[mode] = {}
        for left,right in product(left_menus[e3],right_menus[e5]):
            coefficients = [coordinate_weight(e3,left,l,3)*coordinate_weight(e5,right,m,5) for l,m,*_ in cells]
            for coefficient in coefficients:
                check('nonnegative_selector_coefficient', coefficient >= 0)
            selectors[mode][left,right] = coefficients
    check('559_literal_selectors', sum(map(len,selectors.values())) == 559)

    # Collapse ONLY rational weights, not old source laws or old query responses.
    old = inputs['clustered_q7_q11_retention_obstruction.json']
    check('old_columns', old['dual_row_columns'] == ['central_mode','outside_support','query7','query11','left_selector','right_selector','numerator'])
    denominator = old['dual_denominator']
    check('positive_integer_dual_denominator', isinstance(denominator,int) and denominator > 0)
    check('2568_old_rows', len(old['dual_rows']) == 2568)
    collapsed = defaultdict(F)
    for mode,T,query7,query11,left,right,numerator in old['dual_rows']:
        check('nonnegative_integer_old_numerator', isinstance(numerator,int) and numerator >= 0)
        check('current_bundle_and_literal_selector', mode in selectors and 0 <= T < 32 and (left,right) in selectors[mode])
        collapsed[mode,T,left,right] += F(numerator,denominator)
    collapsed = {k:v for k,v in collapsed.items() if v}
    check('1733_collapsed_rows', len(collapsed) == 1733)
    dual_rows = [list(k)+[str(v)] for k,v in sorted(collapsed.items())]
    check('candidate_collapsed_rows', dual_rows == candidate['dual_rows'])

    g = F(200163067,201247200)
    base = inputs['remaining33_global_root_exclusion_certificate.json']
    check('g_from_canonical_input', F(base['constants']['g']) == g)
    fees = list(map(F,base['combined512_coefficients']))
    check('512_base_coefficients', len(fees) == 512)
    additions = []
    for i,q in enumerate(Q):
        if q == 7:
            continue
        support = 1<<i
        coefficient = g*a[q]
        fees[8*32+support] += coefficient
        additions.append({'mode':8,'support':support,'original_modulus':9*q*q,'coefficient':str(coefficient)})
    check('candidate_four_full_charges', additions == candidate['charge_additions'])
    for fee in fees:
        check('nonnegative_corrected_fee',fee >= 0)
    budget_used = [F(0) for _ in range(512)]
    debit = [F(0) for _ in cells]
    for (mode,T,left,right),weight in collapsed.items():
        budget_used[32*mode+T] += weight
        for index,central_coefficient in enumerate(selectors[mode][left,right]):
            if central_coefficient:
                debit[index] += weight*central_coefficient*cell_data[index]['H'][T]
    budgets = []
    for index,(available,used) in enumerate(zip(fees,budget_used)):
        check('512_budget_inequalities', used <= available)
        record = {'index':index,'available':str(available),'used':str(used)}
        check('candidate_budget_record', record == candidate['fee_budgets'][index])
        budgets.append(record)

    records = []
    ratios = []
    source_total = F(0)
    for index,row in enumerate(cell_data):
        left,right = row['cell']
        mu = F((2-(left==4))*(4-(right==10)),675)
        source = g*mu*row['H'][0]
        source_total += source
        check('80_cell_domination', debit[index] >= source)
        if row['admissible']:
            check('74_strict_cell_domination', debit[index] > source > 0)
            ratios.append((debit[index]/source,row['cell']))
        else:
            check('discarded_zero_source_and_debit', debit[index] == source == 0)
        record = {'cell':list(row['cell']),'physical_cell':list(row['physical']),
            'counts':list(row['counts']),'admissible':row['admissible'],
            'source':str(source),'dual_debit':str(debit[index]),'residual':str(source-debit[index])}
        check('candidate_cell_record', record == candidate['cell_inequalities'][index])
        records.append(record)
    minimum_ratio, minimum_cell = min(ratios)
    check('exact_minimum_ratio', minimum_ratio == F(candidate['minimum_debit_source_ratio']))
    check('minimum_ratio_cell', list(minimum_cell) == candidate['minimum_ratio_cell'])
    check('strict_quarter_gap', minimum_ratio > F(5,4))

    # Recompute the all-live-cells regression gate by maximizing each globally
    # fixed selector AFTER summing its coefficients over the cells.
    mode_fees = []
    for mode in range(16):
        mode_fee = F(0)
        for T in range(32):
            readings = [sum((coefficient*cell_data[index]['H'][T] for index,coefficient in enumerate(coefficients) if coefficient),F(0)) for coefficients in selectors[mode].values()]
            check('selector_reading_nonnegative', all(value >= 0 for value in readings))
            mode_fee += fees[32*mode+T]*max(readings)
        check('candidate_one_field_mode_fee', mode_fee == F(candidate['one_field_mode_fees'][mode]))
        mode_fees.append(mode_fee)
    gate = source_total-sum(mode_fees,F(0))
    check('candidate_one_field_gate', gate == F(candidate['one_field_gate']))
    check('zero_field_attains_zero', all(F(0)*f == 0 for f in fees))
    check('candidate_zero_upper_and_maximum', candidate['maximum_gate'] == candidate['universal_gate_upper'] == '0')
    check('candidate_field_counts', candidate['field_coordinates'] == 80 and candidate['effective_coordinates'] == 74)
    check('candidate_input_hashes', candidate['input_sha256'] == EXPECTED_INPUTS)
    result = {
        'schema':'coherent-star-allfields-obstruction-independent-v1',
        'status':'PASS','check_count':sum(COUNTS.values()),'checks':dict(sorted(COUNTS.items())),
        'audit_method':'Exact rational arithmetic; direct enumeration of disjoint edge sets; current literal selector coefficients rebuilt from definitions; no candidate producer read or imported.',
        'program_sha256':digest(Path(__file__)),
        'candidate_sha256':digest(candidate_path),
        'candidate_program_sha256_claim':candidate['verifier_sha256'],
        'input_sha256':EXPECTED_INPUTS,
        'scope':'All nonnegative central mod9/mod25 fields with the same field in every selector, phase81 count-matching response table, corner (4,10), generic deep caps and corrected full512 fees. Six zero-Z7 cells have identically zero responses. No conclusion for outside-dependent or higher-digit-dependent fields, sharper envelopes, arbitrary sources, or covering/nonexistence.',
        'new_lean_verification':False,'optimizer_used':False,
        'field_coordinates':80,'effective_coordinates':74,'literal_selector_count':559,
        'original_dual_rows':2568,'collapsed_dual_row_count':1733,
        'count_distribution':expected_distribution,
        'response_tables': [{'counts':list(k),'all32_responses':[str(v) for v in table]} for k,table in sorted(H.items())],
        'minimum_debit_source_ratio':str(minimum_ratio),'minimum_ratio_cell':list(minimum_cell),
        'source_deficit_factor':str(minimum_ratio-1),
        'universal_gate_upper':'0','maximum_gate':'0','attained_by':'zero field',
        'one_field_source':str(source_total),'one_field_gate':str(gate),
        'one_field_mode_fees':[str(v) for v in mode_fees],
        'charge_additions':additions,'dual_rows':dual_rows,
        'fee_budgets':budgets,'cell_inequalities':records,
    }
    args.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'checks':result['check_count'],'minimum_ratio':str(minimum_ratio),'one_field_gate':str(gate),'output':str(args.output)}))

if __name__ == '__main__':
    main()
