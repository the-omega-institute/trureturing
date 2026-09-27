#!/usr/bin/env python3
"""Four exact envelopes cover every square-pair central role assignment.

A single stored thinning matrix per primary pattern bounds the same actual
conditional source for all64**20 choices. Endpoint grids are comparisons,
not separately realized source laws. Only standard-library code is used.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from math import prod
from pathlib import Path

SOURCE_JSON_SHA256 = '2e9eac2581f6c0e09b75fa91252c251cb62463e96038e6bdb5ed99a48ede8a3f'
SOURCE_PRODUCER_SHA256 = 'fe0bff7dceec1f2435c91218f371a12b523bec062e91466ad6e6fafd4a21cce6'
THETA_DENOMINATOR = 2**24
ROW_CLASSES = ((0,1,2), (3,), (4,))
COLUMN_CLASSES = ((0,1,2,3,4), (5,6,7,8,9), (11,13,14), (12,), (15,16,17,18,19))
BLOCKS = tuple(tuple((l,m) for l in row for m in column)
               for i,row in enumerate(ROW_CLASSES)
               for j,column in enumerate(COLUMN_CLASSES) if (i,j) != (0,0))
THETA_NUMERATORS = {
    'concentrated_00': (12023794, 12819449, 14758637, 16777216, 11738557, 11259196, 10304978, 14225129, 13011297, 7098617, 8166053, 6391996, 10304978, 8151554),
    'concentrated_12': (12140467, 13503507, 15829085, 16777216, 12014928, 12318888, 12078812, 0, 14564538, 6912042, 8875927, 7883157, 12078812, 8790154),
    'cyclic_roles': (12068920, 13256705, 15125192, 16777216, 11855330, 11877694, 10920199, 10471717, 13687938, 6820228, 8567634, 6620627, 10920199, 8363531),
    'separated_roles': (12287039, 13633553, 15981527, 16777216, 12014928, 12318888, 11866506, 0, 14564538, 6912042, 8875927, 7005219, 11866506, 8790154),
}

class Checks:
    def __init__(self):
        self.values = {}
        self.evaluations = 0

    def require(self, name, predicate):
        self.evaluations += 1
        if not predicate:
            raise ArithmeticError(name)
        self.values[name] = True


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k,v in value.items()}
    if isinstance(value, (tuple,list)):
        return [encode(v) for v in value]
    return value


def source_inputs(path, checks):
    raw = path.read_bytes()
    obj = json.loads(raw)
    producer_path = path.with_suffix('.py')
    producer_raw = producer_path.read_bytes()
    checks.require('pinned604_json', sha256(raw).hexdigest() == SOURCE_JSON_SHA256)
    checks.require('pinned604_producer', sha256(producer_raw).hexdigest()
                   == SOURCE_PRODUCER_SHA256 == obj['producer_sha256'])
    checks.require('all604_checks_true', bool(obj['checks'])
                   and all(v is True for v in obj['checks'].values()))
    specification = importlib.util.spec_from_file_location('fixed_pair_certificate', producer_path)
    library = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(library)
    source = obj['central_source']
    w = list(map(F,source['masses3']))
    v = list(map(F,source['masses5']))
    d3 = F(source['density3'])
    d5 = list(map(F,source['density5_by_root']))
    loss = list(map(F,obj['complete_coefficients']['loss']))
    weighted = list(map(F,obj['complete_coefficients']['weighted_nonunit_query']))
    constants = obj['constants']
    c = F(constants['continuation_c'])
    alpha = F(constants['Haar_factor'])
    checks.require('same_complete_source_and_coefficients',
                   sum(w) == sum(v) == 1 and len(loss) == len(weighted) == 512
                   and min(loss+weighted) >= 0 and weighted[0] == 0
                   and len(obj['retained_inventory']) == 156)
    checks.require('same_continuation_constants', c == F(1084133,201247200)
                   and alpha == F(2673,138320)
                   and F(constants['source_density_D']) == F(3458,405)
                   and F(constants['continuation_multiplier']) == F(200,33))
    record = dict(file=path.name, sha256=sha256(raw).hexdigest(),
                  producer_sha256=sha256(producer_raw).hexdigest(),
                  inherited_checks=len(obj['checks']),
                  six_pattern_certificate_replayed=False)
    return library,obj,w,v,d3,d5,loss,weighted,c,alpha,record


def weights(library):
    primary, secondary, full = [], [], []
    for i,j in library.EDGES:
        q,r = library.OUTSIDE[i],library.OUTSIDE[j]
        a = F(1,(q-1)*(r-1))
        b = F(1,q*(q-2)*(r-1))+F(1,(q-1)*r*(r-2))
        primary.append(a)
        secondary.append(b)
        full.append(a+b)
    return primary,secondary,full


def grid_from_caps(library, G, beta, cell):
    values = []
    for T in range(32):
        value = G[T][cell]-sum(beta[e]*G[T|library.EDGE_MASKS[e]][cell]
                              for e in range(10) if not T & library.EDGE_MASKS[e])
        value += sum(beta[e]*beta[f]*G[T|library.EDGE_MASKS[e]|library.EDGE_MASKS[f]][cell]
                     for e,f in library.MATCHINGS
                     if not T & (library.EDGE_MASKS[e]|library.EDGE_MASKS[f]))
        values.append(value)
    return values


def universal_box(library, full, checks):
    G = [[F() for _ in range(120)] for _ in range(32)]
    factors = {}
    minimum_z = F(1)
    maximum_disjoint = F()
    for l,m in product(range(6),range(20)):
        if l//3 == m//5 == 0:
            continue
        b = library.star_factors(l,m)
        checks.require('all_unmasked_star_factors_positive', min(b) > 0)
        factors[(l,m)] = b
        cell = 20*l+m
        for T in range(32):
            G[T][cell] = prod(b[q] for q in range(5) if not T >> q & 1)
        u = [4*full[e]/(b[i]*b[j]) for e,(i,j) in enumerate(library.EDGES)]
        z = 1-sum(u)+sum(u[e]*u[f] for e,f in library.MATCHINGS)
        disjoint = max(sum(u[f] for f in range(10)
                           if not library.EDGE_MASKS[e] & library.EDGE_MASKS[f])
                       for e in range(10))
        checks.require('universal4kappa_strict_region', z > 0 and disjoint < 1)
        minimum_z = min(minimum_z,z)
        maximum_disjoint = max(maximum_disjoint,disjoint)
    checks.require('universal105_cells', len(factors) == 105)
    checks.require('independent_strict_region_constants',
                   minimum_z == F(31820206188505,126963499999921)
                   and maximum_disjoint == F(6053127,13633361))
    # This finite activation check proves only the local1..4 bound. The
    # ordinary comparison argument covers every combination of the20 roles.
    for i,j in product(range(2),range(4)):
        values = [1+int(i == R)+int(j == C)+int((i,j) == (I,J))
                  for R,C,I,J in product(range(2),range(4),range(2),range(4))]
        checks.require('all64_local_profiles_between1_and4',
                       len(values) == 64 and min(values) == 1 and max(values) == 4)
    # All225 actual residue-role profiles reduce to a retained-root profile.
    # Inactive central residues have zero source mass and can be padded once.
    for R,C,I,J in product(range(3),range(5),range(3),range(5)):
        padded_R = R if R < 2 else 0
        padded_C = C if C < 4 else 0
        padded_point = (I,J) if I < 2 and J < 4 else (0,0)
        for i,j in product(range(2),range(4)):
            actual = 1+int(i == R)+int(j == C)+int((i,j) == (I,J))
            padded = 1+int(i == padded_R)+int(j == padded_C)
            padded += int((i,j) == padded_point)
            checks.require('null_role_padding_dominates_actual_activation',
                           actual <= padded <= 4)
    return G,factors,dict(unmasked_cells=105,minimum_full_polynomial=minimum_z,
                         maximum_disjoint_sum=maximum_disjoint,
                         derivative_bracket_lower=1-maximum_disjoint)


def envelopes(library,G,factors,primary,secondary,full,roles,checks,name):
    lower_query_grid = [[F() for _ in range(120)] for _ in range(32)]
    upper_query_grid = [[F() for _ in range(120)] for _ in range(32)]
    for (l,m),b in factors.items():
        i,j = l//3,m//5
        lower,upper = [],[]
        for e,role in enumerate(roles):
            activation = 1+int(i == role['row'])+int(j == role['column'])
            activation += int((i,j) == tuple(role['point']))
            lo = primary[e]*activation+secondary[e]
            hi = primary[e]*activation+4*secondary[e]
            checks.require(name+'_comparison_caps_in_universal_box',
                           full[e] <= lo <= hi <= 4*full[e])
            lower.append(lo)
            upper.append(hi)
        cell = 20*l+m
        H_at_lo = grid_from_caps(library,G,lower,cell)
        H_at_hi = grid_from_caps(library,G,upper,cell)
        for T in range(32):
            checks.require(name+'_all_support_monotone_grid_order',
                           0 <= H_at_hi[T] <= H_at_lo[T] <= G[T][cell])
            lower_query_grid[T][cell] = H_at_hi[T]
            upper_query_grid[T][cell] = H_at_lo[T]
        # The endpoint comparison is not a claim that either beta vector
        # comes from one globally realizable assignment of original phases.
    return lower_query_grid,upper_query_grid


def exact_lower_gate(library,H_mass,H_query,theta,w,v,d3,d5,loss,weighted,c):
    s3 = [library.selectors(6,3,w,[d3/2]*2,mode) for mode in range(4)]
    s5 = [library.selectors(20,5,v,[3*d/5 for d in d5],mode) for mode in range(4)]
    mass = sum(w[l]*v[m]*theta[20*l+m]*H_mass[0][20*l+m]
               for l,m in product(range(6),range(20)))
    debit,query = F(),F()
    for e3,e5,T in product(range(4),range(4),range(32)):
        index = (4*e3+e5)*32+T
        if not (loss[index] or weighted[index]):
            continue
        screen = max(sum(a*b*theta[20*l+m]*H_query[T][20*l+m]
                         for l,a in left for m,b in right)
                     for left in s3[e3] for right in s5[e5])
        debit += loss[index]*screen
        query += weighted[index]*screen
    return dict(chosen_pair_mass_lower=mass,remaining_original_loss_upper=debit,
                weighted_nonunit_query_upper=query,
                gate_lower=(1-c)*(mass-debit)-c*query)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source',type=Path,
                        default=Path(__file__).with_name('actual_pair_activation_certificate.json'))
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    checks = Checks()
    library,data,w,v,d3,d5,loss,weighted,c,alpha,source = source_inputs(args.source,checks)
    primary,secondary,full = weights(library)
    G,factors,region = universal_box(library,full,checks)
    checks.require('four_patterns_with14_weights', len(THETA_NUMERATORS) == 4
                   and len(BLOCKS) == 14)
    checks.require('uniform_gate_to_Haar', alpha*F(1,125) > F(1,6500))
    free_labels = [row for row in data['retained_inventory'] if row['kind'] == 'pair'
                   and 2 in row['exponents'][2:]]
    checks.require('eighty_free_numerical_pair_labels', len(free_labels) == 80
                   and len({row['modulus'] for row in free_labels}) == 80)
    results = {}
    for name,numerators in THETA_NUMERATORS.items():
        theta = [F() for _ in range(120)]
        checks.require(name+'_bounded_common_theta',len(numerators) == 14
                       and min(numerators) >= 0 and max(numerators) <= THETA_DENOMINATOR)
        for numerator,block in zip(numerators,BLOCKS):
            for l,m in block:
                theta[20*l+m] = F(numerator,THETA_DENOMINATOR)
        checks.require(name+'_zero_mass_cells_not_used',
                       all(not theta[20*l+m] for l,m in product(range(6),range(20))
                           if not G[0][20*l+m] or not w[l]*v[m]))
        roles = [r[0] for r in library.pattern_roles(name)]
        H_mass,H_query = envelopes(library,G,factors,primary,secondary,full,roles,checks,name)
        value = exact_lower_gate(library,H_mass,H_query,theta,w,v,d3,d5,loss,weighted,c)
        checks.require(name+'_complete_secondary_role_gate',value['gate_lower'] > F(1,125))
        value['head_Haar_lower'] = alpha*value['gate_lower']
        value['strict_head_lower'] = F(1,6500)
        results[name] = dict(primary_roles=roles,theta14_numerators=numerators,
                            theta_denominator=THETA_DENOMINATOR,
                            theta120=theta,consequence=value)
    result = dict(schema='arbitrary-square-pair-roles-v1',source=source,
                  scope=dict(head_primes=library.CORE+(23,29,31),
                             fixed='Report604 pure3/pure5 source and central15/star/new9q/new25q roles; one of four primary qr-role patterns',
                             free_role_blocks=20,profiles_per_padded_block=64,
                             complete_padded_role_assignments_per_primary_pattern=64**20,
                             actual_central_profiles_per_present_block=225,
                             padding='Source-null or missing central roles are replaced only in the cap by fixed retained-root roles; original classes remain unchanged',
                             secondary_roles='Every row mod3, column mod5 and point mod15 at q^2r and qr^2 is arbitrary and globally fixed',
                             unspecified_phases='All outside components and remaining admitted original phases arbitrary',
                             all_original_and_query_heights='Same unbounded finite scope as Report604 except fixed pure3/pure5 inventory',
                             exact_common_source='One actual beta and one actual pair-survivor source per original family; both envelope grids bound it',
                             excluded='Arbitrary primary roles; additional9q^2/25q^2; extra160 labels; exterior branches; unrestricted odd covering',
                             lean_verified=False),
                  constants=dict(continuation_c=c,Haar_factor=alpha),
                  universal_strict_region=region,
                  outside_edges=[(library.OUTSIDE[i],library.OUTSIDE[j]) for i,j in library.EDGES],
                  primary_weights=primary,secondary_weight_sums=secondary,kappa=full,
                  theta_blocks=BLOCKS,free_numerical_labels=free_labels,patterns=results,
                  checks=checks.values,predicate_evaluations=checks.evaluations,
                  producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    args.output.write_text(json.dumps(encode(result),indent=2)+'\n')
    print(json.dumps(encode(dict(output=str(args.output),patterns=4,
                                padded_role_assignments_per_pattern=64**20,
                                checks=len(checks.values),evaluations=checks.evaluations,
                                min_gate=min(x['consequence']['gate_lower'] for x in results.values()),
                                head_strict_lower=F(1,6500)))))


if __name__ == '__main__':
    main()
