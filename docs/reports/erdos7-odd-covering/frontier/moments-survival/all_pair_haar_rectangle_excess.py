"""Exact controls for the single-tag all-pair Haar construction.

The only cases are P=(7,) and P=(11,13).  Every original is an actual
numeric congruence class, with its CRT residue and odd distinct modulus.
The full period is 3*prod(P)*5**K; it is NEVER enumerated.

All original tag conditions are 0 modulo 5**h.  Thus membership is
constant on each tag valuation stratum j<K (divisible by 5**j but not
5**(j+1)), and on j=K (the zero residue).  Their exact relative Haar
weights are 4/5**(j+1) and 1/5**K.  A representative 5**j (or 0 at K),
together with every complete core residue, therefore computes exact
Haar integrals.  Numeric membership is independently compared with
coordinate conditions.  Covered/private canonical fibres and their
rectangles are computed from those memberships, before comparing with
the predicted rectangle or any mass formula.

Standard-library imports only; no input files, repository imports,
network, subprocesses, or filesystem discovery.  The sole file access
is writing an explicitly supplied --output path.  All checks raise
explicit exceptions and remain effective under python -O.
"""
from argparse import ArgumentParser
from fractions import Fraction
from itertools import product
import json


def crt(pairs):
    value, modulus = 0, 1
    for local_modulus, residue in pairs:
        value += modulus * (((residue-value) * pow(modulus, -1, local_modulus)) % local_modulus)
        modulus *= local_modulus
    return value % modulus, modulus


def rational(value):
    return {'numerator': str(value.numerator), 'denominator': str(value.denominator)}


def run_case(primes):
    checks = 0
    numeric_membership_tests = 0
    private_witness_membership_tests = 0
    fibre_member_reads = 0

    def check(condition, message):
        nonlocal checks
        checks += 1
        if not condition:
            raise RuntimeError(message)

    n = len(primes)
    D, A = 1, 1
    for p in primes:
        check(p > max(5,4*n), 'prime size contract')
        check(p >= 2 and all(p % d for d in range(2,p) if d*d <= p), 'nonprime P coordinate')
        D *= p
        A *= p-1
    check(len(set(primes)) == n, 'duplicate prime')
    K, core_modulus = A+2, 3*D
    tag_modulus = 5**K
    period = core_modulus*tag_modulus
    originals = []

    def add_original(kind, conditions, tag_height, metadata):
        pairs = [(primes[i], a) for i,a in conditions if i < n]
        pairs += [(3,a) for i,a in conditions if i == n]
        pairs.append((5**tag_height,0))
        residue, modulus = crt(pairs)
        check(all(residue % m == a % m for m,a in pairs), 'original CRT mismatch')
        originals.append({'kind':kind, 'conditions':tuple(conditions),
                          'tag_height':tag_height,'residue':residue,
                          'modulus':modulus, 'metadata':metadata})

    allowed = [tuple(a for a in range(p) if a != 1) for p in primes]
    assignments = tuple(product(*allowed))
    check(len(assignments) == A, 'P assignment inventory')
    for j,v in enumerate(assignments,1):
        add_original('P',tuple(enumerate(v)),j,{'assignment':list(v),'j':j})
    add_original('Q0',((n,0),),K-1,{})
    add_original('Q2',((n,2),),K,{})
    target_indices = []
    for i in range(n):
        target_indices.append(len(originals))
        add_original('C',((i,1),(n,1)),K,{'target_axis':i})
    check(len(originals) == A+2+n, 'original inventory size')
    check(len({o['modulus'] for o in originals}) == len(originals), 'repeated numerical modulus')
    for o in originals:
        check(o['modulus'] > 1 and o['modulus'] % 2 == 1, 'original not odd nonunit')
        check(period % o['modulus'] == 0, 'original period mismatch')
        check(0 <= o['residue'] < o['modulus'], 'residue not canonical')

    pair_admissibility_checks = 0
    for i,t in enumerate(target_indices):
        check(originals[t]['modulus'] == 3*primes[i]*tag_modulus, 'target label mismatch')
        for j,o in enumerate(originals):
            if j != t:
                pair_admissibility_checks += 1
                check(o['modulus'] % primes[i] != 0 or o['modulus'] % 3 != 0,
                      'global pair admissibility failed')

    core_points = tuple(product(*(tuple(range(p)) for p in primes),tuple(range(3))))
    check(len(core_points) == core_modulus, 'core inventory')
    core_values = []
    for coords in core_points:
        value, modulus = crt(tuple(zip(primes,coords[:n]))+((3,coords[n]),))
        check(modulus == core_modulus and all(value % p == coords[i] for i,p in enumerate(primes))
              and value % 3 == coords[n], 'core CRT mismatch')
        core_values.append(value)
    check(len(set(core_values)) == core_modulus, 'core residues not a bijection')
    inverse_tag = pow(tag_modulus,-1,core_modulus)

    groups = []
    for axis in range(n):
        partition = {}
        for index,coords in enumerate(core_points):
            key = tuple(coords[j] for j in range(n) if j != axis)
            partition.setdefault(key,[]).append(index)
        check(all(len(indices) == 3*primes[axis] for indices in partition.values()),
              'canonical fibre size mismatch')
        groups.append(partition)

    tag_weights = [Fraction(4,5**(j+1)) for j in range(K)]+[Fraction(1,tag_modulus)]
    check(sum(tag_weights,Fraction(0)) == 1, 'tag weights do not sum to one')
    excess_mass = Fraction(0)
    rectangle_masses = [Fraction(0) for _ in primes]
    private_stratum_counts = [0]*len(originals)
    actual_rectangles = [set() for _ in primes]
    actual_boundaries = [[] for _ in primes]
    stratum_rows = []
    canonical_fibres_tested = 0

    for depth,weight in enumerate(tag_weights):
        tag_value = 0 if depth == K else 5**depth
        masks, numeric_states = [], []
        excess_count = 0
        for core_index,(coords,core_value) in enumerate(zip(core_points,core_values)):
            value = tag_value+tag_modulus*(((core_value-tag_value)*inverse_tag) % core_modulus)
            check(0 <= value < period and value % core_modulus == core_value
                  and value % tag_modulus == tag_value, 'state CRT mismatch')
            mask = 0
            for original_index,o in enumerate(originals):
                numeric_membership_tests += 1
                numeric = value % o['modulus'] == o['residue']
                coordinate = depth >= o['tag_height'] and all(coords[i] == a for i,a in o['conditions'])
                check(numeric == coordinate, 'numeric/coordinate membership mismatch')
                if numeric:
                    mask |= 1 << original_index
            count = mask.bit_count()
            excess_count += max(count-1,0)
            if count == 1:
                private_stratum_counts[mask.bit_length()-1] += 1
            masks.append(mask)
            numeric_states.append(value)
        excess_mass += weight*Fraction(excess_count,core_modulus)

        rectangle_counts = []
        admitted_counts = []
        for axis,t in enumerate(target_indices):
            rectangles, admitted = set(), 0
            for boundary,indices in groups[axis].items():
                canonical_fibres_tested += 1
                covered, private = True, False
                for index in indices:
                    fibre_member_reads += 1
                    mask = masks[index]
                    covered = covered and mask != 0
                    private = private or mask == (1 << t)
                if covered and private:
                    admitted += 1
                    actual_boundaries[axis].append({'tag_stratum':depth,'other_P_coordinates':list(boundary)})
                    target_residue = originals[t]['residue']
                    for index in indices:
                        value = numeric_states[index]
                        if value % primes[axis] != target_residue % primes[axis] and value % 3 != target_residue % 3:
                            rectangles.add(index)
                            actual_rectangles[axis].add(depth*core_modulus+index)
            rectangle_counts.append(len(rectangles))
            admitted_counts.append(admitted)
            rectangle_masses[axis] += weight*Fraction(len(rectangles),core_modulus)
            # Only now compare membership-derived sets with the proved formulas.
            predicted = {i for i,c in enumerate(core_points)
                         if depth == K and c[n] != 1 and all(a != 1 for a in c[:n])}
            check(rectangles == predicted, 'actual canonical rectangle differs from formula')
            found_boundaries = {tuple(row['other_P_coordinates']) for row in actual_boundaries[axis]
                                if row['tag_stratum'] == depth}
            expected_boundaries = {boundary for boundary in groups[axis]
                                   if depth == K and all(a != 1 for a in boundary)}
            check(found_boundaries == expected_boundaries, 'covered/private boundary characterization')
        stratum_rows.append({'tag_valuation_stratum':depth,'tag_haar_weight':rational(weight),
                             'core_excess_sum':excess_count,'rectangle_core_counts':rectangle_counts,
                             'covered_private_boundary_counts':admitted_counts})

    check(all(count > 0 for count in private_stratum_counts), 'an original has no observed private stratum')
    witnesses = []
    for original_index,o in enumerate(originals):
        if o['kind'] == 'P':
            coords = tuple(o['metadata']['assignment'])+(1,)
        elif o['kind'] in ('Q0','Q2'):
            coords = (1,)+(0,)*(n-1)+(0 if o['kind']=='Q0' else 2,)
        else:
            coords = tuple(1 if i == o['metadata']['target_axis'] else 0 for i in range(n))+(1,)
        value, modulus = crt(tuple(zip(primes,coords[:n]))+((3,coords[n]),(tag_modulus,0)))
        check(modulus == period, 'private witness period')
        hits = []
        for j,test in enumerate(originals):
            private_witness_membership_tests += 1
            if value % test['modulus'] == test['residue']:
                hits.append(j)
        check(hits == [original_index], 'declared private witness failed')
        witnesses.append(str(value))

    hole, modulus = crt(tuple((p,0) for p in primes)+((3,1),(tag_modulus,1)))
    check(modulus == period and all(hole % o['modulus'] != o['residue'] for o in originals),
          'global hole failed')
    a, s = Fraction(A,D), sum((Fraction(1,p) for p in primes),Fraction(0))
    expected_R = Fraction(2,3)*a/tag_modulus
    expected_excess = (7*a+s-1)/(3*tag_modulus)
    check(excess_mass == expected_excess, 'full Haar excess formula')
    check(all(mass == expected_R for mass in rectangle_masses), 'full Haar rectangle formula')
    check(all(rectangle == actual_rectangles[0] for rectangle in actual_rectangles), 'rectangles not identical')
    ratio = sum(rectangle_masses,Fraction(0))/excess_mass
    check(ratio == 2*n*a/(7*a+s-1), 'ratio formula')
    check(ratio > Fraction(n,4), 'n/4 comparison')
    check(ratio > Fraction(2*n,7), '2n/7 comparison')
    check(ratio <= Fraction(n,3), 'n/3 comparison')
    check(s < Fraction(1,4) and a >= 1-s, 'elementary source bounds')

    return {'P':list(primes),'n':n,'D':D,'A':A,'K':K,'full_period':str(period),
            'full_period_enumerated':False,
            'originals':[{'index':i,'kind':o['kind'],'modulus':str(o['modulus']),
                          'residue':str(o['residue']),'tag_height':o['tag_height'],
                          'metadata':o['metadata'],'private_witness':witnesses[i],
                          'observed_private_compressed_states':private_stratum_counts[i]}
                         for i,o in enumerate(originals)],
            'global_hole':str(hole),'actual_covered_private_boundaries':actual_boundaries,
            'tag_strata':stratum_rows,'excess_haar_mass':rational(excess_mass),
            'rectangle_haar_masses':[rational(mass) for mass in rectangle_masses],
            'summed_rectangle_haar_mass':rational(sum(rectangle_masses,Fraction(0))),
            'ratio':rational(ratio),
            'counts':{'unique_compressed_states':(K+1)*core_modulus,
                      'numeric_membership_tests':numeric_membership_tests,
                      'private_witness_membership_tests':private_witness_membership_tests,
                      'global_pair_admissibility_checks':pair_admissibility_checks,
                      'compressed_canonical_fibres_tested':canonical_fibres_tested,
                      'compressed_fibre_member_reads':fibre_member_reads,
                      'explicit_check_calls':checks}}


def main():
    parser = ArgumentParser()
    parser.add_argument('--output')
    args = parser.parse_args()
    result = {'schema':'single-tag-all-pair-haar-control-v1',
              'scope':'Two declared finite exact controls for the same single-tag construction. Local covered-private fibres; globally noncovering. No unrestricted covering claim.',
              'compression':'All tag conditions are zero congruences. Tag valuation j<K has exact weight 4/5^(j+1); j=K has weight1/5^K. Every core P-by-3 residue is tested once per stratum.',
              'cases':[run_case((7,)),run_case((11,13))]}
    encoded = json.dumps(result,indent=2)+'\n'
    if args.output:
        with open(args.output,'w',encoding='utf-8') as stream:
            stream.write(encoded)
    else:
        print(encoded,end='')


if __name__ == '__main__':
    main()
