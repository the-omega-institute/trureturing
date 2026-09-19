#!/usr/bin/env python3
"""Exact numerical/source companion to the ordinary compact-neighborhood proof.

No branch scans or LPs. The proof of compactness is in the accompanying text.
"""
import argparse
from decimal import Decimal, localcontext
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j-source/j_compact_source_neighborhood.json'
SOURCE = 'certificates/source_norms/j-source/j_face_heavy_positive175189_complete_moment_cost_comparison.json'
SOURCE_SHA256 = 'c9fe551e579b5d9e669efb961903244521da90ba18ef26c6ebb19c3308f6a775'
ANCHORS = (
    'profile-notes/46-one-forbidden-carrier-mixture-strengthens-survival.md',
    'profile-notes/48-actual-source-compatibility-excludes-a-relaxed-mass-endpoint.md',
    'profile-notes/59-endpoint-linear-source-deletion-bound.md',
    'profile-notes/62-endpoint-square-from-cylinder-intersections.md',
    'profile-notes/65-endpoint-numerator-from-common-cost-constraints.md',
    'profile-notes/71-global-j-k-control-faces-and-exact-escape-gaps.md',
    'profile-notes/72-a-linear-gap-on-the-entire-controlling-beta-face.md',
    'profile-notes/j-source/130-the-whole-j-face-forces-source-anti-alignment.md',
    'profile-notes/j-source/219-one-late-source-split-controls-complete-saturated-j-heads.md',
    'profile-notes/j-source/264-seven-retained-states-and-two-seven-depths-control-complete-j-heads.md',
    'profile-notes/j-source/288-retaining375-strengthens-the-complete-j-survival-hinge.md',
    'profile-notes/j-source/296-joint-positive175189-strengthens-the-complete-j-survival-hinge.md',
    'profile-notes/j-source/298-retaining375-certifies-the-complete-heavy-cost.md',
    'profile-notes/j-source/299-the-complete-saturated-j-comparison-crosses403.md',
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable provider')
    item = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(item)
    return item


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Unique JSON keys')
        result[key] = value
    return result


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


def decode_tag(value):
    if isinstance(value, list):
        return tuple(map(decode_tag, value))
    if isinstance(value, str):
        try:
            return F(value)
        except ValueError:
            return value
    return value


def polynomial(poly, n):
    c, b, a = poly
    return c+b*n+a*n*n


def product(values):
    ans = F(1)
    for value in values:
        ans *= value
    return ans


def calculate(base):
    io = module('compact_J_io', base/'certificate_io.py')
    raw = io.read_artifact_bytes(base/SOURCE)
    require(sha256(raw).hexdigest() == SOURCE_SHA256, 'Pinned complete299 source')
    data = json.loads(raw, object_pairs_hook=unique)
    pins = dict(data['source_sha256'])
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin,
                'Current logical source pin '+path)
    pins[SOURCE] = SOURCE_SHA256
    for path in ANCHORS:
        pin = sha256(io.read_artifact_bytes(base/path)).hexdigest()
        require(path not in pins or pins[path] == pin, 'Consistent ordinary proof source '+path)
        pins[path] = pin
    require(data['all_original_indices'] == list(range(52)) and len(data['results']) == 59,
            'Every original52 cost and all seven complete external targets')
    vals = {r['name']: F(r['upper']) for r in data['results']}
    mass = F(data['survivor_mass'])
    weights = list(map(F, data['cost_weights']))
    signed = F(data['signed_mass_coefficient'])
    outside = F(data['complete_square_weight'])
    offset = F(data['offset'])
    a, b = (F(data['count_law'][k]) for k in
            ('remaining_hinge1_coefficient', 'whole_constant_coefficient'))
    require(mass == F(3,20) and len(weights) == 52 and min(weights)>0
            and signed<0 and outside>0 and signed+outside>0 and (a,b)==(F(1,7986),F(1,87846)),
            'Exact signed actual-mass and complete count interface')
    count = a*(vals['mean']-mass)+b*mass
    denominator = mass-vals['hinge4']/6-(sum(vals['AP11-'+str(i)] for i in range(4))+count)/7
    numerator = signed*mass+sum(w*vals['cost-'+str(i)] for i,w in enumerate(weights))+outside*vals['square']
    comparison = offset+numerator/denominator
    given = data['comparison_upper']
    require(denominator == F(given['denominator']) and numerator == F(given['numerator'])
            and comparison == F(given['comparison']) and count == F(given['complete_count_tail'])
            and denominator>0 and numerator>0 and 0<offset<comparison<403,
            'Independent full signed299 comparison, complete count tail and strict signs')
    margin = (403-offset)*denominator-numerator
    require(margin == F(given['target403_numerator_margin'])>0,
            'Strict numerator margin is the same299 margin')
    target, floor = (403+comparison)/2, denominator/2
    require(comparison<target<403 and 0<floor<denominator,
            'Strict interior comparison target and denominator floor')

    # Recover every exact target function from the already-checked299
    # all-load envelope, including its recorded polynomial difference.
    basis = {r['name']: r for r in data['basis']}
    require(len(basis)==34 and len(data['proof_data'])==59, 'Unchanged34-observation source')
    source = module('compact_J_original_functions', base/'verify_joint_frontier.py')
    targets = []
    for r, proof in zip(data['results'], data['proof_data']):
        name = r['name']
        require(proof['name']==name, 'Canonical original target order')
        coeff = {k:F(v) for k,v in proof['coefficients'].items()}
        low = [sum(v*F(basis[k]['low_load_values'][i]) for k,v in coeff.items())
               -F(r['low_load_gaps'][i]) for i in range(8)]
        poly = tuple(sum(v*F(basis[k]['tail_polynomial'][i]) for k,v in coeff.items())
                     -F(r['tail_gap_polynomial'][i]) for i in range(3))
        if name.startswith('cost-'):
            index = int(name[5:]); tag = decode_tag(data['original_cost_tags'][index])
            require(low == [source.zero5_cost(tag,n) for n in range(1,9)],
                    'Original finite cost identity '+name)
            degree, leading, constant, entrance = source.zero5_cost_metadata(tag)
            expected = (constant, leading if degree==1 else F(0), leading if degree==2 else F(0))
            require(degree in (1,2) and entrance<=9 and poly==expected,
                    'Original whole cost polynomial '+name)
        else:
            require(name in ('AP11-0','AP11-1','AP11-2','AP11-3','hinge4','mean','square'),
                    'Only the seven declared external target functions')
            original = basis[name]
            require(low==list(map(F,original['low_load_values']))
                    and poly==tuple(map(F,original['tail_polynomial'])),
                    'Exact original external target identity '+name)
        extended = low+[polynomial(poly,9)]
        require(min(low)>=0 and all(extended[n]>=extended[n-1] for n in range(1,9))
                and poly[2]>=0 and 19*poly[2]+poly[1]>=0,
                'Nonnegative nondecreasing target on the whole integer domain '+name)
        ratios = [abs(extended[n]-extended[n-1])/F(2*n+1) for n in range(1,9)]
        tail_lipschitz = abs(poly[2])+abs(poly[1])/19
        constant = max(ratios+[tail_lipschitz])
        require(constant>=0 and all(abs(extended[n]-extended[n-1])<=constant*(2*n+1)
                                    for n in range(1,9)), 'Every head increment including8->9')
        targets.append({'name':name,'low_load_values':low,'tail_polynomial':poly,
                        'quadratic_increment_constant':constant})

    primes = (3,5,7)
    one_total = product(F(p,p-1) for p in primes)
    square_total = product(F(p*(p+1),(p-1)**2) for p in primes)
    tails=[]
    for cut in (8,16,32):
        first = one_total-product(sum((F(1,p**n) for n in range(cut+1)),F(0)) for p in primes)
        second = F(6,5)*(square_total-product(sum((F(2*n+1,p**n) for n in range(cut+1)),F(0)) for p in primes))
        # Closed forms verify the full geometric complement without truncating it.
        square_head = [F(p*(p+1),(p-1)**2)-F(1,p**(cut+1))*
                       (F((2*cut+3)*p,p-1)+F(2*p,(p-1)**2)) for p in primes]
        require(second==F(6,5)*(square_total-product(square_head)) and first>0 and second>0,
                'Complete positive geometric tails, no finite-tail surrogate')
        tails.append({'exponent_cut':cut,'forbidden_haar_tail':first,
                      'uniform_squared_load_tail':second,'carrier_weight_tail':F(1,7**cut)})
    require(all(tails[i+1]['uniform_squared_load_tail']<tails[i]['uniform_squared_load_tail']
                for i in range(2)), 'Ordered check values of complete tail formula')
    return encode({'schema':'erdos7-j-compact-neighborhood-companion-v1','source_sha256':pins,
                   'face_upper':comparison,'face_numerator':numerator,'face_denominator':denominator,
                   'strict403_numerator_margin':margin,'neighborhood_comparison_target':target,
                   'neighborhood_denominator_floor':floor,'epsilon':'existence-only-not-numerically-evaluated',
                   'positive_numerator_mass_floor_coefficient':signed+outside,
                   'complete_count_tail':count,'original_target_increment_bounds':targets,
                   'complete_tail_examples':tails,'scope':'Ordinary compactness existence proof for an actual J source neighborhood. The companion checks exact source identity, complete signed arithmetic and uniform-tail inputs; no LP, branch scan, numerical radius, global join, later-prime continuation or Lean claim.'})


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('compact_J_companion_io', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE,json.dumps(result,indent=2)+'\n')
    else:
        given = json.loads(io.read_artifact_bytes(args.base/CERTIFICATE), object_pairs_hook=unique)
        require(given==result, 'Exact complete source/numerical companion replay')
    with localcontext() as context:
        context.prec=45
        for name in ('face_upper','neighborhood_comparison_target','neighborhood_denominator_floor'):
            val=F(result[name]);print(name,Decimal(val.numerator)/Decimal(val.denominator))
    print('PASS; original targets=59; no numerical epsilon asserted')


if __name__=='__main__':
    main()
