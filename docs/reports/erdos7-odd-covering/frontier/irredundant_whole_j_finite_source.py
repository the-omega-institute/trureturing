#!/usr/bin/env python3
"""Reconstruct an actual high-qJ finite source and verify a private point for every original class."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from math import gcd, prod
from pathlib import Path
import sys
sys.dont_write_bytecode = True
DEFAULT_PROOF = 'profile-notes/339-irredundant-source-seven-labels-bound-the-actual-surplus.md'
DEFAULT_CERTIFICATE = 'certificates/source_norms/irredundant_whole_j_finite_source.json'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Readable source module')
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


def crt_class(exponents, coordinates):
    powers = tuple(p**e for p, e in zip((3,5,7), exponents))
    d = prod(powers)
    a = sum(r*(d//q)*pow(d//q, -1, q)
            for q, r in zip(powers, coordinates) if q > 1) % d
    require(all(a % q == r % q for q, r in zip(powers, coordinates)), 'CRT reconstruction')
    return dict(exponents=exponents, modulus=d, residue=a,
                coordinate_residues=tuple(r % q for q, r in zip(powers, coordinates)))


def original_family(N):
    out = []
    for a in range(1,N+1):
        r3 = 2 if a == 1 else 6 if a == 2 else 3**(a-1)
        out.append(crt_class((a,0,0),(r3,0,0)))
    for b in range(1,N+1):
        out.append(crt_class((0,b,0),(0,5**(b-1),0)))
    for a,b in product(range(1,N+1), repeat=2):
        if a == 1:
            r3,r5 = 1,2*5**(b-1)
        elif a == 2:
            r3,r5 = (1 if b == 1 else 4),3*5**(b-1)
        elif (a,b) == (3,1):
            r3,r5 = 1+3**(a-1),4
        else:
            r3,r5 = 7+3**(a-1),3*5**(b-1)
        out.append(crt_class((a,b,0),(r3,r5,0)))
    for e in range(1,N+1):
        out.extend((crt_class((0,0,e),(0,0,6*7**(e-1))),
                    crt_class((1,0,e),(0,0,7**(e-1))),
                    crt_class((2,0,e),(3,0,2*7**(e-1)))))
    return tuple(out)


def prefix_partition(p, N, targets):
    """Exact integer-weight leaves; no enumeration of the p^N period."""
    branches = set()
    for depth, residue in targets:
        for a in range(depth):
            branches.add((a, residue % (p**a)))
    def visit(a, r):
        if (a,r) not in branches:
            yield (r, p**(N-a), a)
        else:
            for digit in range(p):
                yield from visit(a+1,r+digit*p**a)
    result = tuple(visit(0,0))
    require(sum(w for _,w,_ in result) == p**N, 'Complete compressed axis partition')
    return result


def raw35_masses(family, N):
    raw = tuple(c for c in family if c['exponents'][2] == 0)
    targets = []
    for k in range(2):
        targets.append({(c['exponents'][k],c['coordinate_residues'][k])
                        for c in raw if c['exponents'][k]})
    targets[0].update((2,r) for r in range(9))
    p3 = prefix_partition(3,N,targets[0])
    p5 = prefix_partition(5,N,targets[1])
    cells = (0,3,1,4,7)
    counts = {c:0 for c in cells}
    pure3_counts = {c:0 for c in cells}
    pure3 = tuple(c for c in raw if c['exponents'][1] == 0)
    pure5 = tuple(c for c in raw if c['exponents'][0] == 0)
    for r3,w3,_ in p3:
        if not any(r3 % (3**c['exponents'][0]) == c['coordinate_residues'][0] for c in pure3):
            require(r3 % 9 in pure3_counts, 'Actual surviving mod9 cell')
            pure3_counts[r3%9] += w3
        active5 = tuple((5**c['exponents'][1],c['coordinate_residues'][1])
                        for c in raw
                        if r3 % (3**c['exponents'][0]) == c['coordinate_residues'][0])
        for r5,w5,_ in p5:
            if not any(r5 % modulus == residue for modulus,residue in active5):
                require(r3%9 in counts, 'Actual raw35 surviving cell')
                counts[r3%9] += w3*w5
    five_count = sum(w5 for r5,w5,_ in p5
                     if not any(r5 % (5**c['exponents'][1]) == c['coordinate_residues'][1]
                                for c in pure5))
    return (tuple(F(counts[c],15**N) for c in cells),
            tuple(F(pure3_counts[c],3**N) for c in cells),
            F(five_count,5**N),
            dict(three_leaves=len(p3),five_leaves=len(p5),
                 weighted_cells=len(p3)*len(p5), raw35_period=15**N))


def private_witnesses(family, N):
    raw = tuple((i,c) for i,c in enumerate(family) if c['exponents'][2] == 0)
    partitions = tuple(prefix_partition(p,N,
                       {(c['exponents'][k],c['coordinate_residues'][k])
                        for _,c in raw if c['exponents'][k]})
                       for k,p in enumerate((3,5)))
    coordinates = {}
    for r3,_,_ in partitions[0]:
        active = tuple((i,5**c['exponents'][1],c['coordinate_residues'][1])
                       for i,c in raw
                       if r3 % (3**c['exponents'][0]) == c['coordinate_residues'][0])
        for r5,_,_ in partitions[1]:
            covered = tuple(i for i,d,a in active if r5 % d == a)
            if len(covered) == 1:
                coordinates.setdefault(covered[0],(r3,r5,3))
    require(all(not (3 % (3**c['exponents'][0]) == c['coordinate_residues'][0]
                        and 2 % (5**c['exponents'][1]) == c['coordinate_residues'][1])
                for _,c in raw), 'Common old point (3,2) avoids every original raw35 class')
    for i,c in enumerate(family):
        if c['exponents'][2]:
            coordinates[i] = (3,2,c['coordinate_residues'][2])
    require(set(coordinates) == set(range(len(family))),
            'Private construction succeeds for every original class; none removed')
    result = []
    for i,c in enumerate(family):
        x = crt_class((N,N,N),coordinates[i])['residue']
        covered = tuple(j for j,other in enumerate(family)
                        if x % other['modulus'] == other['residue'])
        require(covered == (i,), 'Private integer lies in its own class and none of the other originals')
        result.append(dict(original_index=i,modulus=c['modulus'],residue=c['residue'],
                           private_integer=x,coordinate_witness=coordinates[i],
                           progression_parameter=(x-c['residue'])//c['modulus']))
    require(len({v['private_integer'] for v in result}) == len(family), 'Distinct private integers')
    return result,dict(three_leaves=len(partitions[0]),five_leaves=len(partitions[1]),
                       weighted_cells=len(partitions[0])*len(partitions[1]),
                       complete_membership_checks=len(family)**2,period=105**N,
                       three_axis_leaves=partitions[0],five_axis_leaves=partitions[1],
                       scope='The prefix trees partition the full finite raw35 coordinates into leaves of constant original-label membership. Search visits every leaf pair with seven coordinate fixed at3. Irredundancy is certified independently by direct evaluation of each final integer against every original modulus, not by trusting the partition or a search-success marker.')


def calculate(base, proof, N):
    require(N >= 12, 'This benchmark uses N at least 12')
    io = module('noncontained_io',base/'certificate_io.py')
    src = module('noncontained_raw',base/'verify_joint_frontier.py')
    family = original_family(N)
    require(len(family) == len({c['modulus'] for c in family}) == (N+1)**2-1+3*N,
            'All distinct original labels retained')
    containments = []
    for i, larger_class in enumerate(family):
        d,a = larger_class['modulus'],larger_class['residue']
        for j, smaller_class in enumerate(family):
            if i == j:
                continue
            d2,a2 = smaller_class['modulus'],smaller_class['residue']
            if d2 % d == 0 and (a2-a) % gcd(d,d2) == 0:
                containments.append((i,j))
    require(not containments, 'No original congruence class is contained in another')
    witnesses,private_partition = private_witnesses(family,N)
    uncovered = crt_class((N,N,N),(3,2,3))['residue']
    require(all(uncovered % c['modulus'] != c['residue'] for c in family),
            'Explicit uncovered integer; the benchmark is not a cover')
    seven = tuple((j,e,j*7**(e-1),7**e) for e in range(1,N+1) for j in (1,2,6))
    require(all((a-b) % gcd(d,q) != 0 for i,(_,_,a,d) in enumerate(seven)
                for _,_,b,q in seven[i+1:]), 'All chosen first-exit seven cylinders are disjoint')
    t = (1-F(1,3**(N-2)))/18
    q = (1-F(1,5**N))/4
    v = F(1,7**N)
    par = ((9*t,F(0),F(0),F(0),F(0)),(F(0),q),
           (F(0),F(0),F(1,5),q-F(1,5),F(0)),
           (F(0),F(0),F(1,135),F(0),t*q-F(1,135)),1-q)
    avail,n,pure,s,D = src.data(par)
    n_direct,pure_direct,z_direct,partition = raw35_masses(family,N)
    require(n_direct == n and pure_direct == pure and z_direct == 1-q,
            'Actual original cylinders reproduce every raw35/pure3 cell mass and pure5 mass')
    require(s == F(5,9)-t-q == sum(n_direct), 'Actual raw35 mass')
    u7 = 1-sum(F(1,7**e) for e in range(1,N+1))
    require(u7 == (5+v)/6, 'Exact actual pure7 normalization')
    mA,mB = n[0]+n[1],n[1]
    carrier = mA+mB
    deletion = sum(F(1,7**e)*carrier/u7 for e in range(1,N+1))
    require(deletion == (1-v)*carrier/(5+v), 'Complete actual disjoint mixed7 union')
    S = s-deletion
    T2 = (max(avail)/18+(sum(pure)+max(pure[0]+pure[1],sum(pure[2:]))+max(pure))/4+F(1,72))/5
    S0 = s-T2-(1-v)*carrier/5
    rho = S-S0
    qJ = (18*t)**2*(4*q)**4*(1-v)
    delta = 1-qJ
    ir_upper = F(273719,3937640)+F(2994037,11812920)*delta
    require(0 < delta < F(1,4000) and F(1,40) < rho < ir_upper < F(7,100),
            'Actual high-qJ source inside the remaining339 region')
    existing = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/j_whole_face_high_rho_finite_guard.json'),object_pairs_hook=io._unique)
    if N == 12:
        witness = existing['actual_finite_witness']
        require(all(F(witness[k]) == value for k,value in dict(S=S,S0=S0,rho=rho,delta=delta).items()),
                'This is exactly the existing329 actual finite source, now with every containment checked')
    paths = ('certificate_io.py','verify_joint_frontier.py',
             'profile-notes/311-imperfect-j-source-alignment-forces-a-sharp-sector-surplus.md',
             'profile-notes/329-a-finite-whole-j-neighborhood-covers-high-surplus.md',
             'certificates/source_norms/j_whole_face_high_rho_finite_guard.json')
    proof_bytes = io.read_artifact_bytes(proof)
    result = dict(schema='irredundant-whole-j-finite-source-v1',height=N,
        scope='Actual finite effective9 source; every original class has a verified private integer, so every class is necessary to its forbidden union. Reuses329 actual witness. This finite family does not cover the integers. No Lean or test-extremality assertion.',
        source_sha256={p:sha256(io.read_artifact_bytes(base/p)).hexdigest() for p in paths},
        ordinary_proof=dict(sha256=sha256(proof_bytes).hexdigest(),byte_count=len(proof_bytes)),
        producer_sha256=sha256(io.read_artifact_bytes(Path(__file__))).hexdigest(),
        original_forbidden_classes=family,
        original_label_count=len(family),ordered_distinct_pairs=len(family)*(len(family)-1),
        original_containments=containments,
        private_integer_witnesses=witnesses,private_witness_verification=private_partition,
        uncovered_integer=uncovered,uncovered_coordinate_witness=(3,2,3),
        original_seven_cylinders=seven,seven_cylinders_pairwise_disjoint=True,
        raw35_compressed_verification=partition,raw_parameters=par,
        raw35_cell_masses=n_direct,pure3_cell_masses=pure_direct,pure5_mass=z_direct,
        mass=dict(raw35=s,pure7=u7,old_root0=mA,old_cell1=mB,carrier=carrier,
                  mixed7_deletion=deletion,S=S,S0=S0,rho=rho,qJ=qJ,delta=delta,
                  same_delta_339_upper=ir_upper),
        finite_inventory='All physical exponents are at most N. Every original label of this family is listed; absent mixed cofactors are not added. S0 retains the established complete cap tails and the empty-carrier weight7^-N.')
    return io,encode(result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[1])
    parser.add_argument('--proof',type=Path)
    parser.add_argument('--certificate',type=Path)
    parser.add_argument('--height',type=int,default=12)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write',action='store_true')
    mode.add_argument('--check',action='store_true')
    args = parser.parse_args()
    proof = args.proof or args.base/DEFAULT_PROOF
    certificate = args.certificate or args.base/DEFAULT_CERTIFICATE
    io,result = calculate(args.base,proof,args.height)
    if args.write:
        io.write_certificate_text(certificate,json.dumps(result,indent=2)+'\n')
    else:
        require(result == json.loads(io.read_artifact_bytes(certificate),object_pairs_hook=io._unique),
                'Full exact certificate replay')
    print('PASS',result['original_label_count'],'original labels;',result['ordered_distinct_pairs'],
          'ordered pair checks; zero containments; private integer for every class; exact actual source mass')
    print('compressed raw35',result['raw35_compressed_verification'])
    print('private witness verification',{k:v for k,v in result['private_witness_verification'].items()
                                          if k not in ('three_axis_leaves','five_axis_leaves','scope')})
    for key in ('S','S0','rho','delta','same_delta_339_upper'):
        print(key,result['mass'][key],float(F(result['mass'][key])))


if __name__ == '__main__':
    main()
