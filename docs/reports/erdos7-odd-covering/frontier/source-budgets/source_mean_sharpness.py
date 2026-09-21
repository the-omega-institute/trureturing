#!/usr/bin/env python3
"""Replay sharp near-J means and the direct square/scalar continuation boundary."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True
PROOF = 'profile-notes/321-384/339-irredundant-source-seven-labels-bound-the-actual-surplus.md'
CERTIFICATE = 'certificates/source_norms/source-budgets/source_mean_sharpness.json'
CONSUMER = 'certificates/source_norms/source-budgets/source_own_test_consumer.json'
SOURCES = (CONSUMER, 'certificate_io.py', 'verify_joint_frontier.py',
           'profile-notes/001-064/42-whole-hinge-absorption-sharpens-actual-survival.md',
           'profile-notes/321-384/327-actual-two-prime-survival-needs-a-masked-moment.md',
           'problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md',
           'frontier/source-budgets/irredundant_whole_j_finite_source.py',
           'profile-notes/321-384/329-a-finite-whole-j-neighborhood-covers-high-surplus.md')


def require(ok, message):
    if not ok:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Readable source module')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def original_source(src, N):
    require(N >= 3, 'The actual source construction starts at height3')
    family, private = [], []
    for original in src.original_family(N):
        a, b, e = original['exponents']
        r3, r5, r7 = original['coordinate_residues']
        if a and b:
            r3 = 1 if a <= 2 else 7 + 3**(a-1)
            r5 = (2 if a == 1 else 3) * 5**(b-1)
        if e:
            r7 = (6 if e == 1 else 1 + 7**(e-1)) if a == 0 else (
                (1 if e == 1 else 2 + 7**(e-1)) if a == 1 else
                (2 if e == 1 else 3 * 7**(e-1)))
        family.append(src.crt_class((a,b,e), (r3,r5,r7)))
        if e:
            xyz = (4 if a == 0 else 0 if a == 1 else 3, 4, r7)
        elif a and b:
            xyz = (r3,r5,4)
        elif a:
            xyz = (r3,4,4)
        else:
            xyz = (4,r5,4)
        private.append(xyz)
    require(len(family) == len({c['modulus'] for c in family}) == N*N + 5*N,
            'Complete distinct numerical original inventory')
    require(all(c['modulus'] > 1 and c['modulus'] % 2 for c in family), 'Odd nontrivial originals')
    witnesses = []
    for i, xyz in enumerate(private):
        x = src.crt_class((N,N,N), xyz)['residue']
        require([j for j,c in enumerate(family) if x % c['modulus'] == c['residue']] == [i],
                'Actual CRT private integer checked against every original')
        witnesses.append(dict(original_index=i, coordinates=xyz, integer=x))
    hole = src.crt_class((N,N,N), (4,4,4))['residue']
    require(all(hole % c['modulus'] != c['residue'] for c in family), 'Actual uncovered integer')
    return family, witnesses, hole


def test_residue(i, j, positive_seven):
    if j:
        r3 = 0 if i == 0 else 1 if i == 1 else 4
    else:
        r3 = 0 if i == 0 else 1 if i == 1 else (
            (3 if positive_seven else 4) if i == 2 else 18)
    return r3, 4 if j else 0


def finite_test_means(src, N, family, u7, w):
    """Integrate every supplied old35 test over a complete prefix partition."""
    raw = [c for c in family if c['exponents'][2] == 0]
    targets = [{(c['exponents'][k],c['coordinate_residues'][k])
                for c in raw if c['exponents'][k]} for k in range(2)]
    targets[0].update((2,r) for r in range(9))
    for i,j,positive in product(range(N+1), range(N+1), (False,True)):
        residues = test_residue(i,j,positive)
        for k,depth in enumerate((i,j)):
            if depth:
                targets[k].add((depth,residues[k] % ((3,5)[k]**depth)))
    axes = [src.prefix_partition(p,N,targets[k]) for k,p in enumerate((3,5))]
    for k,prime in enumerate((3,5)):
        for depth,residue in targets[k]:
            require(all(a >= depth or (x-residue) % prime**a != 0
                        for x,_,a in axes[k]), 'Every source/test indicator is constant on every partition leaf')
            require(sum(m for x,m,_ in axes[k] if x % prime**depth == residue) == prime**(N-depth),
                    'Each complete query cylinder has its exact Haar size')
    cells = (0,3,1,4,7)
    retained = []
    for x,m3,_ in axes[0]:
        active = [(5**c['exponents'][1],c['coordinate_residues'][1]) for c in raw
                  if x % 3**c['exponents'][0] == c['coordinate_residues'][0]]
        for y,m5,_ in axes[1]:
            if not any(y % modulus == residue for modulus,residue in active):
                require(x % 9 in cells, 'Actual surviving old cell')
                retained.append((x,y,F(m3*m5,15**N),w[cells.index(x % 9)]))
    rows, zero, positive_raw = [], F(0), F(0)
    for i,j in product(range(N+1), repeat=2):
        zres = test_residue(i,j,False)
        pres = test_residue(i,j,True)
        zmass = sum(m*weight for x,y,m,weight in retained
                    if x % 3**i == zres[0] % 3**i and y % 5**j == zres[1] % 5**j)
        pmass = sum(m for x,y,m,_ in retained
                    if x % 3**i == pres[0] % 3**i and y % 5**j == pres[1] % 5**j)
        if i or j:
            zero += zmass
        positive_raw += pmass
        rows.append(dict(old_exponents=(i,j), zero7_residues=zres,
                         positive7_old_residues=pres, zero7_mass=zmass,
                         positive7_raw35_mass=pmass))
    seven_targets = {(c['exponents'][2],c['coordinate_residues'][2])
                     for c in family if c['exponents'][2]}
    seven_targets.update((k,4) for k in range(1,N+1))
    seven_axis = src.prefix_partition(7,N,seven_targets)
    seven_rows = []
    for k in range(1,N+1):
        chosen = [(x,m) for x,m,_ in seven_axis if x % 7**k == 4]
        require(sum(m for _,m in chosen) == 7**(N-k), 'Complete selected seven test cylinder')
        require(all(not any(x % 7**c['exponents'][2] == c['coordinate_residues'][2]
                            for c in family if c['exponents'][2]) for x,_ in chosen),
                'Every positive7 test cylinder misses all actual seven restrictions')
        seven_rows.append(dict(exponent=k,residue=4,mass=F(1,7**k)/u7))
    positive = positive_raw * sum(row['mass'] for row in seven_rows)
    return dict(zero7=zero, positive7=positive, total=zero+positive,
                positive7_raw35_mean=positive_raw, old_test_rows=rows,
                positive7_test_cylinders=seven_rows,
                complete_nonunit_test_count=(N+1)**3-1,
                old_partition=dict(three_leaves=len(axes[0]),five_leaves=len(axes[1]),
                                   survivor_leaf_pairs=len(retained)))


def upper_endpoints(joint):
    """Affine dominance at both endpoints covers the whole K>=5 range."""
    rows = []
    for x in (F(0),F(1,7**4)):
        a, b = (6-x)/35, F(6,35)
        w = (1-a,1-a-b,F(1),F(1),F(1))
        for i,j in product(range(2,5), repeat=2):
            par = ((F(1,2),F(0),F(0),F(0),F(0)), (F(0),F(1,4)),
                   tuple(F(1,4) if k == i else F(0) for k in range(5)),
                   tuple(F(1,72) if k == j else F(0) for k in range(5)), F(3,4))
            d,n,eta,_,_ = joint.data(par)
            wn,wd,we = (tuple(w[k]*v[k] for k in range(5)) for v in (n,d,eta))
            R = lambda v: max(sum(v[:2]),sum(v[2:]))
            terms = (R(wn),max(wn),max(wd),sum(we),R(we),max(we),max(w))
            expected = (F(1,8),F(1,18),F(3,4)*(1-a),F(1,2)-a/6-b/9,
                        F(1,3),F(1,9),F(1))
            require(terms == expected, 'All max candidates match their affine dominant values')
            cap = terms[0]+terms[1]+terms[2]/18+(terms[3]+terms[4]+terms[5])/4+terms[6]/72
            require(cap == F(571,1260)+x/420 == F(17,36)-a/12-b/36,
                    'K-layer weighted cofactor formula at each dominance endpoint')
            rows.append(dict(layer_remainder=x,beta_cell=i,late_cell=j,terms=terms,cap=cap))
    require(F(571,1260)+F(3,20) == F(38,63), 'Sharp upper and lower limiting constant')
    return rows


def calculate_family(src, joint, N):
    family, private, hole = original_source(src,N)
    n,eta,z,partition = src.raw35_masses(family,N)
    t,q,r = (1-F(1,3**(N-2)))/18, (1-F(1,5**N))/4, (1-F(1,7**N))/6
    require(z == 1-q and eta == (F(1,9)-t,F(1,9),F(1,9),F(1,9),F(1,9)), 'Exact pure source masses')
    require(n == (z*(F(1,9)-t),z/9,(1-3*q)/9,(1-2*q)/9,(1-2*q)/9-t*q),
            'Actual original raw35 classes reproduce the exact cell formula')
    targets = {(c['exponents'][2],c['coordinate_residues'][2]) for c in family if c['exponents'][2]}
    seven = src.prefix_partition(7,N,targets)
    good = deleted_A = deleted_B = 0
    for x,m,_ in seven:
        hit = [any(c['exponents'][0] == a and c['exponents'][2]
                   and x % 7**c['exponents'][2] == c['coordinate_residues'][2] for c in family)
               for a in (0,1,2)]
        if not hit[0]:
            good += m
            deleted_A += m*hit[1]
            deleted_B += m*(hit[1] or hit[2])
    u = F(good,7**N)
    require(u == 1-r and F(deleted_A,7**N) == F(1,7) and F(deleted_B,7**N) == F(2,7),
            'Actual pure7 law and exact original A/B deletion')
    d = 1/(7*u)
    w = (1-d,1-2*d,F(1),F(1),F(1))
    s = sum(n)
    S = s-d*(n[0]+2*n[1])
    par = ((9*t,F(0),F(0),F(0),F(0)), (F(0),q), (F(0),F(0),q,F(0),F(0)),
           (F(0),F(0),F(0),F(0),t*q), z)
    avail,nn,ee,ss,_ = joint.data(par)
    require((nn,ee,ss) == (n,eta,s), 'Same actual effective9 source chart')
    T2 = (max(avail)/18+(sum(eta)+max(sum(eta[:2]),sum(eta[2:]))+max(eta))/4+F(1,72))/5
    S0 = s-T2-(1-F(1,7**N))*(n[0]+2*n[1])/5
    qJ = (18*t)**2*(4*q)**4*(1-F(1,7**N))
    delta, rho = 1-qJ, S-S0
    direct = finite_test_means(src,N,family,u,w)
    R = sum(n[2:])
    V0 = R+n[3]+(1-d)*z*t+q*(sum(a*b for a,b in zip(w,eta))+F(4,9)+t)
    C = R+z/9+z*t+q
    Vplus = r*(s+C)/u
    require(direct['zero7'] == V0 and direct['positive7_raw35_mean'] == s+C
            and direct['positive7'] == Vplus, 'Every finite test integrates to the claimed joint formula')
    upper = None
    if delta <= F(1,4000):
        K = 5
        require(delta < F(6,7**K), 'Strict forced-layer premise')
        while delta < F(6,7**(K+1)):
            K += 1
        bound = (1+7*delta)*(F(571,1260)+F(1,7**(K-1)*420))+F(3,20)+F(13,40)*delta
        require(V0+Vplus <= bound, 'Finite lower witness lies below the same-source uniform upper')
        upper = dict(forced_layers=K,delta=delta,mean_upper=bound)
    return dict(height=N, original_label_count=len(family), original_classes=family,
                private_integer_witnesses=private, private_membership_checks=len(family)**2,
                uncovered_integer=hole, uncovered_coordinates=(4,4,4), raw35_partition=partition,
                seven_partition_leaves=len(seven), source=dict(t=t,q=q,r=r,u7=u,d=d,w=w,n=n,eta=eta,
                z=z,s=s,S=S,S0=S0,qJ=qJ,delta=delta,rho=rho), finite_test=direct,
                closed_formula=dict(zero7=V0,positive7=Vplus,total=V0+Vplus,raw35_nonunit=C),
                forced_layer_upper=upper, limit_gap=F(38,63)-V0-Vplus)



def scalar_boundary(base, io, joint):
    consumer = json.loads(io.read_artifact_bytes(base/CONSUMER), object_pairs_hook=io._unique)
    for path,pin in consumer['source_sha256'].items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Current own-test source input '+path)
    raw_proof = io.read_artifact_bytes(base/PROOF)
    require(sha256(raw_proof).hexdigest() == consumer['ordinary_proof']['sha256']
            and len(raw_proof) == consumer['ordinary_proof']['byte_count'], 'Current own-test ordinary proof')
    require(sha256((base/'frontier/source-budgets/source_own_test_consumer.py').read_bytes()).hexdigest()
            == consumer['producer_sha256'], 'Current own-test producer')
    head = consumer['full_haar_head_chain']['head']
    delta = F(consumer['delta'])
    scale = 1+7*delta
    zeta = tuple(F(v) for v in consumer['source_weights'])
    kappa = tuple(F(6,5)-v for v in zeta)
    def weighted_square(dat, weights):
        d,n,eta,_,_ = dat
        P = max(sum(eta[l]*weights[l]*(b[l]**2-1) for l in range(5))
                +max(weights[l]*(b[l]+1)/9 for l in range(5)) for b in joint.BASES)
        zero = max(sum(weights[l]*(n[l]+eta[l]/4)*(b[l]**2-1) for l in range(5))
                   +max(weights[l]*(d[l]+F(1,4))*(b[l]+1)/9 for l in range(5)) for b in joint.BASES)
        return zero+F(7,8)*sum(eta[l]*weights[l] for l in range(5))+F(5,8)*P
    rows = []
    for i,j in product(range(2,5),repeat=2):
        par = ((F(1,2),F(0),F(0),F(0),F(0)), (F(0),F(1,4)),
               tuple(F(1,4) if k == i else F(0) for k in range(5)),
               tuple(F(1,72) if k == j else F(0) for k in range(5)), F(3,4))
        dat = joint.data(par)
        reference = joint.zero5_raw(('seven_block',(('s',F(1)),0)),dat)
        require(weighted_square(dat,(F(6,5),)*5) == reference, 'Unweighted quadratic A2 reconstruction')
        old = joint.zero7_raw(('s',F(1)),dat)
        new = old-reference+weighted_square(dat,kappa)
        require(old == F(263,48) and new == F(304687,57624), 'All nine centered-square comparison values')
        rows.append(dict(beta_cell=i,late_cell=j,old=old,new=new))
    M2 = scale*max(row['new'] for row in rows)
    e,D = F(head['denominator_mass_coefficient']),F(head['denominator_constant'])
    caps = tuple((p,F(c)) for p,c in head['full_factors'])
    J2 = joint.moment(caps,2)
    a,b = zeta[0],zeta[1]-zeta[0]
    Smax = F(1,4)+delta/2-a*(F(1,8)-delta/12)-b*(F(1,12)-delta/9)
    E = e*Smax-D
    require(E > 0 and J2 > 1 and e*J2*M2+(J2-1)*D > 0,
            'Positive containing source denominator and decreasing assigned seed formula')
    seed_floor = 1+(J2*M2+(J2-1)*Smax)/E
    require(M2 == F(1220880809,230496000) and J2 == F(1139,560)
            and Smax == F(123557689,576240000)
            and seed_floor == F(334490138381673633,3923164203788188) > 85,
            'Exact uniform lower bound on the assigned upper-majorant seed')
    certificates = []
    for (p,f,k),expected in zip(((17,85,171),(19,171,480),(23,480,1000)),
                                (F(625111,16384),F(8981,324),F(4544192000,14641))):
        ap,bp = F(3*p-1,(p-1)**2),F(1,4*(p-1)**2)
        A,B,C = F(k-f),F(f-k)+ap*f,bp*f*(k-1)
        gap = 4*A*C-B*B
        require(A > 0 and gap == expected > 0, 'All-real strict quadratic barrier')
        minimum = gap/(4*A)
        require(2*A*(B/(2*A)) == B and A*(B/(2*A))**2+minimum == C,
                'Exact completed-square coefficient identity')
        certificates.append(dict(prime=p,input_floor=f,output_strict_floor=k,
                                 a=ap,b=bp,quadratic=(A,B,C),four_AC_minus_B_squared=gap,
                                 global_minimum=minimum))
    cap29 = F(1,4)/F(1,4*(29-1)**2)
    require(cap29 == 784 < 1000, 'Next-prime legal input cap contradicts carried majorant floor')
    return dict(centered_square_vertices=rows,centered_square_upper=M2,head_square_multiplier=J2,
                head_e=e,head_D=D,raw_source_mass_upper=Smax,assigned_seed_floor=seed_floor,
                scalar_quadratics=certificates,next_prime=29,strict_legal_input_cap=cap29,
                carried_majorant_floor=1000,
                scope='The lower bound is on the allocated upper-bound expression, not on actual Gamma. The all-threshold obstruction rejects only this direct weighted-square allocation and scalar recurrence; it does not refute actual survival or the richer through37 hinge account.')


def calculate(base, proof, heights):
    io = module('sharpness_io',base/'certificate_io.py')
    src = module('sharpness_source',base/'frontier/source-budgets/irredundant_whole_j_finite_source.py')
    joint = module('sharpness_joint',base/'verify_joint_frontier.py')
    square_boundary = scalar_boundary(base,io,joint)
    endpoint_rows = upper_endpoints(joint)
    results = [calculate_family(src,joint,N) for N in heights]
    proof_bytes = io.read_artifact_bytes(proof)
    return io,encode(dict(schema='source-mean-sharpness-v1',
        scope='Finite actual irredundant noncover sources and one finite complete own test for each height. The ordinary proof establishes the general K-layer upper and sharp limiting uniform mean38/63. No finite-delta optimizer, nonlinear-hinge sharpness, or unrestricted covering conclusion.',
        source_sha256={p:sha256(io.read_artifact_bytes(base/p)).hexdigest() for p in SOURCES},
        ordinary_proof=dict(sha256=sha256(proof_bytes).hexdigest(),byte_count=len(proof_bytes)),
        producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        affine_dominance_endpoints=endpoint_rows, sharp_mean=F(38,63), results=results,
        direct_square_scalar_boundary=square_boundary))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    parser.add_argument('--proof',type=Path)
    parser.add_argument('--certificate',type=Path)
    parser.add_argument('--heights',type=int,nargs='+',default=[3,12,24])
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write',action='store_true')
    mode.add_argument('--check',action='store_true')
    args = parser.parse_args()
    require(args.heights == sorted(set(args.heights)), 'Increasing distinct verification heights')
    io,result = calculate(args.base,args.proof or args.base/PROOF,args.heights)
    certificate = args.certificate or args.base/CERTIFICATE
    if args.write:
        io.write_certificate_text(certificate,json.dumps(result,indent=2)+'\n')
    else:
        require(result == json.loads(io.read_artifact_bytes(certificate),object_pairs_hook=io._unique),
                'Complete exact sharpness certificate replay')
    print('PASS affine dominance at18 endpoint vertices; complete actual finite test integrals; all-threshold scalar boundary')
    for row in result['results']:
        print('N',row['height'],'originals',row['original_label_count'],
              'private checks',row['private_membership_checks'],'finite mean',row['finite_test']['total'])


if __name__ == '__main__':
    main()
