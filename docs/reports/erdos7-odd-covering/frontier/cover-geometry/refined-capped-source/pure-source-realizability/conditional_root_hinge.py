"""Complete conditional root-mixture hinge and one fixed-candidate diagnostic.
Standalone standard-library replay; reuses pinned827 head and tail arithmetic.
The exact first moment retains all geometric heights; only low product atoms
are finite. No solver or candidate/source search is performed.
"""
from fractions import Fraction as F
from itertools import product
from math import prod
from pathlib import Path
import argparse
import hashlib
import json

SOURCE_CERTIFICATE = 'retained_factorial_hinge_certificate.json'
SOURCE_RESULT = 'retained_factorial_hinge.json'
EXPECTED_C = '17557f86d60a40310275025219d893e28ba103b5f099cf53886a8eb8ef970aca'
EXPECTED_R = '1e76928fa5e63ca221913ad6cdd7ba0db4a54ab093a3a2c26086e1e08b1710e5'
MATH_FIELDS = ('actual_family','expected_hinge','leaves','nonzero_u','normalization',
               'partitions','pattern_encoding','phase45','primes','selected_labels',
               'tail','threshold','weights')
MATH_SHA = '7c2aea132c63baaecadc6d398c8cc7f848fc2bd82887fdb1918766c69bcc3574'
Q = (5,7,11,13,17,19,23)
MAX = 28
checks = 0

def need(ok, label):
    global checks
    checks += 1
    if not ok:
        raise ValueError(label)


def load_unique(path, expected=None):
    raw = path.read_bytes()
    if expected is not None:
        need(hashlib.sha256(raw).hexdigest() == expected, 'pinned input '+path.name)
    def unique(pairs):
        out = {}
        for key, value in pairs:
            need(key not in out, 'duplicate key '+key)
            out[key] = value
        return out
    return json.loads(raw, object_pairs_hook=unique)


def convolve(a, b):
    out = [F(0)]*MAX
    for i in range(1, MAX):
        if a[i]:
            for j in range(1, (MAX-1)//i+1):
                out[i*j] += a[i]*b[j]
    return out


def q_law(q, pi, singleton):
    C = F(q-1, q-2)
    need(pi > C/q**2, 'live depth-two nonsaturation')
    atoms = [F(0)]*MAX
    if singleton:
        need(pi <= C/q, 'singleton cap')
        atoms[2] = pi-C/q**2
        for n in range(3, MAX):
            atoms[n] = C*F(q-1, q**n)
        mean = 2*pi+C/F(q*(q-1))
    else:
        need(pi >= C/q, 'other first-depth nonsaturation')
        atoms[1] = pi-C/q
        for n in range(2, MAX):
            atoms[n] = C*F(q-1, q**n)
        mean = pi+C/F(q-1)
    need(min(atoms) >= 0 and sum(atoms) < pi, 'positive finite atoms with nonzero full tail')
    return atoms, mean


def ternary_law(M, R, V):
    need(F(0) <= V <= R <= M, 'genuine ternary submeasure caps')
    a = [F(0)]*MAX
    a[1] = M-R
    a[2] = R-V
    for n in range(3, MAX):
        a[n] = 2*V/F(3**(n-2))
    return a, M+R+F(3, 2)*V


def hinge(h, mean, mass, atoms):
    return mean-h*mass+sum(((h-n)*atoms[n] for n in range(1, h)), F(0))


def finite_controls():
    start = checks
    leaves = (4,7,2,5,8)
    retained = {True:(F(1,5),F(1,10),F(0),F(1,20),F(0)),
                False:(F(0),F(1,5),F(1,10),F(0),F(1,5))}
    def layout(seed):
        out=[]
        for e,f in product(range(4),range(3)):
            a3=(4 if seed==-1 or e<3 else 4+9*((seed+2*f)%3))%3**e
            a5=0 if seed==-1 or f==0 else (e+seed)%2 if f==1 else (e+2*seed)%5+5*((e+seed)%5)
            out.append((e,f,a3,a5))
        return out
    def actual(query,singleton,h,leaf):
        xs=[x for x in range(25) if (x%5==0)==singleton]
        loads=[sum(x3%3**e==a3 and x5%5**f==a5 for e,f,a3,a5 in query)
               for x3,x5 in product((leaf,leaf+9,leaf+18),xs)]
        return F(sum(max(v-h,0) for v in loads),len(loads))
    def bound(pi,singleton,h,M,R,V):
        b,bmean=q_law(5,pi,singleton)
        a,amean=ternary_law(M,R,V)
        return hinge(h,amean*bmean,M*pi,convolve(a,b))
    def by_weights(pi,singleton,h,w):
        return bound(pi,singleton,h,sum(w),max(sum(w[:2]),sum(w[2:])),max(w))
    for h in range(21):
        total_root=total_leaf=F(0)
        for singleton,pi in ((True,F(1,5)),(False,F(4,5))):
            w=retained[singleton]; M=sum(w); R=max(sum(w[:2]),sum(w[2:])); V=max(w)
            root=bound(pi,singleton,h,M,R,V)
            leaf=bound(pi,singleton,h,M,M,M)
            A0=bound(pi,singleton,h,F(1),F(0),F(0))
            A1=bound(pi,singleton,h,F(1),F(1),F(0))-A0
            A2=bound(pi,singleton,h,F(1),F(1),F(1))-A0-A1
            need(min(A0,A1,A2)>=0,'nonnegative stoploss increments')
            need(root==M*A0+R*A1+V*A2,'root increment identity')
            need(leaf-root==(M-R)*A1+(M-V)*A2,'root/leaf difference identity')
            rev=tuple(reversed(w)); mid=tuple((a+b)/2 for a,b in zip(w,rev))
            need(2*by_weights(pi,singleton,h,mid)<=root+by_weights(pi,singleton,h,rev),
                 'retained-table midpoint convexity')
            for seed in (-1,0,1,2):
                need(actual(layout(seed),singleton,h,4)<=bound(pi,singleton,h,F(1),F(1),F(1))/pi,
                     'arbitrary-cofactor phases in one actual cell')
            total_root+=root; total_leaf+=leaf
        for seed in (-1,0,1,2):
            exact=sum(pi*w*actual(layout(seed),singleton,h,leaf)
                      for singleton,pi in ((True,F(1,5)),(False,F(4,5)))
                      for leaf,w in zip(leaves,retained[singleton]))
            need(exact<=total_root<=total_leaf,'actual retained mixture and root/leaf domination')
        def mixed(t):
            return by_weights(t,True,h,retained[True])+by_weights(1-t,False,h,retained[False])
        lo,hi=F(3,19),F(4,19)
        need(2*mixed((lo+hi)/2)==mixed(lo)+mixed(hi),'fixed-live-cell block affineness')
    # Complete single-prime Haar counterexample: separate first-digit cells
    # can worsen the inherited full-source hinge despite being valid.
    q=5
    old=F(1,q-1); separate=F(q,q-1)
    need(separate==q*old and separate>old,'no full-source dominance')
    return {'checks':checks-start,'finite_period':675,'fixed_layouts':4,
            'thresholds':list(range(21)),'literal_ternary_leaves':list(leaves),
            'colour_partition':[[0],[1,2,3,4]],
            'actual_law':'Haar suffix above each ternary leaf and Haar modulo25',
            'properties':['arbitrary-cofactor phases','root/leaf identity',
                          'retained-table convexity','fixed-live-cell block affineness'],
            'single_prime_haar_counterexample':{'q':q,'h':1,'full':str(old),'cell_bound':str(separate)}}

def compute(c, previous, finite_controls):
    need(c['primes'] == list(Q) and c['leaves'] == [4, 7, 2, 5, 8], 'same source coordinates')
    need(c['phase45'] == 31 and c['threshold'] == 16, 'same candidate contract')
    need(c['normalization'] == previous['normalization'] == 'nu_u restricted to U / nu_u(U)',
         'same retained survivor denominator')
    need(previous['point']['name'] == 'C' and previous['point']['vertex5'] == 2
         and previous['point']['other_mask'] == 63, 'only authorized C point')
    pi = tuple(tuple(map(F, row)) for row in previous['point']['probabilities'])
    want_pi = ((F(4, 15), F(4, 15), F(7, 15)),) + tuple(
        (F(q-1, q*(q-2)), 1-F(q-1, q*(q-2))) for q in Q[1:])
    need(pi == want_pi and all(sum(row) == 1 for row in pi), 'literal C probabilities')
    patterns = tuple(product(range(3), *[range(2) for _ in Q[1:]]))
    weights = tuple(map(F, c['weights']))
    need(sum(weights) == 1 and c['weights'] == previous['weights'], 'same normalized weights')
    U = [[F(0)]*len(patterns) for _ in range(5)]
    seen = set()
    for row in c['nonzero_u']:
        l, s, v = row['leaf_index'], row['pattern_id'], F(row['u'])
        need(type(l) is int and type(s) is int and 0 <= l < 5 and 0 <= s < 192,
             'retained coordinate')
        need((l, s) not in seen and 0 < v <= weights[l], 'one valid retained entry')
        seen.add((l, s)); U[l][s] = v
    need(len(seen) == 106 and previous['nonzero_u'] == 106, 'same fixed table')

    laws = {}
    for i, q in enumerate(Q):
        for col, prob in enumerate(pi[i]):
            singleton = col < 2 if i == 0 else col == 0
            need(len(c['partitions'][i][col]) == 1 if singleton
                 else len(c['partitions'][i][col]) > 1, 'literal category type')
            laws[i, col] = q_law(q, prob, singleton)

    root_atoms = [F(0)]*MAX
    leaf_atoms = [F(0)]*MAX
    root_mean = leaf_mean = mass = F(0)
    pattern_rows = []
    cache = {}
    for sid, s in enumerate(patterns):
        u = tuple(U[l][sid] for l in range(5))
        M = sum(u)
        if not M:
            continue
        R, V = max(sum(u[:2]), sum(u[2:])), max(u)
        cell_pi = prod((pi[i][col] for i, col in enumerate(s)), start=F(1))
        # q5 colours0 and1 have identical auxiliary laws at this fixed point.
        key = (0 if s[0] < 2 else 2,) + s[1:]
        if key not in cache:
            a = [F(0)]*MAX; a[1] = F(1)
            m = F(1)
            for i, col in enumerate(key):
                b, bmean = laws[i, col]
                a = convolve(a, b)
                m *= bmean
            cache[key] = a, m
        qatoms, qmean = cache[key]
        b3, m3 = ternary_law(M, R, V)
        b3leaf, m3leaf = ternary_law(M, M, M)
        ra, la = convolve(b3, qatoms), convolve(b3leaf, qatoms)
        for n in range(1, MAX):
            root_atoms[n] += ra[n]
            leaf_atoms[n] += la[n]
        root_mean += m3*qmean
        leaf_mean += m3leaf*qmean
        mass += M*cell_pi
        # Component domination at the one requested leaf comparison threshold.
        rh = hinge(16, m3*qmean, M*cell_pi, ra)
        lh = hinge(16, m3leaf*qmean, M*cell_pi, la)
        need(F(0) <= rh <= lh, 'per-cell root/leaf domination')
        pattern_rows.append({'pattern_id': sid, 'pattern': list(s), 'M': str(M),
                             'R': str(R), 'V': str(V), 'probability': str(cell_pi),
                             'rootH16': str(rh), 'leafH16': str(lh)})

    old = {k: F(v) for k, v in previous['exact'].items()}
    need(mass == old['M'] and 0 < old['L'] <= mass <= 1, 'same retained initial mass and certified floor')
    K4, L, tail = old['K4'], old['L'], old['tail']
    T29 = F(120361, 74088)
    T = F(c['tail']['expected_upper'])
    need(tail == 27*T29*T*K4, 'same complete tail debit; factor29 once')
    need(old['oldGate'] == 12*L-old['oldH16']-tail, 'inherited old gate identity')
    need(sum(root_atoms) < mass and sum(leaf_atoms) < mass, 'complete means retain tails above atom cutoff')

    curve = []
    for h in range(MAX+1):
        H = hinge(h, root_mean, mass, root_atoms)
        G = (28-h)*L-H-tail
        need(H >= 0, 'nonnegative full hinge')
        curve.append({'h': h, 'Hroot': str(H), 'G': str(G),
                      'Hroot_decimal': float(H), 'G_decimal': float(G)})
    for h in range(1, MAX):
        need(F(curve[h-1]['Hroot'])-2*F(curve[h]['Hroot'])+F(curve[h+1]['Hroot'])
             == root_atoms[h], 'integer second difference equals exact atom')
    need(all(F(curve[h]['Hroot']) >= F(curve[h+1]['Hroot']) for h in range(MAX)),
         'hinge monotonicity')
    root16 = F(curve[16]['Hroot'])
    leaf16 = hinge(16, leaf_mean, mass, leaf_atoms)
    G16 = F(curve[16]['G'])
    need(root16 <= leaf16 and G16-old['oldGate'] == old['oldH16']-root16,
         'same-source hinge replacement identity')
    best = max(curve[:28], key=lambda row: F(row['G']))
    closed_best = max(curve, key=lambda row: F(row['G']))
    result = {
        'schema': 'e7-conditional-root-hinge-result-v1',
        'contract': 'one fixed phase31 candidate at C; no solver or new candidate',
        'inputs': [{'file': SOURCE_CERTIFICATE, 'sha256': EXPECTED_C}, {'file': SOURCE_RESULT, 'sha256': EXPECTED_R}],
        'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'point': previous['point'],
        'normalization': c['normalization'],
        'inherited_exact': {k: str(old[k]) for k in ('M', 'L', 'K4', 'tail', 'oldH16', 'oldGate')},
        'complete_root_mean': str(root_mean), 'complete_leaf_mean': str(leaf_mean),
        'root_atoms_below28': {str(i): str(root_atoms[i]) for i in range(1, MAX)},
        'curve': curve, 'Hleaf16': str(leaf16), 'Hleaf16_decimal': float(leaf16),
        'Hroot16': str(root16), 'Hroot16_decimal': float(root16),
        'G16': str(G16), 'G16_decimal': float(G16),
        'hinge_improvement16': str(old['oldH16']-root16),
        'hinge_improvement16_decimal': float(old['oldH16']-root16),
        'strict_improvement16': root16 < old['oldH16'],
        'positive_G16': G16 > 0,
        'best_permitted_integer': best,
        'closed_interval_upper': closed_best,
        'positive_some_permitted_threshold': F(best['G']) > 0,
        'all_real_permitted_thresholds_fail': F(closed_best['G']) <= 0,
        'interpolation': 'integer loads imply affine H/G on every [j,j+1]; '
                         'endpoint28 is included only to bound the final open interval',
        'scope': 'fixed candidate/C only; no optimized-kernel, full-cell, actual-covering, '
                 'or Lean conclusion; positivity not inferred from improvement alone',
        'active_patterns': len(pattern_rows), 'pattern_rows': pattern_rows,
        'finite_controls': finite_controls, 'checks': checks,
    }
    return result

def main():
    global checks
    base=Path(__file__).resolve().parent
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate',type=Path,default=base/'conditional_root_hinge_certificate.json')
    parser.add_argument('--source-certificate',type=Path,default=base/SOURCE_CERTIFICATE)
    parser.add_argument('--source-result',type=Path,default=base/SOURCE_RESULT)
    parser.add_argument('--result',type=Path,default=base/'conditional_root_hinge.json')
    parser.add_argument('--write-result',type=Path)
    args=parser.parse_args()
    cert=load_unique(args.certificate)
    need(cert['schema']=='e7-conditional-root-hinge-certificate-v1','certificate schema')
    need(cert['source_certificate']=={'file':SOURCE_CERTIFICATE,'sha256':EXPECTED_C},'source certificate binding')
    need(cert['source_result']=={'file':SOURCE_RESULT,'sha256':EXPECTED_R},'source result binding')
    need(tuple(cert['source_math_fields'])==MATH_FIELDS and cert['source_math_sha256']==MATH_SHA,
         'complete mathematical-field binding')
    need(cert['threshold_domain']=={'lower':0,'upper_exclusive':28,'closed_diagnostic_upper':28,
                                   'leaf_control':16,'nominal':16},'full fixed threshold contract')
    need(cert['ternary_roots']==[[4,7],[2,5,8]],'literal ternary roots')
    need(cert['normalization']=='nu_u restricted to U / nu_u(U)','certificate denominator')
    need(cert['source_point']=='C only' and cert['retained_positive_entries']==106,'one fixed candidate/source')
    c=load_unique(args.source_certificate,EXPECTED_C)
    source=load_unique(args.source_result,EXPECTED_R)
    need(set(c)==set(MATH_FIELDS)|{'schema'},'no unbound source certificate fields')
    semantic=json.dumps({k:c[k] for k in MATH_FIELDS},sort_keys=True,separators=(',',':')).encode()
    need(hashlib.sha256(semantic).hexdigest()==MATH_SHA,'all source mathematical fields unchanged')
    need(source['schema']=='e7-retained-factorial-hinge-result-v1'
         and source['certificate_sha256']==EXPECTED_C,'inherited result/certificate binding')
    previous=dict(source['fixed_candidate_C'])
    previous.update(normalization=source['normalization'],weights=source['weights'],
                    nonzero_u=source['nonzero_u'])
    controls=finite_controls()
    result=compute(c,previous,controls)
    result['certificate_sha256']=hashlib.sha256(args.certificate.read_bytes()).hexdigest()
    if args.write_result:
        args.write_result.write_text(json.dumps(result,indent=2)+'\n')
        action='generated'
    else:
        expected=load_unique(args.result)
        # Parsing the retained result is not arithmetic evidence; record the
        # computation's checks before this extra equality check.
        need(result==expected,'retained result mismatch')
        action='verified'
    print(json.dumps({'action':action,'arithmetic_checks':result['checks'],
                      'active_patterns':result['active_patterns'],
                      'Hroot16':result['Hroot16_decimal'],'G16':result['G16_decimal'],
                      'all_permitted_thresholds_fail':result['all_real_permitted_thresholds_fail']}))

if __name__=='__main__':
    main()
