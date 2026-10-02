"""Four predeclared source/digit limits and one q=11,N=2 exact control.

No producer main, old finite-control suite, parameter search or continuation.
Explicit source files and output path; no directory traversal.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
from math import prod
from pathlib import Path
import json
import runpy
import time

parser = argparse.ArgumentParser(description=__doc__)
for name in ('arithmetic-library', 'first-source', 'second-source', 'output'):
    parser.add_argument('--'+name, type=Path, required=True)
args = parser.parse_args()
LIBRARY = args.arithmetic_library
INPUTS = [('FC110', args.first_source), ('FC131', args.second_source)]
OUTPUT = args.output
lib = runpy.run_path(str(LIBRARY), run_name='batch127_head_mass_definitions')
Q = lib['PRIVATE']
P = lib['PRIMES']
HEADS = lib['HEADS']
ROOTS = lib['ROOTS']
checks = 0


def require(ok, message):
    global checks
    checks += 1
    if not ok:
        raise ValueError(message)


def mul(values):
    return prod(values, start=F(1))


def private_formula(digit, root, i, j, A):
    q = 11
    c, tail = 1/(1-A), A-F(1,q)
    b, t = c*A, c*tail
    active = int(root == 2)
    g = 1-active*b
    if digit == 1:
        f = b if root == 1 else t
        Z = F(0)
    elif digit == 6:
        f = c*(F(1,q)-(1+active)*tail)
        Z = int(i == 2)*(1+active)*int(j == 3)*t
    else:
        raise ValueError('Only the two predeclared digits are admitted')
    X = int(i == 2)*f + active*int(i == 0)*b
    Y = (1+active)*int(j == 3)*b
    H = g-X-Y+Z
    return g,X,Y,Z,H


def fixed_finite_control():
    q,n = 11,2
    modulus = q**n
    carrier = set(range(modulus))
    def cylinder(word):
        residue = sum(d*q**k for k,d in enumerate(word))
        return {x for x in carrier if x % q**len(word) == residue}
    roles = {j:cylinder((j,)) | cylinder((6,j)) for j in range(6)}
    pure_free = carrier-roles[0]
    denominator = len(pure_free)
    A = F(1,q)+F(1,q*q)
    require(F(denominator,modulus) == 1-A, 'Literal pure normalization')
    cases = 0
    for digit in (1,6):
        actual_free5 = cylinder((digit,)) | cylinder((6,2))
        for root in ROOTS:
            remaining = pure_free-(roles[1] if root == 2 else set())
            for i,j in product(range(5),range(7)):
                group5 = (actual_free5 if i == 2 else set()) | (
                    roles[4] if root == 2 and i == 0 else set())
                group7 = (roles[3] if j == 3 else set()) | (
                    roles[5] if root == 2 and j == 3 else set())
                left,right = remaining & group5, remaining & group7
                actual = tuple(F(len(s),denominator) for s in (
                    remaining,left,right,left & right,remaining-(group5 | group7)))
                predicted = private_formula(digit,root,i,j,A)
                require(actual == predicted, 'All five raw actual event masses match at fixed N=2')
                cases += 1
    return {'q':q,'N':n,'modulus':modulus,'pure_carrier_size':denominator,
            'root_head_digit_cells':cases,'source_dependence':'Both sources have identical q11 addresses and roots.'}


def evaluate_case(name,digit,c,b,w,old_arrays,g):
    full = (1 << len(Q))-1
    raw = {r:{p:[[g[r][q]*old_arrays[r][p][k][i] for i in range(p)]
                 for k,q in enumerate(Q)] for p in HEADS} for r in ROOTS}
    intersection = {r:[[F(0) for _ in range(7)] for _ in range(5)] for r in ROOTS}
    local = {}
    for r in ROOTS:
        local[r] = []
        for i,j in product(range(5),range(7)):
            gq,X,Y,Z,H = private_formula(digit,r,i,j,F(1,10))
            require(gq == g[r][11], 'Private star carrier unchanged')
            raw[r][5][0][i] = X
            raw[r][7][0][j] = Y
            intersection[r][i][j] = Z
            require(0 <= X <= gq and 0 <= Y <= gq and 0 <= Z <= min(X,Y), 'Actual raw subset guards')
            require(0 <= max(F(0),gq-X-Y) <= H <= gq-max(X,Y), 'Literal intersection sandwich')
            local[r].append({'i5':i,'i7':j,'g':gq,'X':X,'Y':Y,'Z':Z,'H':H})
    matrices = {}
    lower_roots,actual_roots = {},{}
    for r in ROOTS:
        factors = [[[g[r][q]-max(raw[r][5][k][i],raw[r][7][k][j])
                     for j in range(7)] for i in range(5)] for k,q in enumerate(Q)]
        matrices[r] = [[[F(1) for _ in range(7)] for _ in range(5)]]
        for mask in range(1,full+1):
            bit = mask & -mask
            k = bit.bit_length()-1
            before = mask ^ bit
            matrices[r].append([[matrices[r][before][i][j]*factors[k][i][j]
                                for j in range(7)] for i in range(5)])
        def residual(use_actual):
            return sum((w[r][5][i]*w[r][7][j]*mul(
                (g[r][q]-raw[r][5][k][i]-raw[r][7][k][j]+intersection[r][i][j]
                 if use_actual and q == 11 else
                 max(F(0),g[r][q]-raw[r][5][k][i]-raw[r][7][k][j]))
                for k,q in enumerate(Q)) for i,j in product(range(5),range(7))),F(0))
        lower_roots[r],actual_roots[r] = residual(False),residual(True)
        require(lower_roots[r] <= actual_roots[r], 'True same-source group survivor contains lower comparison')
    free,selected = F(0),F(0)
    support_count = 0
    buckets = {}
    for size in range(2,len(P)+1):
        for support in combinations(P,size):
            fixed = tuple(p for p in HEADS if p in support)
            inside = sum(1 << k for k,q in enumerate(Q) if q in support)
            outside = full ^ inside
            lower = {p:2 if size == 2 and len(fixed) == 1 else 1 for p in fixed}
            private_factor = mul(b[q] for q in Q if q in support)
            table = {}
            for address in product(*(range(p) for p in fixed)):
                row = dict(zip(fixed,address))
                T = {}
                for r in ROOTS:
                    T[r] = sum(((F(1) if 5 in fixed else w[r][5][i])*
                                (F(1) if 7 in fixed else w[r][7][j])*
                                matrices[r][outside][i][j]
                                for i in ([row[5]] if 5 in fixed else range(5))
                                for j in ([row[7]] if 7 in fixed else range(7))),F(0))
                    require(T[r] >= 0, 'Nonnegative same-source raw unsupported-coordinate kernel')
                table[address] = T
            f,s = lib['supported_head_sum'](fixed,table,lower,c,w)
            f,s = private_factor*f,private_factor*s
            free += f
            selected += s
            key = ','.join(map(str,fixed)) or 'none'
            bucket = buckets.setdefault(key,{'supports':0,'free':F(0),'selected':F(0)})
            bucket['supports'] += 1
            bucket['free'] += f
            bucket['selected'] += s
            support_count += 1
    require(support_count == 2036, 'Exact complete FC159 nongroup support inventory')
    Araw,Atrue = sum(lower_roots.values())/2,sum(actual_roots.values())/2
    J = Araw-free-selected
    return {'source':name,'changed_digit':digit,'gamma':F(1,2),
            'raw_q11_cells':local,'raw_group_lower_roots':lower_roots,
            'actual_group_survivor_roots':actual_roots,
            'weighted_group_lower':Araw,'weighted_actual_group_survivor':Atrue,
            'free_min_cap_fee':free,'selected_min_cap_fee':selected,
            'native_J':J,'native_J_decimal':float(J),'native_J_positive':J>0,
            'actual_residual_minus_same_fee':Atrue-free-selected,
            'support_count':support_count,'by_supported_heads':buckets,
            'head_depth_thresholds':{p:lib['threshold'](p,1,c,w) for p in HEADS}}


started = time.monotonic()
control = fixed_finite_control()
cases = []
provenance = {LIBRARY.name:sha256(LIBRARY.read_bytes()).hexdigest()}
source_checks = 0
for name,path in INPUTS:
    baseline = lib['Checks']()
    data,schema,c,b,w,arrays,g,digest = lib['read_witness'](path,baseline)
    source_checks += baseline.count
    provenance[path.name] = digest
    require(data['private_sources']['11']['5']['free'][2] == '1/9', 'Declared q11 free5 head row2')
    for r in ROOTS:
        require([g[r][11]*x for x in arrays[r][5][0]] ==
                [F(int(r == 2 and i == 0)+int(i == 2),9) for i in range(5)],
                'q11 selected5 root2 row0 in both sources')
        require([g[r][11]*x for x in arrays[r][7][0]] ==
                [F((1+int(r == 2))*int(j == 3),9) for j in range(7)],
                'q11 free7 and root2 selected7 share row3 in both sources')
    for digit in (1,6):
        case = evaluate_case(name,digit,c,b,w,arrays,g)
        cases.append(case)
        print(json.dumps({k:case[k] for k in ('source','changed_digit','native_J_decimal','native_J_positive')}),flush=True)

def serialize(x):
    if isinstance(x,F): return str(x)
    if isinstance(x,dict): return {str(k):serialize(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)): return [serialize(v) for v in x]
    return x

result = {'contract':'Only q11 free5 depth-one digit2 is replaced by1 or6, for each fixed FC110/FC131 source. All other phases and the exact FC159 inventory stay fixed. Native raw min-cap J, gamma=1/2, fixed limiting pure caps; no continuation or universal bad-phase conclusion.',
          'finite_control':control,'cases':cases,'checks':checks,'source_schema_checks':source_checks,
          'input_provenance':provenance,'elapsed_seconds':time.monotonic()-started,
          'scope':['Four fixed limits only; no parameter, prime, order or clipping sweep.',
                   'Depth tails use the existing exact supported_head_sum definitions, not truncation.',
                   'No dependency main, prior finite-control suite, Lean or continuation is executed.',
                   'Hashes are provenance, never admission or cache gates.']}
OUTPUT.write_text(json.dumps(serialize(result),indent=2,sort_keys=True)+'\n')
print(json.dumps({'checks':checks,'source_schema_checks':source_checks,'elapsed_seconds':result['elapsed_seconds'],'output':str(OUTPUT)}),flush=True)
