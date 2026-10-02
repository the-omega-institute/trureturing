"""Pay the actual inverse-compression finite target; no RH conclusion.

The author scalar-moment containment is an explicit premise. Classical trial
proposal minimizes the source's residual quadratic for center A,B; directed
arithmetic checks its use and the complete finite sign independently of doubles.
"""
import argparse
import hashlib
import json
import importlib.metadata
import platform
import time
from pathlib import Path
import numpy as np
from flint import arb, arb_mat, ctx

parser = argparse.ArgumentParser()
parser.add_argument('--prime', type=Path, required=True)
parser.add_argument('--kernel', type=Path, required=True)
parser.add_argument('--manifest', type=Path, required=True)
parser.add_argument('--out', type=Path, required=True)
parser.add_argument('--bits', type=int, default=1536)
args = parser.parse_args()
manifest_bytes = args.manifest.read_bytes()
manifest = json.loads(manifest_bytes)
input_bytes = {'prime': args.prime.read_bytes(),
               'kernel': args.kernel.read_bytes(),
               'consumer': Path(__file__).read_bytes()}
if manifest['schema']!='ACTUAL_C9_RETAINED_INPUTS_V1':
    raise ValueError('Wrong scientific input manifest.')
actual_versions = {'python': platform.python_version(),
                   'python_flint': importlib.metadata.version('python-flint'),
                   'numpy': importlib.metadata.version('numpy')}
if manifest['arithmetic_versions']!=actual_versions:
    raise ValueError('Arithmetic runtime differs from admitted versions.')
for key, payload in input_bytes.items():
    if hashlib.sha256(payload).hexdigest() != manifest[key]['sha256']:
        raise ValueError(f'Unbound scientific input: {key}')
prime, kernel = json.loads(input_bytes['prime']), json.loads(input_bytes['kernel'])
canonical_basis='sqrt((4j+1)/(2log3))*P_(2j)(u/log3),j=0..size-1'
if prime['basis']!=canonical_basis or kernel['basis']!=canonical_basis:
    raise ValueError('Wrong canonical basis.')
if prime['cutoff']!=9 or kernel['cutoff']!=9 or prime['even_dimension']!=kernel['even_dimension']:
    raise ValueError('Mismatched retained embedding.')
if kernel['moment_source_sha256']!='f8cb5c681a22755b980d2e98d781353fe9ce058fe33eb8a7753585e2c52b2f93':
    raise ValueError('Wrong source moment identity.')
size = prime['even_dimension']
if size != 256:
    raise ValueError('The stated complement allowances require the256-mode space.')
ctx.prec = args.bits
started = time.monotonic()

def matrix(record):
    centers=record['integer_centers']
    if len(centers)!=size or any(len(row)!=size for row in centers):
        raise ValueError('Wrong actual matrix dimensions.')
    if any(not isinstance(value,int) for row in centers for value in row):
        raise ValueError('Noninteger rational centers.')
    if any(centers[i][j]!=centers[j][i] for i in range(size) for j in range(i)):
        raise ValueError('Non-Hermitian exact rational centers.')
    if record['common_denominator_power']!=512:
        raise ValueError('Unexpected source center grid.')
    return arb_mat([[arb(x)*arb(2)**(-record['common_denominator_power'])
                     for x in row] for row in record['integer_centers']])

A, B, J = matrix(prime['A']), matrix(prime['B']), matrix(kernel['J'])
if max(prime['A']['operator_error_upper_power_of_two'],prime['B']['operator_error_upper_power_of_two'])>-400:
    raise ValueError('Prime arithmetic input is not admitted.')
identity = arb_mat(size,size)
for i in range(size): identity[i,i] = 1
mu = arb(4)/5
# Proposal only. X is rounded to a fixed grid and then treated as exact.
proposal = (B-mu*A).solve(A-mu*identity)
integers=[]
for i in range(size):
    row=[]
    for j in range(size):
        mantissa, exponent = map(int,proposal[i,j].mid().man_exp())
        exponent+=256
        row.append(mantissa<<exponent if exponent>=0 else (mantissa+(1<<(-exponent-1)))>>(-exponent))
    integers.append(row)
X=arb_mat([[arb(x)*arb(2)**(-256) for x in row] for row in integers])
norm_square=sum(x*x for row in integers for x in row)
s=32
if norm_square > s*s*2**512:
    raise ValueError('Exact Frobenius trial bound failed.')
epsA=arb(2)**prime['A']['operator_error_upper_power_of_two']
epsB=arb(2)**prime['B']['operator_error_upper_power_of_two']
epsJ=arb(2)**(-205)  # Analytic2^-206 plus smaller directed matrix error.
if kernel['J']['arithmetic_operator_error_upper_power_of_two'] > -207:
    raise ValueError('Kernel arithmetic error too large for epsilonJ.')
deltaX=(s*s+2*s/mu)*epsA+(s*s/mu)*epsB
Xt=X.transpose()
W=X+Xt-Xt*A*X+(identity-A*X-Xt*A+Xt*B*X)/mu+deltaX*identity
D=B-A*A
epsD=epsB+(2*arb(2011)/325+epsA)*epsA
target=W.inv()+J-(epsJ+arb(2)**(-187)+arb(2)**(-186)*epsD)*identity-arb(2)**(-186)*D
print(json.dumps({'stage':'complete_error_paid_target','elapsed_seconds':time.monotonic()-started}),flush=True)
float_target=np.array([[float(target[i,j].mid()) for j in range(size)] for i in range(size)])
float_target=(float_target+float_target.T)/2
float_values,float_vectors=np.linalg.eigh(float_target)

# A directed test of a fixed rational vector is a valid negative witness for
# this sufficient finite target. Floating eigenvalues merely propose that vector.
if float_values[0]<0:
    v_int=[int(round(float(x)*2**48)) for x in float_vectors[:,0]]
    v=[arb(x)*arb(2)**(-48) for x in v_int]
    value=sum((v[i]*target[i,j]*v[j] for i in range(size) for j in range(size)),arb(0))
    witness={'integer_centers':v_int,'common_denominator_power':48,
             'quadratic_ball':value.str(50),'directed_negative':bool(value<0)}
else:
    witness=None

# Directed LDL on every pivot, including small finite-band eigenvalues.
current=[[target[i,j] for j in range(size)] for i in range(size)]
pivots=[]
minimum_pivot=None
complete_positive=True
for k in range(size):
    pivot=current[k][k]
    pivots.append(pivot.str(40))
    if not pivot>0:
        complete_positive=False
        break
    lower=pivot.lower()
    if minimum_pivot is None or lower<minimum_pivot:
        minimum_pivot=lower
    for i in range(k+1,size):
        factor=current[i][k]/pivot
        for j in range(i,size):
            current[j][i]-=current[j][k]*factor
            current[i][j]=current[j][i]
result={'cutoff':9,'even_dimension':size,'precision_bits':args.bits,
        'source_input_manifest_sha256':hashlib.sha256(manifest_bytes).hexdigest(),
        'arithmetic_versions':manifest['arithmetic_versions'],
        'moment_containment_premise':kernel['moment_containment_premise'],
        'trial_grid_bits':256,'trial_exact_frobenius_bound':s,
        'trial_exact_frobenius_squared_numerator':str(norm_square),
        'trial_exact_frobenius_squared_denominator_power':512,
        'trial_integer_centers':integers,
        'epsilonJ_upper_power_of_two':-205,
        'float_minimum_proposal_only':float(float_values[0]),
        'negative_sufficient_target_witness':witness,
        'directed_LDL_complete_positive':complete_positive,
        'directed_LDL_pivots_checked':len(pivots),
        'directed_LDL_last_pivot':pivots[-1],
        'directed_LDL_pivots':pivots,
        'directed_LDL_minimum_lower_bound':minimum_pivot.str(50) if minimum_pivot is not None else None,
        'elapsed_seconds':time.monotonic()-started,
        'scope':'Conditional numerical research of the specified sufficient comparison only. '
                'Source contract reviewed separately; this output attests no independent execution, '
                'moment containment, full-Weil positivity or RH proof.'}
args.out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['negative_sufficient_target_witness','directed_LDL_pivots','trial_integer_centers']}),flush=True)
if complete_positive and len(pivots)==256 and not (witness and witness['directed_negative']):
    raise SystemExit(0)
raise SystemExit(2)
