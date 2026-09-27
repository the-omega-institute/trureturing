#!/usr/bin/env python3
"""Fixed conditional Gibbs-mixture budget from retained alpha and tau only.
No smooth-label enumeration, original producer, or parameter search.
"""
from fractions import Fraction as F
from decimal import Decimal,localcontext
from math import factorial
from pathlib import Path
import argparse
import hashlib,json
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--input',type=Path,default=Path(__file__).with_name('phase_resampling_arithmetic.json'))
parser.add_argument('--output',type=Path)
args=parser.parse_args()
src=args.input
try:
 raw=src.read_bytes()
except OSError as error:
 parser.error(str(error))
source_hash=hashlib.sha256(raw).hexdigest()
if source_hash!='da1e922b5745ede67d601c3780043f6d97aa8ee1bf64944479c58b2113f9d10f':
 parser.error('input must be the pinned phase-resampling arithmetic data')
data=json.loads(raw);alpha=F(data['alpha']);tau=F(data['tail']);Lam=1/alpha
eps=F(1,10**7);R0=F(70871,3375);x=F(6732875,10**6);target=F(6737023,10**6)
S50=sum((x**j/F(factorial(j)) for j in range(51)),F(0))
unmixed=x+Lam*tau
mixed=(1-eps)*x+eps*R0+Lam*tau
checks={
 'positive_alpha':alpha>0,
 'nonnegative_tau':tau>=0,
 'fixed_log_Taylor_certificate':alpha*S50>1,
 'unmixed_upper_below_target':unmixed<target,
 'mixed_upper_below_target':mixed<target,
 'mixed_upper_below_6_737016':mixed<F(842127,125000),
 'mixture_has_positive_weights':0<eps<1,
 'retained_lower_density_coefficient':eps/F(5)==F(1,50000000),
}
if not all(checks.values()):raise ValueError(checks)
with localcontext() as ctx:
 ctx.prec=70
 def dec(v):return Decimal(v.numerator)/Decimal(v.denominator)
 log=dec(Lam).ln()
 out={
 'source_sha256':source_hash,
 'scope':'Arithmetic consequences of the stated Gibbs-law and report467 premises; not Lean verification',
 'alpha':str(alpha),'tau':str(tau),'Lambda':str(Lam),'epsilon':str(eps),'reference_total_query_upper':str(R0),
 'log_upper_x':str(x),'log_Taylor_degree':50,'target':str(target),
 'Lambda_times_tau':str(Lam*tau),'unmixed_rational_upper':str(unmixed),'mixed_rational_upper':str(mixed),
 'unmixed_rational_margin':str(target-unmixed),'mixed_rational_margin':str(target-mixed),
 'extra_mixing_cost_in_rational_upper':str(mixed-unmixed),'mixed_lower_density_coefficient':str(eps/F(5)),
 'log_Lambda_decimal':str(log),'Lambda_tau_decimal':str(dec(Lam*tau)),
 'unmixed_value_decimal':str(log+dec(Lam*tau)),
 'mixed_value_decimal':str((1-dec(eps))*log+dec(eps)*dec(R0)+dec(Lam*tau)),
 'unmixed_upper_decimal':str(dec(unmixed)),'mixed_upper_decimal':str(dec(mixed)),
 'unmixed_rational_margin_decimal':str(dec(target-unmixed)),
 'mixed_rational_margin_decimal':str(dec(target-mixed)),
 'checks':checks,
 }
content=json.dumps(out,indent=2)+'\n'
if args.output is None:
 print(content,end='')
else:
 args.output.write_text(content,encoding='utf-8')
