"""Directed exact lower bounds for the auxiliary profile-neighborhood budget."""
from fractions import Fraction as F
from hashlib import sha256
from math import isqrt,prod
from pathlib import Path
import importlib.util
import sys
sys.dont_write_bytecode=True
_spec=importlib.util.spec_from_file_location('transport_io',Path(__file__).with_name('adaptive_phase_io.py'))
_io=importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_io)
require=_io.require

CERTIFICATE='certificates/source_norms/source-budgets/profile_auxiliary_transport.json'
SOURCES=('certificate_io.py', 'frontier/source-budgets/adaptive_phase_io.py', 'problem-details/61-coordinate-retention-and-profile-neighborhood-obstruction.md', 'problem-details/60-positive-cylinder-covers-across-head-profiles.md', 'frontier/source-budgets/uniform_phase_capacity_input.json', 'certificates/source_norms/source-budgets/positive_cylinder_polynomial.json', 'frontier/source-budgets/positive_cylinder_polynomial.py')

def calculate(base):
    ctx=_io.Context(base,SOURCES,__file__)
    INPUT='frontier/source-budgets/uniform_phase_capacity_input.json'
    D=ctx.read(INPUT)
    require(sha256(ctx.raw(INPUT)).hexdigest()=='ea227d216660f496ecb3a2c89dbc145605f0ad83c94e5996a7ee76d746ea712b','same complete actual seven-phase input')
    polynomial=ctx.fresh('certificates/source_norms/source-budgets/positive_cylinder_polynomial.json','frontier/source-budgets/positive_cylinder_polynomial.py')
    P=D['prime_order'];H=D['heights'];R=[[F(x) for x in row] for row in D['profiles']]
    require(len(P)==len(H)==len(R)==20,'all twenty coordinates')
    B=16384;CAP=(2*B+1)//5;SCALE=10**15;primes=[p for p in range(2,B+1) if all(p%d for d in range(2,isqrt(p)+1))]
    def low(f):return f.numerator*SCALE//f.denominator
    def multiply(value,f):return value*f.numerator//f.denominator
    def convolution(weights,atoms):
     out=[0]*(CAP+1)
     for f,a in atoms:
      for d in range(1,CAP//f+1):out[d*f]+=weights[d]*a//SCALE
     return out
    weights=[0]*(CAP+1);weights[1]=SCALE;mean=second=SCALE
    for p,h,r in zip(P,H,R):
     atoms=[(f,low(r[f-1]-r[f])) for f in range(1,h+1)]
     for f in range(h+1,CAP+1):
      a=low(r[h]*F(p-1,p**(f-h)))
      if not a:break
      atoms.append((f,a))
     weights=convolution(weights,atoms)
     first=1+sum(r[1:],F(0))+r[h]/(p-1)
     square=1+sum(((2*e+1)*r[e] for e in range(1,h+1)),F(0))+r[h]*(F(2*h+1,p-1)+F(2*p,(p-1)**2))
     mean=multiply(mean,first);second=multiply(second,square)
    charge=0;steps=[]
    for q in primes:
     if q<=73:continue
     cutoff=(2*q+1)//5
     numerator=5*mean-(2*q+1)*SCALE+sum((2*q+1-5*d)*weights[d] for d in range(1,cutoff+1))
     step=max(0,numerator//(3*(q-2)));charge+=step;steps.append([q,step,charge])
     c=F(5*(q-1),3*(q-2));atoms=[(1,low(1-c/q))]
     for f in range(2,CAP+1):
      a=low(c*F(q-1,q**f))
      if not a:break
      atoms.append((f,a))
     weights=convolution(weights,atoms)
     mean=multiply(mean,1+c/(q-1));second=multiply(second,1+c*F(3*q-1,(q-1)**2))
    C=F(charge,SCALE);J=F(second,SCALE);T=F(326059,4);h=F(1,50000);U=F(696181396681816852739454137354543,1086338369123261718750000000000000)
    lower=(1-h)**20*(C+(J-1)/(T-1));upper=(1+h)**12*U;gap=lower-upper
    if gap<=0:raise ValueError(('box inequality did not pass',str(gap)))
    require(U==F(polynomial['balanced_value']) and max(t['coordinate_mask'].bit_count() for t in polynomial['terms'])==12,'same fixed polynomial value and degree')
    require(gap>F(1329,2000000),'strict relative-box excess greater than0.0006645')
    out={'schema':'fixed-continuation-profile-neighborhood-lower-v1','scope':'Lower bounds on exact independent auxiliary C,J. Every finite nonroot depth cap of all20 head coordinates may vary in its relative box, with geometric higher-digit lift and fixed delta2/5,B,T. This is not a lower bound on actual tail losses.','B':B,'T':str(T),'scale':SCALE,'stages':steps,'C_lower':str(C),'J_lower':str(J),'h':str(h),'head_coordinates':20,'polynomial_degree_bound':12,'base_survivor_upper':str(U),'new_auxiliary_B_lower':str(lower),'new_survivor_upper':str(upper),'score_excess_lower':str(gap),'score_excess_lower_decimal':float(gap)}
    return ctx.finish(out)


if __name__=="__main__":
    _io.run(CERTIFICATE,calculate,__file__)
