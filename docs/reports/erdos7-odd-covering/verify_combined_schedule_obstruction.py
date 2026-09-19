"""Check all integer 11/13/17/19/23 schedules for one SH27 feature bound.

The hash-bound adjacent saturated convex profile is a verified prerequisite.
This program verifies a finite obstruction for that numerical certificate,
not an obstruction for actual congruence families or other observations.
Only Python's standard library is required; all judging arithmetic is exact.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
import argparse
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import json
import time

PRIMES=(11,13,17,19,23)
CAP=22
SCALE=10**18

def require(condition,message):
    if not condition:raise ArithmeticError(message)

def ceildiv(a,b):return -((-a)//b)

def floor_scaled(x):return x.numerator*SCALE//x.denominator

def read_profile(source):
    raw=read_artifact_bytes(source);data=json.loads(raw)
    require(data['schema']==1,'known profile schema')
    mean,square=F(data['mean_nu_upper']),F(data['square_nu_upper'])
    hinges={int(k):F(v['nu_upper']) for k,v in data['hinges'].items()}
    hinges[2]=F(data['refined_hinge2']['nu_upper'])
    require(mean==2+hinges[2] and square>mean>2,'exact retained mean and square')
    require(set(hinges)=={2,3,4,5,6,8,10,12},'exact source hinge knots')
    hinges[1]=mean-1
    # Convex interpolation between stated knots, then monotonicity after12.
    for j in (7,9,11):hinges[j]=(hinges[j-1]+hinges[j+1])/2
    for j in range(13,CAP):hinges[j]=hinges[12]
    require(all(h>=max(F(0),mean-j) for j,h in hinges.items()),
            'nonnegative charge correction and consistent affine baseline')
    return data,sha256(raw).hexdigest(),mean,square,hinges

def tables(mean,hinges):
    result={}
    for p in PRIMES:
        choices=[]
        for threshold in range(1,p-1):
            d=p-1-threshold;cap=F(p-1,d);a=F(3*p-1,(p-1)**2);k=1+a*cap
            require(d>=1 and cap<=p,'admissible full-history AP kernel')
            corrections=[F(0)]*CAP;intercepts=[F(0)]*CAP
            for n in range(1,threshold):
                lo=threshold//n;hi=(threshold+n-1)//n;t=F(threshold,n)
                ht=hinges[lo] if lo==hi else (hi-t)*hinges[lo]+(t-lo)*hinges[hi]
                corrections[n]=n*ht-n*mean+threshold
                require(corrections[n]>=0,'nonnegative exact profile correction')
                def cost0(j):
                    return a*(F(p-1,p-1-min(n*j,threshold))-cap)
                values={j:cost0(j) for j in range(1,hi+2)}
                intercepts[n]=values[1]+(values[2]-values[1])*(mean-1)
                intercepts[n]+=sum((values[j+1]-2*values[j]+values[j-1])*hinges[j]
                                   for j in range(2,hi+1))
            probabilities={1:1-cap/p,**{n:cap*(p-1)/p**n for n in range(2,CAP)}}
            require(all(v>=0 for v in probabilities.values()),'valid low auxiliary probabilities')
            choices.append({'T':threshold,'d':d,'k':k,'corrections':corrections,
                            'intercepts':intercepts,'correction_lower':list(map(floor_scaled,corrections)),
                            'intercept_lower':list(map(floor_scaled,intercepts)),
                            'probabilities':probabilities})
        result[p]=choices
    return result

def exact_calibration(pre,mean,square,data):
    probabilities={1:F(1)};fullmean=F(1);charge=F(0);corrected=square;standard=square
    for p,threshold in ((11,4),(13,5)):
        row=pre[p][threshold-1];d=row['d'];k=row['k']
        charge+=(mean*fullmean-threshold+
                 sum(v*row['corrections'][n] for n,v in probabilities.items() if n<threshold))/d
        correction=sum(v*row['intercepts'][n] for n,v in probabilities.items() if n<threshold)
        corrected=k*corrected+correction;standard*=k
        new={}
        for n,v in probabilities.items():
            for m,pr in row['probabilities'].items():
                if n*m<CAP:new[n*m]=new.get(n*m,F(0))+v*pr
        probabilities=new;fullmean*=1+F(1,d)
    expected=data['combined_prime_cost']
    require(charge==F(expected['affine_slope']),'same published SH29 charge functional')
    require(corrected-standard==F(expected['affine_intercept']),
            'same published SH29 combined intercept functional')
    return {'charge':str(charge),'combined_intercept':str(corrected-standard)}

def compute(source, *, additional_hinges=None):
    data,source_hash,mean,square,hinges=read_profile(source)
    if additional_hinges is not None:
        require(set(additional_hinges)==set(range(13,22)),'exact additional hinge domain')
        for t,h in additional_hinges.items():
            require(0<=h<=hinges[t],'additional observation improves the same feature')
            hinges[t]=h
    pre=tables(mean,hinges);calibration=exact_calibration(pre,mean,square,data)
    divisors={n:[a for a in range(1,n+1) if n%a==0] for n in range(1,CAP)}
    mean_lower=floor_scaled(mean);counts=[0]*len(PRIMES)
    leaves=0;min_charge=None;min_constant=None;arg_charge=None;arg_constant=None

    def visit(index,charge_lower,corrected_lower,fullmean_lower,prob_lower,prob_upper,schedule):
        nonlocal leaves,min_charge,min_constant,arg_charge,arg_constant
        p=PRIMES[index]
        for row in pre[p]:
            threshold,d,k=row['T'],row['d'],row['k'];counts[index]+=1
            rr,vv=row['correction_lower'],row['intercept_lower']
            numerator=mean_lower*fullmean_lower//SCALE-threshold*SCALE
            numerator+=sum(prob_lower[n]*rr[n]//SCALE for n in range(1,threshold))
            # The exact charge is nonnegative; max(0,lower) remains a lower bound.
            next_charge=charge_lower+max(0,numerator//d)
            # Negative intercept coefficients require UPPER probability bounds.
            correction=sum((prob_upper[n] if vv[n]<0 else prob_lower[n])*vv[n]//SCALE
                           for n in range(1,threshold))
            next_corrected=corrected_lower*k.numerator//k.denominator+correction
            next_schedule=schedule+[threshold]
            if index==len(PRIMES)-1:
                leaves+=1;constant=next_corrected-SCALE
                if min_charge is None or next_charge<min_charge:
                    min_charge=next_charge;arg_charge=next_schedule
                if min_constant is None or constant<min_constant:
                    min_constant=constant;arg_constant=next_schedule
                continue
            next_lower=[0]*CAP;next_upper=[0]*CAP
            for n in range(1,CAP):
                for m in divisors[n]:
                    z=row['probabilities'][n//m]
                    next_lower[n]+=prob_lower[m]*z.numerator//z.denominator
                    next_upper[n]+=ceildiv(prob_upper[m]*z.numerator,z.denominator)
            visit(index+1,next_charge,next_corrected,fullmean_lower*(d+1)//d,
                  next_lower,next_upper,next_schedule)

    initial=[0]*CAP;initial[1]=SCALE
    visit(0,0,floor_scaled(square),SCALE,initial,initial,[])
    require(counts==[9,99,1485,25245,530145] and leaves==530145,
            'all and only the specified integer schedules')
    require(min_charge>103*SCALE//100 and min_constant>101*SCALE,
            'strict positive barrier for every terminal certificate')
    return {'schema':1,'scope':'SH27 discrete-hinge feature functional; every integer threshold schedule through23',
            'profile_certificate_sha256':source_hash,'grid_scale':SCALE,
            'primes':list(PRIMES),'threshold_domain':'1 <= T_p <= p-2',
            'initial_mean':str(mean),'initial_square':str(square),
            'integer_hinges':{str(k):str(v) for k,v in sorted(hinges.items())},
            'published_two_step_calibration':calibration,'prefix_counts':counts,'schedule_count':leaves,
            'minimum_charge_coefficient_lower':str(F(min_charge,SCALE)),
            'minimum_affine_constant_lower':str(F(min_constant,SCALE)),
            'argmin_charge_grid_bound':arg_charge,'argmin_constant_grid_bound':arg_constant,
            'uniform_barrier':'cert(W)-W > 101+(3/100)W > 0 for every W>0'}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source',type=Path,default=(Path(__file__).resolve().parent / 'certificates/saturated_convex_profile_certificate.json'))
    parser.add_argument('--certificate',type=Path,default=(Path(__file__).resolve().parent / 'certificates/combined_schedule_obstruction_certificate.json'))
    parser.add_argument('--write-certificate',action='store_true')
    args=parser.parse_args();start=time.perf_counter()
    if not args.write_certificate:
        expected=json.loads(read_artifact_text(args.certificate))
        require(sha256(read_artifact_bytes(args.source)).hexdigest()==expected['profile_certificate_sha256'],
                'exact same-law prerequisite source hash')
    result=compute(args.source)
    if args.write_certificate:write_certificate_text(args.certificate, json.dumps(result,indent=2)+'\n')
    else:require(result==expected,'all recomputed obstruction certificate fields')
    print(json.dumps({'schedule_count':result['schedule_count'],
                      'minimum_charge_coefficient_lower':result['minimum_charge_coefficient_lower'],
                      'minimum_affine_constant_lower':result['minimum_affine_constant_lower'],
                      'uniform_barrier':result['uniform_barrier'],'seconds':time.perf_counter()-start}))

if __name__=='__main__':main()
