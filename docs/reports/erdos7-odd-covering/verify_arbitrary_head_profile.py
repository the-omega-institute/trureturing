#!/usr/bin/env python3
"""Exact PP1--PP6 constants for one actual generic pure-base continuation."""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from collections import defaultdict
from fractions import Fraction as F
from pathlib import Path
import argparse
from hashlib import sha256
import json

HERE = Path(__file__).resolve().parent

def require(value, message):
    if not value:
        raise ArithmeticError(message)

def encode(x):
    if isinstance(x,F): return str(x)
    if isinstance(x,dict): return {str(k):encode(v) for k,v in x.items()}
    if isinstance(x,(tuple,list)): return [encode(v) for v in x]
    return x

def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate certificate key: '+key)
        result[key] = value
    return result

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('certificate', nargs='?', type=Path,
                    default=HERE/'certificates/arbitrary_head_profile_certificate.json')
parser.add_argument('--source-directory', type=Path, default=HERE)
parser.add_argument('--write', action='store_true')
args = parser.parse_args()
pins = {
    'certificates/uniform_gamma_cofactor_certificate.json': 'bc8dd94c2471cb6ae97479c241553183b2585774a2ba09291eb267a612d05c6c',
    'certificates/star_block_obstruction_certificate.json': 'a378fed7d44cb1dd77fa81b9d9888cc248014011bf8a25aafeeceab8166a1907',
    'certificates/joint_density_certificate.json': 'de89179f6a15e78501c7568f3df125c3af53cb9d176066e6937eca9932878b9c',
}
source = {}
for filename, digest in pins.items():
    raw = read_artifact_bytes(args.source_directory/filename)
    require(sha256(raw).hexdigest() == digest, 'source SHA-256: '+filename)
    source[filename] = json.loads(raw, object_pairs_hook=unique)
G = F(source['certificates/uniform_gamma_cofactor_certificate.json']['signed_two_level_three_prime_parameters']['Gamma357_upper'])
R = F(source['certificates/joint_density_certificate.json']['improved_R_bound'])
D0 = 1/F(source['certificates/star_block_obstruction_certificate.json']['cm1_actual_head_sharpness']['infimum_ambient_uncovered_density'])
require((G,R,D0) == (F(3849,106),F(1649,360),F(432,53)), 'same uniform357 law source constants')
M=1+R
dist={1:F(1)}
for p in (3,5,7):
    new=defaultdict(F)
    for n,w in dist.items():
        for v in range(1,13//n+1):
            new[n*v]+=w*F(p-1,p**v)
    dist=dict(new)
haar_mean=F(35,16)
haar_hinges={h:D0*(haar_mean-h+sum((h-n)*w for n,w in dist.items() if n<h)) for h in range(1,13)}
profile={0:M,1:R,2:(G-1+17*R)/30,3:(G-1+2*R)/15}
profile.update({h:haar_hinges[h] for h in range(4,13)})
require(profile[2]==F(2159489,572400) and profile[3]==F(424267,143100),'mean/square integer hinges')
require(profile[4]==F(4733643,2272375) and profile[6]==F(8571397321,8350978125),'full Haar hinge values')
for L in range(1,1001):
    require(max(0,L-2)<=F(L*L+17*L-18,30),'first integer-majorant fixture')
    require(max(0,L-3)<=F(L*L+2*L-3,15),'second integer-majorant fixture')

def H(t):
    if t<=1: return M-t
    n=t.numerator//t.denominator
    if t==n: return profile[n]
    return (n+1-t)*profile[n]+(t-n)*profile[n+1]

def evaluate(T11,T13):
    d11,d13=10-T11,12-T13
    c11,c13=10/d11,12/d13
    require(d11>0 and d13>0 and c11<=11 and c13<=13,'auxiliary law admissibility')
    b11=H(T11)/d11
    cutoff=T13.numerator//T13.denominator
    cost=F(0);mass=F(0);mean=F(0)
    for n in range(1,cutoff+1):
        pn=1-c11/11 if n==1 else c11*10/F(11**n)
        mass+=pn;mean+=pn*n
        cost+=pn*n*H(T13/n)
    tail_mass=c11/F(11**cutoff)
    tail_mean=tail_mass*(cutoff+1+F(1,10))
    require(mass+tail_mass==1 and mean+tail_mean==1+c11/10,'full multiplier mass and first moment')
    cost+=M*tail_mean-T13*tail_mass
    b13=cost/d13
    rho=1-b11-b13
    J=G*(1+F(32,100)*c11)*(1+F(38,144)*c13)
    out=dict(T11=T11,T13=T13,c11=c11,c13=c13,b11=b11,b13=b13,
             survival_lower=rho,physical_square=J,positive_survival_bound=rho>0)
    if rho>0:
        out['supported_square']=1+(J-1)/rho
        out['supported_Haar_density']=D0*c11*c13/rho
    return out

chosen=evaluate(F(4),F(6))
rho=chosen['survival_lower'];f=chosen['supported_square']
require(rho==F(171474522380088889,498009616542900000),'chosen actual normalizer')
require(f==F(42035473165849976389,171474522380088889)<256,'chosen supported seed below256')
closed_b13=(F(28,33)*profile[6]+F(100,363)*profile[3]+F(19300,483153)*profile[2]+F(887,322102)*R+F(1,966306))/6
require(chosen['b13']==closed_b13,'independent closed13 charge formula')
K0=F(598121,53)
Kphysical=K0*F(1664,375)*F(1843,432)
Kfinal=1+(Kphysical-1)/rho
require(Kphysical==F(114643048312,536625),'pure-base quartic multipliers')
require(Kfinal==F(106393040395571160497689,171474522380088889),'chosen law fourth moment')
s17=1-f/256
J17=F(89,64)*f
G17=1+(J17-1)/s17
require(s17==F(1862004563452779195,43897477729302755584)>0,'actual17 survival')
require(G17==F(2984518594775348323619,372400912690555839),'supported17 unit-floor result')

rows=[evaluate(a,b) for a in list(map(F,range(1,10)))+[F(100,11)]
                    for b in list(map(F,range(1,12)))+[F(144,13)]]
positive=[r for r in rows if r['positive_survival_bound']]
best=min(positive,key=lambda r:r['supported_square'])
require(len(rows)==120 and best['T11']==4 and best['T13']==6,'endpoint certificate search')
result=dict(
    schema='erdos7-arbitrary-head-profile-v1',
    source_sha256=pins,
    scope='Actual generic uniform357 source; pure-base AP11/13 kernels at thresholds4,6; one final conditioning. All original heights/residues retained. Ordinary proof, not Lean or global actual-law optimality.',
    source_inputs=dict(G=G,R=R,D0=D0,mean_bound=M),
    truncated_product_distribution=dist,full_product_mean=haar_mean,
    Haar_hinge_bounds=haar_hinges,integer_profile=profile,
    selected_actual_law=chosen,
    initial_fourth=K0,physical_fourth13=Kphysical,supported_fourth13=Kfinal,
    next17=dict(kernel='full-Haar T4, delta=1/2, from supported13 law',
                assigned_bad_upper=f/256,actual_survival_lower=s17,
                physical_square=J17,supported_square=G17),
    integer_majorant_fixture_count=1000,
    endpoint_search=dict(count=len(rows),positive_count=len(positive),
                         best_thresholds=[F(4),F(6)],rows=rows))
result = encode(result)
if args.write:
    write_certificate_text(args.certificate, json.dumps(result,indent=2)+'\n')
else:
    require(json.loads(read_artifact_text(args.certificate),object_pairs_hook=unique) == result,
            'entire certificate equals exact recomputation')
print('PASS pure-base(4,6): G13=',f,'; rho=',rho,'; G17=',G17,';',len(rows),'endpoint certificates')
