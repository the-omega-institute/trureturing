"""Exact standard-library checks for the saturated all-height transfer.
The universal inequalities are proved in marked_head_profile.md (SH1-SH13);
finite CRT checks do not
replace their all-height argument. No independence of original forbidden
and test classes is assumed.
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
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import argparse
import json
P=(3,5,7);h=(2,1,1);base=315;delta0=F(53,432)
subsets=tuple(range(8))
def require(p,msg):
 if not p:raise ArithmeticError(msg)
def mul(xs):
 out=1
 for x in xs:out*=x
 return out
def epow(aa):return mul(p**a for p,a in zip(P,aa))
low_exps=list(product(*(range(a+1) for a in h)));low=[epow(a) for a in low_exps]
exps=dict(zip(low,low_exps))
DJ={j:[d for d,a in zip(low,low_exps) if all(a[i]==h[i] for i in range(3) if j>>i&1)] for j in subsets}
require([len(DJ[j]) for j in [1,2,4,3,5,6,7]]==[4,6,6,2,2,3,1],'seven saturated label counts')
alpha=[F(1,p-1) for p in P];beta=[F(p+1,(p-1)**2) for p in P]
def coeff(j,k,al=alpha,be=beta):
 return mul(be[i] if (j>>i&1 and k>>i&1) else al[i] if ((j^k)>>i&1) else F(1) for i in range(3))
K=[[coeff(j,k) for k in subsets] for j in subsets]
aJ=[coeff(0,j) for j in subsets]
heightchecks=[]
for heights in [(0,0,0),(1,0,0),(0,1,1),(1,1,1),(2,2,2),(3,2,1)]:
 al=[sum((F(1,p**e) for e in range(1,n+1)),F(0)) for p,n in zip(P,heights)]
 be=[sum((F(1,p**max(e,f)) for e in range(1,n+1) for f in range(1,n+1)),F(0)) for p,n in zip(P,heights)]
 for p,n,x,y in zip(P,heights,al,be):
  require(x==F(1,p-1)*(1-F(1,p**n)),'finite alpha closed form')
  require(y==sum((F(2*e-1,p**e) for e in range(1,n+1)),F(0)),'finite beta maximum count')
 active={j:list(product(*(range(1,heights[i]+1) if j>>i&1 else [0] for i in range(3)))) for j in subsets}
 for j,k in product(subsets,repeat=2):
  raw=sum((mul(F(1,p**max(ei,fi)) for p,ei,fi in zip(P,e,f)) for e in active[j] for f in active[k]),F(0))
  require(raw==coeff(j,k,al,be),'direct finite kernel sum')
  require(0<=raw<=K[j][k],'finite kernel dominated by infinite kernel')
 labels={};high=0
 for aa in product(*(range(hp+np+1) for hp,np in zip(h,heights))):
  j=sum(1<<i for i in range(3) if aa[i]>h[i]);ee=tuple(max(aa[i]-h[i],0) for i in range(3));d=epow(tuple(min(aa[i],h[i]) for i in range(3)))
  m=epow(aa);key=(j,ee,d)
  require(d in DJ[j] and m==d*epow(ee),'saturated decomposition reconstruction')
  require(key not in labels,'unique full original label')
  labels[key]=m;high+=bool(j)
 require(len(set(labels.values()))==len(labels),'decomposition is injective in modulus')
 require(high==sum(len(DJ[j])*len(active[j]) for j in subsets if j),'all higher original labels counted')
 heightchecks.append({'extra_heights':list(heights),'all_original_divisor_labels':len(labels),'higher_labels':high,'kernel_entries_checked':64})

def lcm(a,b):
 from math import gcd
 return a*b//gcd(a,b)
def pure_constants(ternary_removed):
 removed=[ternary_removed,F(1,5),F(1,7)]
 def cell(d):
  return mul((1-removed[i]) if aa==0 else F(1,P[i]**aa) for i,aa in enumerate(exps[d]))
 mm={j:sum((cell(d) for d in DJ[j]),F(0)) for j in subsets}
 cc={(j,k):sum((cell(lcm(d,e)) for d in DJ[j] for e in DJ[k]),F(0)) for j,k in product(subsets,repeat=2)}
 rr=sum((aJ[j]*mm[j] for j in subsets if j),F(0))
 c=sum((aJ[j]*cc[0,j] for j in subsets if j),F(0))
 s=sum((K[j][k]*cc[j,k] for j,k in product(subsets,repeat=2) if j and k),F(0))
 Ainf=[F(p,p-1)-rho for p,rho in zip(P,removed)]
 Ah=[sum((F(1,p**a) for a in range(hp+1)),F(0))-rho for p,hp,rho in zip(P,h,removed)]
 Binf=[F(p*(p+1),(p-1)**2)-rho for p,rho in zip(P,removed)]
 Bh=[sum((F(2*a+1,p**a) for a in range(hp+1)),F(0))-rho for p,hp,rho in zip(P,h,removed)]
 D=[sum(((a+1+F(1,p-1))*F(1,p**a) for a in range(hp+1)),F(0))-rho for p,hp,rho in zip(P,h,removed)]
 require(rr==mul(Ainf)-mul(Ah),'factored omitted mean')
 require(c==mul(D)-mul(Bh),'factored low-high cross term')
 require(s==mul(Binf)-2*mul(D)+mul(Bh),'factored high-high term')
 require(2*c+s==mul(Binf)-mul(Bh),'ordered full square difference')
 return {'removed_ternary_mass':str(ternary_removed),'delta_r':str(rr),'delta_c':str(c),'delta_s':str(s),'delta_square_increment':str(2*c+s),'A_infinite':list(map(str,Ainf)),'A_low':list(map(str,Ah)),'B_infinite':list(map(str,Binf)),'B_low':list(map(str,Bh)),'D_mixed':list(map(str,D)),'R_ambient_improvement':str(F(347,1680)-rr),'Delta_ambient_improvement':str(F(733,252)-2*c-s),'square_improvement_after_delta0_division':str((F(733,252)-2*c-s)/delta0)}
original=pure_constants(F(1,3));strong=pure_constants(F(4,9))
require((original['delta_r'],original['delta_c'],original['delta_s'],original['delta_square_increment'])==('103/720','7/9','713/945','2183/945'),'oracle explicit constants')
require((strong['delta_r'],strong['delta_c'],strong['delta_s'],strong['delta_square_increment'])==('97/720','34/45','16693/22680','10193/4536'),'effective pure3/pure9 improvement')

# A genuine marked head with independent original/test high residues.
old=[(3,0),(9,4),(5,0),(15,1),(45,37),(7,0),(21,16),(35,24),(63,25),(105,19),(315,109)]
Omega=[x for x in range(base) if all(x%d!=a for d,a in old)]
N=len(Omega);delta=F(N,base)
require(N==86 and all(x%3!=0 and x%9!=4 and x%5!=0 and x%7!=0 for x in Omega),'actual marked pure exclusions')
cellmax={d:F(max(sum(x%d==a for x in Omega) for a in range(d)),N) for d in low}
M={j:sum((cellmax[d] for d in DJ[j]),F(0)) for j in subsets}
C={(j,k):sum((cellmax[lcm(d,e)] for d in DJ[j] for e in DJ[k]),F(0)) for j,k in product(subsets,repeat=2)}

def crt_residue(residues,mods):
 Q=mul(mods)
 return sum(a*(Q//m)*pow(Q//m,-1,m) for a,m in zip(residues,mods))%Q
Q=33075;allaa=list(product(range(4),range(3),range(3)));divs=[epow(aa) for aa in allaa]
higher=[m for m in divs if base%m!=0];carrier=[z for z in range(Q) if z%base in set(Omega)]
al=[F(1,p) for p in P];be=al
rr=sum((coeff(0,j,al,be)*M[j] for j in subsets if j),F(0))
cross=sum((coeff(0,j,al,be)*C[0,j] for j in subsets if j),F(0))
sq=sum((coeff(j,k,al,be)*C[j,k] for j,k in product(subsets,repeat=2) if j and k),F(0))
B2=C[0,0]+2*cross+sq
# Independent regrouping by the twelve exact low projections used by the
# next weighted-law calculation.  This identity needs no uniform mu.
mean_coeff={d:mul(F(p,p-1) if a==hp else F(1) for p,a,hp in zip(P,exps[d],h))-1 for d in low}
pair_coeff={}
for d,e in product(low,repeat=2):
 factors=[]
 for p,a,b0,hp in zip(P,exps[d],exps[e],h):
  factors.append(F(p*(p+1),(p-1)**2) if a==hp and b0==hp else F(p,p-1) if a==hp or b0==hp else F(1))
 pair_coeff[d,e]=mul(factors)-1
for d in low:
 require(mean_coeff[d]==sum((aJ[j] for j in subsets if j and d in DJ[j]),F(0)),
         'each low-label mean coefficient equals its saturated subset sum')
for d,e in product(low,repeat=2):
 direct=sum((K[j][k] for j,k in product(subsets,repeat=2)
             if (j or k) and d in DJ[j] and e in DJ[k]),F(0))
 require(pair_coeff[d,e]==direct,'each ordered pair coefficient equals its saturated subset sum')
Rcaps=sum((mean_coeff[d]*cellmax[d] for d in low),F(0))
Dcaps=sum((pair_coeff[d,e]*cellmax[lcm(d,e)] for d,e in product(low,repeat=2)),F(0))
Rsaturated=sum((aJ[j]*M[j] for j in subsets if j),F(0))
Dsaturated=2*sum((aJ[j]*C[0,j] for j in subsets if j),F(0))+sum((K[j][k]*C[j,k] for j,k in product(subsets,repeat=2) if j and k),F(0))
require(Rcaps==Rsaturated and Dcaps==Dsaturated,'twelve low-cylinder coefficients equal the eight-block transfer')

# SH13 coefficients are nonnegative expectations outside a finite depth box.
# Compare direct depth enumeration with products of one-prime moments.
layout_boxes=[]
for bounds in [(0,0,0),(1,1,1),(8,5,4)]:
 moments=[[sum((F(p-1,p**(z+1))*(1+z)**k for z in range(n+1)),F(0))
           for k in range(3)] for p,n in zip(P,bounds)]
 mass=mul(row[0] for row in moments)
 direct={d:F(0) for d in low}
 direct_mass=F(0)
 for zz in product(*(range(n+1) for n in bounds)):
  prob=mul(F(p-1,p**(z+1)) for p,z in zip(P,zz))
  direct_mass+=prob
  weights={d:mul(1+z for z,a,hp in zip(zz,exps[d],h) if a==hp) for d in low}
  for d,e in product(low,repeat=2):
   direct[lcm(d,e)]+=prob*(weights[d]*weights[e]-1)
 require(direct_mass==mass and 0<mass<1,'finite depth box mass')
 outside={d:F(0) for d in low}
 factored={d:F(0) for d in low}
 for d,e in product(low,repeat=2):
  inside=mul(moments[i][int(exps[d][i]==h[i])+int(exps[e][i]==h[i])]
             for i in range(3))-mass
  factored[lcm(d,e)]+=inside
  remaining=pair_coeff[d,e]-inside
  require(remaining>=0,'each outside ordered-pair coefficient is nonnegative')
  outside[lcm(d,e)]+=remaining
 require(factored==direct,'independent direct and factored weighted depth sums')
 layout_boxes.append({'inclusive_depth_bounds':list(bounds),'points':mul(n+1 for n in bounds),
                      'probability':str(mass),'old_square_coefficient':str(1-mass),
                      'outside_cylinder_coefficients':{str(d):str(outside[d]) for d in low}})
crtchecks=[]
for seed in [1,4,11]:
 tests={m:(seed*(m//3+2*m//5+3*m//7+1)+7)%m for m in divs}
 forbidden={m:(seed*(3*m//3+m//5+5*m//7+2)+13)%m for m in higher}
 centered={}
 for aa,m in zip(allaa,divs):
  mods=[p**a for p,a in zip(P,aa) if a]
  rs=[tests[m]%(p**min(a,hp)) for p,a,hp in zip(P,aa,h) if a]
  centered[m]=crt_residue(rs,mods)
  d=epow(tuple(min(a,hp) for a,hp in zip(aa,h)))
  require(centered[m]%d==tests[m]%d,'added-digit centering preserves every low label')
 rows=[];centerloads=[];final=[]
 for z in carrier:
  A0=sum(z%m==tests[m] for m in low);U=sum(z%m==tests[m] for m in higher);L=A0+U
  rows.append((A0,U,L));centerloads.append(sum(z%m==centered[m] for m in divs))
  if all(z%m!=forbidden[m] for m in higher):final.append(L)
 size=len(rows);q=F(len(final),size);qstar=max(delta0/delta,1-rr)
 require(q>=qstar>0 and delta*q>delta0,'actual finite survivor lower bounds')
 require(F(sum(U for A0,U,L in rows),size)<=rr,'finite saturated mean transfer')
 require(F(sum(A0*U for A0,U,L in rows),size)<=cross,'finite saturated cross transfer')
 require(F(sum(U*U for A0,U,L in rows),size)<=sq,'finite saturated high square transfer')
 require(F(sum(L*L for A0,U,L in rows),size)<=B2,'finite complete square transfer')
 conditioned=F(sum(L*L for L in final),len(final))
 require(conditioned<=1+(B2-1)/qstar<=B2/qstar,'same-law conditioning unit saving')
 for t in [0,1,4,8,12,15,24]:
  actual=F(sum(max(L-t,0) for A0,U,L in rows),size)
  require(actual<=F(sum(max(L-t,0) for L in centerloads),size),'uniform-lift added-digit concentration')
  for u in [F(1,2),F(1),F(2),F(4)]:
   head=F(sum(max(A0-(t-u),0) for A0,U,L in rows),size)
   bound=head+min(rr,sq/(4*u))
   require(actual<=bound,'finite shifted hinge bound')
   require(F(sum(max(L-t,0) for L in final),len(final))<=bound/qstar,'same-law hinge conditioning')
 require(sum(L*L for A0,U,L in rows)<=sum(L*L for L in centerloads),'uniform-lift square concentration')
 crtchecks.append({'seed':seed,'period':Q,'lift_points':size,'final_points':len(final),'q':str(q),'q_lower':str(qstar),'conditional_square':str(conditioned)})

# Equal low observations and q do not determine the conditioned cost.
C9=next(a for a in range(9) if any(x%9==a for x in Omega));eta=F(sum(x%9==C9 for x in Omega),N)
lift=[z for z in range(945) if z%315 in set(Omega)]
vals=[]
for original27 in [C9,C9+9]:
 S=[z for z in lift if z%27!=original27]
 phi=F(sum(z%27==C9 for z in S),len(S));square=F(sum((1+int(z%27==C9))**2 for z in S),len(S))
 vals.append((F(len(S),len(lift)),phi,square))
require(vals[0][0]==vals[1][0]==1-eta/3 and vals[0][1]==0 and vals[1][1]==eta/(3-eta),'post-deletion relative-position obstruction')
require(vals[0][2]==1 and vals[1][2]==1+3*eta/(3-eta),'conditioned-square obstruction')
result={'scope':'ordinary all-height saturated transfer; finite checks are supplementary; delta0 supplied by existing CM8 theorem','subset_order':[[P[i] for i in range(3) if j>>i&1] for j in subsets],'saturated_low_labels':{str(j):DJ[j] for j in subsets},'infinite_kernel':[[str(v) for v in row] for row in K],'height_checks':heightchecks,'oracle_constants':original,'pure3_pure9_improvement':strong,'actual_CRT_checks':crtchecks,'actual_twelve_cap_identity':{'R':str(Rcaps),'Delta':str(Dcaps),'mean_coefficients':{str(d):str(mean_coeff[d]) for d in low},'pair_coefficients_checked':len(pair_coeff)},'post_deletion_obstruction':{'head_eta':str(eta),'q':str(vals[0][0]),'hinges':[str(a[1]) for a in vals],'squares':[str(a[2]) for a in vals]}}
result['common_layout_depth_boxes']=layout_boxes
parser = argparse.ArgumentParser(description=__doc__)
mode = parser.add_mutually_exclusive_group()
mode.add_argument("--check", type=Path, help="compare against an exact certificate")
mode.add_argument("--output", type=Path, help="write the reconstructed certificate")
args = parser.parse_args()
if args.output:
 write_certificate_text(args.output, json.dumps(result, indent=2) + "\n")
else:
 certificate = args.check or (Path(__file__).resolve().parent / 'certificates/saturated_height_certificate.json')
 require(json.loads(read_artifact_text(certificate)) == result, "certificate equals exact reconstruction")
print(json.dumps({'verified':True,'higher_height_cases':len(heightchecks),'kernel_entries':64*len(heightchecks),'oracle_delta_r':original['delta_r'],'oracle_delta_square_increment':original['delta_square_increment'],'strong_delta_r':strong['delta_r'],'strong_delta_c':strong['delta_c'],'strong_delta_s':strong['delta_s'],'strong_delta_square_increment':strong['delta_square_increment'],'actual_CRT_cases':len(crtchecks),'conditioning_obstruction_verified':True},sort_keys=True))
