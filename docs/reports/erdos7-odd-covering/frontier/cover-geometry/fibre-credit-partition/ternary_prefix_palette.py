"""Exact constants and actual-prefix counterexample for the FC55 consumer."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import json
from math import lcm,prod
from pathlib import Path

ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--input',required=True)
ap.add_argument('--palette-result',required=True)
ap.add_argument('--output',required=True)
args=ap.parse_args()
INPUT=Path(args.input)
checks=0

def need(ok,msg):
 global checks
 checks+=1
 if not ok:raise ValueError(msg)

input_raw=INPUT.read_bytes()
palette_raw=Path(args.palette_result).read_bytes()
palette=json.loads(palette_raw)
need(palette['input_sha256']==sha256(input_raw).hexdigest(),'FC55 result belongs to this input')
data=json.loads(input_raw);Q=data['primes'];I=[d for d,r in data['selected_witness'] if r==1]
need(Q==[5,7,11,13,17,19,23,29,31,37,41],'Reference prime coordinates')
need(len(I)==187,'FC55 palette')
c={p:F(p-1,p-2) for p in Q}

def cap(d):
 need(type(d) is int and d>1,'Positive nonunit cofactor')
 n=d;out=F(1)
 for p in Q:
  if n%p==0:
   out*=c[p]
   while n%p==0:n//=p;out/=p
 need(n==1,'supported cofactor')
 return out

Lambda=F(1,3)+sum((cap(d) for d in I),F())
C=prod(c.values());delta=F(palette['direct_rational_lower'])
need(delta==F(292527371565907424953871442589053611843,9096975436175030140708833970611382254375),'Inherited FC55 reserve')
need(C==F(1048576,403767) and C<F(8,3),'nonternary density cap')
need(delta>F(4,125),'FC55 rational reserve')
need(Lambda==F(168769304242196707293415566822404691426002591,308068383579416257083082334631421410785113125),'raw palette cap')
Omega5=Lambda/81
head=F(1,500)-Lambda/1296
final=head-F(7,8000)
need(Omega5<F(1,100),'depth5 collision upper')
need(head>F(63,40000),'head bound')
need(final>F(7,10000),'SH12 continuation bound')
need(F(1,500)-F(7,8000)==F(9,8000),'zero collision tail margin')
unrestricted_loss=(C-1)/(2*C*3**6)
unrestricted_head=F(1,500)-unrestricted_loss
unrestricted_final=unrestricted_head-F(7,8000)
need(unrestricted_loss==F(644809,1528823808),'all-cofactor depth6 loss')
need(unrestricted_head==F(301604827,191102976000),'all-cofactor depth6 head')
need(unrestricted_final==F(134389723,191102976000),'all-cofactor depth6 final')
need(unrestricted_final>F(7,10000),'all-cofactor depth6 tail continuation')
need(F(1,500)-(C-1)/(2*C*3**5)-F(7,8000)<0,'depth5 same allowance insufficient')

# Globally fixed CRT phases. Divisor closed, irredundant, no duplicate label.
family=[(3,0),(5,0),(9,2),(15,1),(27,5),(45,37),(81,8),(135,28),(405,244)]
L=lcm(*(m for m,a in family));need(L==405,'period')
labels={m for m,a in family}
need(len(labels)==len(family),'distinct numerical labels')
for m in labels:
 need(all(d in labels for d in range(2,m+1) if m%d==0),'numerical divisor closure')
private={}
for m,a in family:
 pts=[x for x in range(L) if x%m==a and all(x%n!=b for n,b in family if n!=m)]
 need(bool(pts),'private integer for each original')
 private[m]=pts[0]
survivors=[x for x in range(L) if all(x%m!=a for m,a in family)]
need(len(survivors)==124,'whole actual survivor count')
need(not [x for x in survivors if x%81==1],'empty actual fibre at1mod81')
stars=[(m,a) for m,a in family if m%5==0 and m!=5]
need([a%5 for m,a in stars]==[1,2,3,4],'all four nonzero5 roots')
need([a%(m//5) for m,a in stars]==[1,1,1,1],'nested literal ternary prefixes')
need(all(sum(m==3**i*5 for m,a in stars)==1 for i in range(1,5)),'one star per ternary layer')
need(all(1%(m//5)==a%(m//5) for m,a in stars),'same ternary point sees all stars')
need(F(len([x for x in survivors if x%3==1]),405)==F(68,405),'chosen root actual mass')
Omega_example=sum((F(3,3**i)*F(1,4) for i in range(2,5)),F())
need(Omega_example==F(13,108),'actual same-source collision charge')
result={'input_sha256':sha256(input_raw).hexdigest(),'palette_result_sha256':sha256(palette_raw).hexdigest(),'checks':checks,'palette_count':len(I),
'Lambda':str(Lambda),'nonternary_density_cap':str(C),'FC55_reserve':str(delta),
'depth5_Omega_upper':str(Omega5),'head_density_lower':str(head),'head_density_lower_decimal':float(head),
'final_supported_mass_lower':str(final),'final_supported_mass_lower_decimal':float(final),
'unrestricted_above_depth6':{'loss':str(unrestricted_loss),'head_density_lower':str(unrestricted_head),'final_supported_mass_lower':str(unrestricted_final),'final_decimal':float(unrestricted_final)},
'zero_collision_head_density':'1/500','zero_collision_final_supported_mass':'9/8000',
'counterexample':{'family':family,'period':L,'survivors':len(survivors),'private_points':private,'empty_fibre':'1 mod81','collision_charge':str(Omega_example)},
'scope':'Ordinary reuse of PF13-PF18 collision selection with FC55; actual fixed phases, finite labels, arbitrary heights. No Lean verification or unrestricted Erdos7 resolution.'}
Path(args.output).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'checks':checks,'Lambda':float(Lambda),'Omega5':float(Omega5),'head':float(head),'final':float(final),'actual_counterexample_survivors':len(survivors)},sort_keys=True))
