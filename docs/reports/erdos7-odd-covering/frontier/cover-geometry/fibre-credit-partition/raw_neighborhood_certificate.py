"""Exact radius-1/10000 comparison bounds at the two fixed FC132 sources.
Only one declared radius is evaluated; no source or radius search.
"""
import argparse,json
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
from math import prod
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--input',required=True)
ap.add_argument('--output',required=True)
args=ap.parse_args();raw=Path(args.input).read_bytes();data=json.loads(raw)
checks=0
def need(ok,message):
 global checks
 checks+=1
 if not ok:raise ValueError(message)
expected_hash='4e824f35c5f921cdacee1cb462cf3387f5524978e859c65460e45cb3fcb5f8c4'
need(sha256(raw).hexdigest()==expected_hash,'Declared FC132 center result bytes')
P=(11,13,17,19,23,29,31,37,41);delta=F(1,10000);gamma=F(1,2)
b={p:F(1,p-2) for p in (5,7)+P}
def cap(p,l):return F(p-1,p-2)/p**l
def B(p,l):return cap(p,l)*F(p,p-1)
def phi(p,l):
 v=cap(p,l);k=0
 while v>delta:v/=p;k+=1
 need(v<=delta and (k==0 or p*v>delta),'Exact minimal geometric cutoff')
 return k*delta+v*F(p,p-1)
C=prod((1+b[q] for q in P),start=F(1));C1=sum((b[q] for q in P),F(0));C2=C-1-C1
f51,f52,f71,f72=phi(5,1),phi(5,2),phi(7,1),phi(7,2)
S=C2*(1+b[5]+b[7])+C1*(B(5,2)+B(7,2))+C*b[5]*b[7]
omega=F(3,2)*(C1*(f52+f72)+C2*(f51+f71)+C*(b[7]*f51+b[5]*f71))
T_epsilon=(5+7+2*len(P))*delta
group_error=(5+7+3*len(P))*delta
T_fee_error=F(3,2)*S*T_epsilon
error=group_error+omega+T_fee_error
need(T_epsilon==30*delta and group_error==39*delta and T_fee_error==45*S*delta,'Declared conservative raw coefficients')
need(omega==F(91555439,58835256480),'Fixed-head-cap modulus matches exact MC12 value')
need(F(3,2)*S==F(240191291,466350885),'Full-inventory coefficient matches MC13')
expected_scores={'first_layer_witness':F(17062109570167,198315713846250),'bounded_joint_result':F(25372782312134,297473570769375)}
centers=[]
need(len(data['results'])==2,'Exactly two predeclared centers')
for entry in data['results']:
 name=entry['recognized_schema'];score=F(entry['modes']['head_min']['score'])
 need(name in expected_scores and score==expected_scores[name],'Exact FC132 min-cap center score')
 need(F(entry['gamma'])==gamma and entry['support_count']==2036,'Fixed weight and numerical inventory')
 need(score==F(entry['weighted_group_residual'])-F(entry['modes']['head_min']['free'])-F(entry['modes']['head_min']['selected']),'Center residual-minus-fees identity')
 lower=score-error
 need(lower>0,'Positive certified raw neighborhood margin')
 centers.append({'schema':name,'witness_path':entry['witness_path'],'witness_sha256':entry['witness_sha256'],'center_score':str(score),'center_score_decimal':float(score),'neighborhood_lower_bound':str(lower),'neighborhood_lower_bound_decimal':float(lower)})
need({c['schema'] for c in centers}==set(expected_scores),'Both distinct required centers present')
out={'contract':'Conditional uniform lower bounds on two specified raw-state neighborhoods of radius exactly 1/10000 around the FC132 sources, using ternary height at most one, fixed physical addresses, gamma=1/2, fixed finite support and caps, actual-source guards and head totals at most one. Not a bound on the whole source domain.',
 'input_sha256':sha256(raw).hexdigest(),'gamma':str(gamma),'radius':str(delta),'private_primes':list(P),
 'coordinate_norms':{'heads':'Each root/head/physical row differs by at most radius.','private':'At each root/private q, |Delta g|, sup_i|Delta X_i| and sup_j|Delta Y_j| are each at most radius; X=g*x, Y=g*y.'},
 'modulus':{'T_sup_error':str(T_epsilon),'group_error':str(group_error),'fixed_T_head_fee_error':str(omega),'kernel_fee_error':str(T_fee_error),'inventory_S':str(S),'total_error':str(error),'total_error_decimal':float(error)},
 'centers':centers,'checks':checks,
 'limits':['The neighborhood is intersected with the admissible common actual/raw-source domain and all row masses are nonnegative with each head total at most one.','The continuous raw min-cap function retains supported-private cap charges at zero carriers; it is not the boundary rule that discards such roots.','Fixed pure caps and inventory, physical addresses and gamma are essential; no radius optimization or source search was performed.','No global arbitrary-source positivity, arbitrary-prime extension, full AP realization of the centers, or Lean verification is claimed.']}
Path(args.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
print(json.dumps({'checks':checks,'error':str(error),'error_decimal':float(error),'centers':centers},sort_keys=True))
