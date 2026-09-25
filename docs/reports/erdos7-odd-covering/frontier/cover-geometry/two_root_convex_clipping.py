#!/usr/bin/env python3
"""Exact two-root convex clipping certificate and global supporting dual."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
from math import prod
import argparse
import hashlib
import json

ap=argparse.ArgumentParser()
ap.add_argument('--hinge-input',default=str(Path(__file__).with_name('height_three_clipping_envelope.json')))
ap.add_argument('--output',default=str(Path(__file__).with_suffix('.json')))
args=ap.parse_args()
checks=[]
def need(name,p):
    if not p: raise ValueError(name)
    checks.append(name)

source_bytes=Path(args.hinge_input).read_bytes()
source=json.loads(source_bytes)
B=F(source['B'])
target=F(566,49)
corners=[[F(v) for v in c['K_integer'][:8]] for c in source['corners']]
need('same actual PA query supplier',B==F(432040125182653876501,86355045355449035400))
need('complete four low-threshold corner profiles',len(corners)==4 and all(len(c)==8 for c in corners))
need('corner zero dominates every integer endpoint',all(corners[0][n]>=corners[i][n] for n in range(8) for i in range(1,4)))
K=corners[0]
K3=K[3]
r=(24+48*B)/(24-K3)
q=2-(1+3*B)/r
y=3+K3/q
alpha=(1+(1+B)/(r*q))/2
need('exact candidate r',r==F(7548357118614250413488684,625732567524997445251785))
need('dual is a two-point probability',0<q<1)
need('dual atom lies below both root scales',6<y<7<12)
need('dual convex weights',0<alpha<1)
need('dual also respects the complete first moment',q*y<B)

def low_K(t):
    if t==7:return K[7]
    n=t.numerator//t.denominator
    return (n+1-t)*K[n]+(t-n)*K[n+1]

support_rows=[]
for t in sorted({F(n) for n in range(8)}|{y}):
    k=low_K(t)
    lower=q*max(F(0),y-t)
    need('supporting scalar hinge at '+str(t),k>=lower)
    support_rows.append({'t':t,'K':k,'dual_hinge':lower,'gap':k-lower})
need('contact at threshold three',K3==q*(y-3))
need('positive entire low-threshold profile',all(k>=0 for k in K))
need('dual first cancellation',r*q==2*r-1-3*B)
need('dual second cancellation',r*q*(15-y)==12*(1+B))
need('dual weight cancellation',(2*alpha-1)*r*q==1+B)
constant=B-r+(1+B)+r*q*(1-alpha)
w_coefficient=-(1+B)+r*q*(2*alpha-1)
x_coefficient=9*(1+B)-r*q*(alpha*(12-y)+(1-alpha)*(18-y))
need('global certificate dual has zero constant and coefficients',constant==w_coefficient==x_coefficient==0)

def hinge_terms(la,ta,lb,tb):
    if ta>tb:la,ta,lb,tb=lb,tb,la,ta
    if la>=lb:return [(la,ta)]
    cross=(lb*tb-la*ta)/(lb-la)
    return [(la,ta),(lb-la,cross)]

# Setting the unneeded high-threshold costs to zero is optimistic. Every
# nonnegative valid extension costs at least this relaxation. This is used
# only to diagnose the LOWER dual, never to claim an actual upper bound.
def optimistic_K(t):
    return low_K(t) if t<=7 else F(0)

control_count=0
bounded_root_controls=0
for w,ta,tb in product((F(0),F(1,8),F(3,8),F(1,2),F(5,8),F(7,8),F(1)),
                       map(F,(0,1,3,6,9,11)),map(F,(0,1,3,7,12,17))):
    la=w/(12-ta);lb=(1-w)/(18-tb)
    terms=hinge_terms(la,ta,lb,tb)
    knots={F(0),ta,tb,y,*[t for _,t in terms]}
    probes=knots|{t+1 for t in knots}
    if not all(sum(c*max(F(0),z-t) for c,t in terms)==max(la*max(F(0),z-ta),lb*max(F(0),z-tb)) for z in probes):
        raise ValueError(('hinge decomposition',w,ta,tb))
    cost=sum(c*optimistic_K(t) for c,t in terms)
    x=max(la,lb)
    N=B+(1+B)*(max(w,1-w)+9*x)
    if cost<q*max(la*max(F(0),y-ta),lb*max(F(0),y-tb)) or N-r*(1-cost)<0:
        raise ValueError(('global dual control',w,ta,tb))
    # At y<12<18 no root cap activates. These are every breakpoint
    # of the allocation function on [0,y], including both endpoints.
    splits={F(0),y}|{v for v in (ta,y-tb) if 0<=v<=y}
    capped_values=[]
    for split in splits:
        loss_a=la*max(F(0),split-ta)
        loss_b=lb*max(F(0),y-split-tb)
        if not (loss_a<=w and loss_b<=1-w):
            raise ValueError(('bounded root cap at dual atom',w,ta,tb,split))
        capped_values.append(min(w,loss_a)+min(1-w,loss_b))
    if max(capped_values)!=max(la*max(F(0),y-ta),lb*max(F(0),y-tb)):
        raise ValueError(('bounded root allocation maximum',w,ta,tb))
    bounded_root_controls+=1
    control_count+=1
need('all rational hinge and global-dual controls',control_count==252)
need('bounded root envelope equals the hinge at the dual atom',bounded_root_controls==252)

w=F(3,8);ta=tb=F(3);la=w/(12-ta);lb=(1-w)/(18-tb)
N=B+(1+B)*(max(w,1-w)+9*max(la,lb))
cost=la*K3
need('candidate equal slopes and legal clips',la==lb==F(1,24) and 1-ta/12==F(3,4) and 1-tb/18==F(5,6))
need('candidate positive mass certificate',0<1-cost)
need('candidate attains dual globally',N/(1-cost)==r)
need('bounded root loss attains the same scalar moment bound',
     q*max(min(w,la*max(F(0),y-ta)),min(1-w,lb*max(F(0),y-tb)))==cost)
need('full two-root envelope misses continuation gate',r>target)

# Actual fixed original family and all32 Q-activation atoms.
primes=(5,7,11,13,17)
ternary=(0,6,9,15,18)
originals=[{'m':3,'a':1},{'m':9,'a':3}]
for p,a in zip(primes,ternary):
    full_a=a+81*((-a*pow(81,-1,p))%p)
    originals.append({'m':81*p,'a':full_a})
need('actual original labels are distinct',len({c['m'] for c in originals})==7)
need('actual full CRT phases retained',all(c['a']%81==a and c['a']%p==0 for c,p,a in zip(originals[2:],primes,ternary)))
A=[t for t in range(81) if t%3==0 and t%9!=3]
Broot=[t for t in range(81) if t%3==2]
need('actual root fibre sizes',len(A)==18 and len(Broot)==27 and len(set(ternary))==5 and all(t in A for t in ternary))
raw_mass=F(0);hinge_mass=F(0);nu_mass=F(0)
for bits in product((0,1),repeat=5):
    prob=prod(F(1,p) if b else F(p-1,p) for p,b in zip(primes,bits))
    forbidden={a for a,b in zip(ternary,bits) if b}
    ca=F(sum(t not in forbidden for t in A),len(A))
    cb=F(sum(t not in forbidden for t in Broot),len(Broot))
    n=sum(bits)
    if ca!=1-F(n,18) or cb!=1:
        raise ValueError(('actual fibre',bits))
    beta=w*min(F(1),ca/F(3,4))+(1-w)*min(F(1),cb/F(5,6))
    raw_mass+=prob*beta
    hinge_mass+=prob*F(1,24)*max(F(0),F(2*n,3)-3)
    nu_mass+=prob
need('actual Q atoms form one probability',nu_mass==1)
need('nonzero actual clipping loss attains its scalar majorant',1-raw_mass==hinge_mass==F(1,6126120))
all_active_ca=F(sum(t not in set(ternary) for t in A),len(A))
eta_root_A=w*all_active_ca/max(all_active_ca,F(3,4))
eta_root_B=1-w
conditional_root_A=eta_root_A/(eta_root_A+eta_root_B)
fixed_u_root_A=w*all_active_ca/(w*all_active_ca+1-w)
need('root-dependent normalization differs from fixed-u normalization',
     conditional_root_A==F(26,71) and fixed_u_root_A==F(13,43)
     and conditional_root_A!=fixed_u_root_A)

# Scalar-allocation certificate boundaries at the three admissible prefix depths.
prefix_depth_rows=[]
for prefix_h in (2,3,4):
    prefix_k=3**(prefix_h-2)
    prefix_scale=F(6,prefix_k)
    prefix_theta=F(3**prefix_h,54)
    prefix_cells=[j for j in range(3**prefix_h) if j%3!=1 and j%9!=3]
    first_residual_cap=F(3)**(prefix_h-4)
    first_layout_weight=F(2,3)
    need('prefix refinement complete residual coefficients at h'+str(prefix_h),
         len(prefix_cells)==5*prefix_k
         and prefix_scale*prefix_theta==1
         and first_layout_weight/(1-F(1,3))==1
         and prefix_theta*first_layout_weight==first_residual_cap
         and first_residual_cap<=1)
    partition_count=0
    partition_ok=True
    for residual_e in (4,5,6):
        for original_phase in range(3**residual_e):
            memberships=sum(original_phase%(3**prefix_h)==cell for cell in prefix_cells)
            in_actual_pure_survivor=(original_phase%3!=1 and original_phase%9!=3)
            if memberships!=int(in_actual_pure_survivor):
                partition_ok=False
            partition_count+=1
    need('prefix refinement unique actual residual assignment at h'+str(prefix_h),
         partition_ok and partition_count==1053)
    descendants=[sum(cell%9==old_cell for cell in prefix_cells) for old_cell in (0,2,5,6,8)]
    complete_prefix_coefficient=sum((F(1,3**(a-2)) for a in range(2,prefix_h+1)),F(0))+F(1,2*prefix_k)
    # sum_{a>h}3^(h-a)=1/2, so max(w_i/kappa_i) contributes(s_h/2)x.
    complete_deep_query_sum=F(1,3)/(1-F(1,3))
    need('prefix refinement entire query and ancestor coefficients at h'+str(prefix_h),
         descendants==[prefix_k]*5
         and complete_prefix_coefficient==F(3,2)
         and complete_deep_query_sum==F(1,2)
         and prefix_scale*prefix_k==6 and y>prefix_scale)
    prefix_depth_rows.append({'h':prefix_h,'cells':len(prefix_cells),
                              'scale':prefix_scale,'complete_residual_cap':prefix_theta,
                              'actual_phase_partition_controls':partition_count,
                              'ancestor_query_coefficient':complete_prefix_coefficient})
need('prefix refinement reuses the exact probability-dual cancellation',
     0<q<1 and q*y<B and r*q*y==30*r-27-57*B
     and -(1+B)/2+r*q*y/6==5*(r-1-2*B)
     and r>1+2*B and r>F(566,49))
prefix_refinement={'scope':'For h=2,3,4 all live cells may have independent weights and clips; the retained raw-query/untruncated-hinge certificate is at least the existing579 optimum. Not an exact minimum at these depths or an actual-law lower bound. No claim for h>4.',
                   'depths':prefix_depth_rows,'certificate_lower_barrier':r,
                   'reused_dual_mean':q*y,'added_named_checks':10}

# Retain the actual bound loss_i<=w_i and hence total loss<=1.
# The scalar dual uses a feasible allocation, not actual-family load data.
prefix_sat_barrier=(B+F(9,10)*(1+B))/(1-q/5)
prefix_sat_derivative=q*(1+2*B)-(1+B)/2
need('bounded prefix loss exact rational barrier',
     prefix_sat_barrier==F(33914609213286804860799851870837955027791000698,
                          2820576058673273244795335584651143056943842655))
need('bounded prefix loss ratio increases on its full feasible range',
     0<q<1 and prefix_sat_derivative==F(17390107284801685724248961343831194148679463,
                                      3948335574863297592288635491589985266448000)
     and prefix_sat_derivative>0)
need('bounded prefix loss barrier remains above continuation gate',
     F(566,49)<prefix_sat_barrier<r)
prefix_fill_rows=[]
for fill_h in (2,3,4):
    fill_k=3**(fill_h-2)
    fill_s=F(6,fill_k)
    fill_cells=[j for j in range(3**fill_h) if j%3!=1 and j%9!=3]
    fill_n=len(fill_cells)
    # Positive unequal weights and unequal clips exercise the individual cap.
    fill_weights=[F(j+1,fill_n*(fill_n+1)//2) for j in range(fill_n)]
    fill_clips=[F(1+j%5,6) for j in range(fill_n)]
    fill_thresholds=[fill_s*(1-kappa) for kappa in fill_clips]
    fill_lambdas=[w/(fill_s-t) for w,t in zip(fill_weights,fill_thresholds)]
    old_prefixes=(0,2,5,6,8)
    prefix_masses={a:sum((w for cell,w in zip(fill_cells,fill_weights) if cell%9==a),F(0)) for a in old_prefixes}
    fill_old=max(old_prefixes,key=lambda a:prefix_masses[a])
    fill_z=prefix_masses[fill_old]
    fill_indices=[j for j,cell in enumerate(fill_cells) if cell%9==fill_old]
    fill_loads=[fill_s if j in fill_indices else F(0) for j in range(fill_n)]
    # Place the excess in the same prefix; the selected cell is already capped.
    fill_loads[fill_indices[0]]+=y-6
    need('bounded loss prefix filling is feasible at h'+str(fill_h),
         sum(fill_weights)==1 and len(fill_indices)==fill_k
         and fill_k*fill_s==6 and y>6
         and sum(fill_loads)==y and all(load>=0 for load in fill_loads)
         and fill_z>=F(1,5))
    fill_losses=[min(w,lam*max(F(0),load-t))
                 for w,lam,load,t in zip(fill_weights,fill_lambdas,fill_loads,fill_thresholds)]
    need('bounded loss all selected prefix cells saturate at h'+str(fill_h),
         all(fill_losses[j]==fill_weights[j] for j in fill_indices)
         and sum(fill_losses)==fill_z and sum(fill_losses)<=1
         and all(F(0)<=loss<=w for loss,w in zip(fill_losses,fill_weights)))
    prefix_fill_rows.append({'h':fill_h,'prefix_cells':fill_k,'scale':fill_s,
                             'max_prefix':fill_old,'prefix_mass':fill_z,
                             'dual_allocation_total':sum(fill_loads),'capped_loss':sum(fill_losses)})
prefix_refinement['bounded_loss']={'scope':'For h=2,3,4 the sharp scalar allocation envelope also caps each cell loss by its weight and total loss by1. With the same raw query numerator, the feasible moment dual gives this strict lower barrier, not an exact optimum or actual-law lower bound.',
                                  'lower_barrier':prefix_sat_barrier,'derivative_numerator':prefix_sat_derivative,
                                  'prefix_fill_controls':prefix_fill_rows,'added_named_checks':9}
prefix_refinement['added_named_checks']=19

result={'scope':'Exact global certificate optimum for both the full max-two-hinge envelope and all same-scalar-moment bounded-root-loss estimates retaining the raw query numerator; not an actual-query lower bound or source-realizability claim.',
 'hinge_input_sha256':hashlib.sha256(source_bytes).hexdigest(),'B':B,'K3':K3,'target':target,
 'optimum':r,'gap':r-target,'q':q,'y':y,'alpha':alpha,'dual_mean':q*y,
 'supporting_hinge':support_rows,'rational_parameter_controls':control_count,
 'bounded_root_parameter_controls':bounded_root_controls,
 'actual_originals':originals,'actual_raw_mass':raw_mass,'actual_loss':hinge_mass,
 'actual_all_active_root_conditional':conditional_root_A,
 'actual_fixed_u_all_active_root_conditional':fixed_u_root_A,
 'prefix_refinement':prefix_refinement,'check_count':len(checks),'checks':checks}
Path(args.output).write_text(json.dumps(result,default=str,indent=2)+'\n')
print(json.dumps({'checks':len(checks),'parameter_controls':control_count,'optimum':str(r),
                  'optimum_decimal':float(r),'gap':str(r-target),'actual_loss':str(hinge_mass),'bounded_prefix_barrier':str(prefix_sat_barrier)}))
