#!/usr/bin/env python3
"""Same-PG1-law higher hinges, fixed11/13 transfer and scalar17/19 boundary.

Run with python3 -I -O; --write rebuilds the adjacent certificate. Canonical
original9/H2 and mod3 probability certificates are hash-bound inputs. The
point geometry helper is loaded from the same directory.
All omitted auxiliary depths are included by exact geometric moments.
"""
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from pathlib import Path
import importlib.util
import argparse
import json
import numpy as np

HERE=Path(__file__).resolve().parent

def load(path,name):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module

def require(ok,message):
    if not ok:raise ArithmeticError(message)

def costs(A,B,full_A,full_B,R,v,roots,full_roots,z,t):
    z3,z5,z7=z;u=z7+1;s=(z3+1)*(z5+1)
    if u>=t-1:
        av=np.maximum(full_A-t,0)@(R-v)+full_A@v
        bv=int((full_B@v).max())
        return {str(i):int(av[full_roots==i].max())+u*bv-t*int(v.sum()) for i in (1,2)}
    n=len(A)
    base=np.zeros((n,n),dtype=np.int64)
    first=base.copy();second=base.copy();together=base.copy()
    for k in range(len(R)):
        a=A[:,k,None];b=B[None,:,k];x=a+u*b
        ga=np.maximum(a-t,0);gx=np.maximum(x-t,0)
        base+=(R[k]-v[k])*ga+v[k]*gx
        low=(R[k]-v[k])*(np.maximum(a+s-t,0)-ga)
        ai=low+v[k]*(np.maximum(x+s-t,0)-gx)
        bi=v[k]*(np.maximum(x+u*s-t,0)-gx)
        ji=low+v[k]*(np.maximum(x+(1+u)*s-t,0)-gx)
        require(np.all(ji>=ai+bi),'convex coincident singleton increment')
        np.maximum(first,ai,out=first);np.maximum(second,bi,out=second)
        np.maximum(together,ji,out=together)
    score=base+np.maximum(first+second,together)
    return {str(i):int(score[roots==i].max()) for i in (1,2)}

def direct(full_A,full_B,R,v,roots,z,t,i):
    """No singleton elimination; independent exhaustive complete layout pairs."""
    u=z[2]+1;AA=full_A[roots==i];best=-1
    for start in range(0,len(AA),32):
        A=AA[start:start+32]
        score=np.broadcast_to((np.maximum(A-t,0)@(R-v))[:,None],(len(A),len(full_B))).copy()
        for k in range(len(R)):
            score+=v[k]*np.maximum(A[:,k,None]+u*full_B[None,:,k]-t,0)
        best=max(best,int(score.max()))
    return best

def consumer(square, h2, h4, h6):
    h3, h5 = (h2+h4)/2, (h4+h6)/2
    p1, p2, mean_n = F(28, 33), F(50, 363), F(7, 6)
    tail_mass, tail_mean = 1-p1-p2, mean_n-p1-2*p2
    require(tail_mass > 0 and tail_mean >= 3*tail_mass, 'complete multiplier N>=3 tail')
    charge11 = h4/6
    # For N=2, (2L-5)+ = (L-2)+ +(L-3)+ for integer L.
    # For N>=3, (N L-5)+ <= N(L-2)+ +(2N-5), including L=1.
    charge13 = (p1*h5+p2*(h2+h3)+h2*tail_mean+2*tail_mean-5*tail_mass)/7
    alternative = (F(131, 726)*h2+F(50, 363)*h3+F(28, 33)*h5+F(2, 121))/7
    require(charge13 == alternative, 'independent complete multiplier calculation')
    growth11 = 1+F(32, 100)*F(10, 6)
    growth13 = 1+F(38, 144)*F(12, 7)
    require(growth11*growth13 == F(1403, 630), 'fixed thresholds4/5 square growth')
    survival = 1-charge11-charge13
    require(survival > 0, 'positive joint surviving mass at two new primes')
    before = growth11*growth13*square
    after = 1+(before-1)/survival
    return {'threshold11': 4, 'threshold13': 5, 'H2': str(h2), 'H3_interpolated': str(h3),
            'H4': str(h4), 'H5_interpolated': str(h5), 'H6': str(h6),
            'head_square': str(square), 'charge11': str(charge11), 'charge13': str(charge13),
            'total_charge': str(charge11+charge13), 'retained_mass_lower': str(survival),
            'square_before_conditioning': str(before), 'supported_square_upper': str(after)}



def scalar_gap(seed):
    # T6 at17 followed by the necessary19 denominator condition.
    a,b,K=F(25,128),F(1,1024),F(324)
    polynomial=lambda f:(K-(1+a)*f)**2-4*(K-f)*K*b*f
    quadratic,linear,constant=F(44145,16384),-F(9477,8),F(104976)
    require((1+a)**2+4*K*b==quadratic and -2*K*(1+a)-4*K*K*b==linear
            and K*K==constant,'expanded two-step necessary polynomial')
    lo,hi=F(123058769468748,10**12),F(123058769468749,10**12)
    require(polynomial(lo)>0>polynomial(hi),'rational bracket of smaller necessary root')
    require(2*quadratic*hi+linear<0 and polynomial(F(256))<0,
            'smaller root unique below256 and excludes inputs through256')
    require(hi<seed<256 and polynomial(seed)<0,'provided square-only seed fails17/19')
    stronger=(500-(1+a)*seed)**2-4*(500-seed)*500*b*seed
    require(stronger<0,'every admissible scalar17 output exceeds500')
    return {'scope':'necessary condition for existing square-only T6, not actual noncoverage or an obstruction to richer-profile continuation',
            'input_seed':str(seed),'prime17_a':str(a),'prime17_b':str(b),
            'prime19_requires_seed_below':'324',
            'polynomial_coefficients':list(map(str,(quadratic,linear,constant))),
            'smaller_root_lower':str(lo),'smaller_root_upper':str(hi),
            'polynomial_at_seed':str(polynomial(seed)),
            'gap_above_necessary_threshold_lower':str(seed-hi),
            'all_admissible_prime17_updates_exceed':'500',
            'negative_discriminant_for500':str(stronger)}


def evaluate(data,source_directory):
    PG=load(source_directory/'verify_point_geometry.py','point_geometry')
    source=(source_directory/'mod3_conditioned_geometry_certificate.json').read_bytes()
    m9raw=(source_directory/'original9_conditioned_geometry_certificate.json').read_bytes()
    m9=json.loads(m9raw)
    require(sha256(source).hexdigest()==data['mod3_source_sha256']==m9['source_sha256']
            and sha256(m9raw).hexdigest()==data['original9_source_sha256'],
            'hash-bound canonical original9 and unchanged probability source')
    require(m9['source_case']=='PG1' and m9['result']['hinge2']['H2_upper']=='3'
            and F(m9['result']['hinge2']['minimum_margin'])>0,'canonical same-law H2 prerequisite')
    case=next(c for c in json.loads(source)['cases'] if c['name']=='PG1')
    pts=np.array(case['points'],dtype=np.int64);xs=np.array(case['old_points'],dtype=np.int64)
    w=np.array(case['weight_numerators'],dtype=np.int64);den=case['weight_denominator']
    require(sum(map(int,w))==den and np.all(w>=0),'normalized actual point law')
    require(case['points']==[x for x in range(315) if all(x%d!=a for d,a in case['family'])],'actual low carrier')
    ri=np.array([xs.tolist().index(int(x%45)) for x in pts])
    R=np.array([sum(int(ww) for ww,r in zip(w,ri) if r==i) for i in range(len(xs))],dtype=np.int64)
    v=np.array([max(int(ww) for ww,r in zip(w,ri) if r==i) for i in range(len(xs))],dtype=np.int64)
    require(np.all(R>=v),'row relaxation')
    cut=(8,5,4)
    ds,gamma,eta,rem,depths,probs,beta,eo=PG.coeffs(cut);rem[ds.index(35)]-=F(1,4)
    caps=[max(sum(int(ww) for x,ww in zip(pts,w) if x%d==a) for a in range(d)) for d in ds]
    GD=PG.group_setup({'survivors':pts.tolist(),'points':xs.tolist()},(9,45),35)
    group,_,_=PG.group_oracle(w,GD)
    loss=F(group['value'],48*den)+sum((r*F(c,den) for r,c in zip(rem,caps)),F(0))
    q=1-loss
    require(q==F(m9['result']['survival_lower'])>0,'same independent actual survival')
    outside=[]
    for d,g in zip(ds,gamma):
        inside=F(1)
        for p,h,limit in zip((3,5,7),(2,1,1),cut):
            e,dd=0,d
            while dd%p==0:e+=1;dd//=p
            inside*=sum((F(p-1,p**(z+1))*(1+z)**int(e==h) for z in range(limit+1)),F(0))
        outside.append(1+g-inside-1+beta)
    require(min(outside)>=0,'nonnegative complete first-moment geometric remainder')
    tail=sum((e*F(c,den) for e,c in zip(outside,caps)),F(0))
    require(str(tail)==m9['result']['hinge2']['outside_mean_increment'],'same complete first tail')
    mods=(3,5,9,15)
    choices=list(product(*(sorted(set(int(x%d) for x in xs)) for d in mods)))
    feat=np.array([[[int(x%d==a) for x in xs] for d,a in zip(mods,row)] for row in choices],dtype=np.int64)
    roots=np.array([row[0] for row in choices],dtype=np.int64)
    _,full_feat=PG.geometry(xs)
    full_roots=np.array([int(xs[np.flatnonzero(row[1])[0]]%3) for row in full_feat],dtype=np.int64)
    require(4*den*(6*78)**2<2**63,'all convex singleton intermediates fit signed64')
    cache={}
    for z3,z5 in product(range(9),range(6)):
        B=1+np.einsum('aer,e->ar',feat,np.array([1,1+z5,1+z3,1+z5],dtype=np.int64))
        FB=np.einsum('aer,e->ar',full_feat,np.array([1,1,1+z5,1+z3,1+z5,(1+z3)*(1+z5)],dtype=np.int64))
        cache[z3,z5]=(B,FB)
    branches=[];direct_checks=[]
    for j in sorted(set(map(int,xs%9))):
        nums={str(t):{str(i):[] for i in (1,2)} for t in (4,6)}
        for z in depths:
            B,FB=cache[z[:2]]
            A=B-feat[:,2,:]+(xs%9==j).astype(np.int64)
            FA=FB-full_feat[:,3,:]+(xs%9==j).astype(np.int64)
            for t in (4,6):
                got=costs(A,B,FA,FB,R,v,roots,full_roots,z,t)
                for i in (1,2):nums[str(t)][str(i)].append(got[str(i)])
                if j in (1,2) and z==(0,0,0):
                    for i in (1,2):
                        require(direct(FA,FB,R,v,full_roots,z,t,i)==got[str(i)],'independent full-layout hinge maximum')
                        direct_checks.append({'root3':i,'root9':j,'depth':list(z),'threshold':t,'numerator':got[str(i)]})
        for i in (1,2):
            values={}
            for t in (4,6):
                nn=nums[str(t)][str(i)]
                U=(1-beta)*F(nn[0],den)+sum((p*F(n,den) for p,n in zip(probs,nn)),F(0))+tail
                baseline=1+(pts%3==i).astype(np.int64)+(pts%9==j).astype(np.int64)
                require(np.all(np.maximum(baseline-t,0)==0),'signed floor is zero at thresholds4/6')
                # R_E((C-g(b))*mu)=C*R_E(mu), so the exact signed
                # target criterion is U-C*q<=0. It provides no extra rebate.
                values[str(t)]={'numerators':nn,'lambda_upper':str(U),'nu_upper':str(U/q)}
            branches.append({'root3':i,'root9':j,'hinges':values})
        print(json.dumps({'completed_original9':j,'depths_per_branch':len(depths)}),flush=True)
    bounds={str(t):max(F(r['hinges'][str(t)]['nu_upper']) for r in branches) for t in (4,6)}
    scenario=consumer(F(m9['result']['Gamma_upper']),F(3),bounds['4'],bounds['6'])
    require(F(scenario['supported_square_upper'])<F(data['rounded_Gamma13_upper']),
            'strict fixed11/13 same-law endpoint')
    result={'source_sha256':sha256(source).hexdigest(),'original9_sha256':sha256(m9raw).hexdigest(),
            'scope':'same actual PG1 low probability, fixed original3/original9 across Z; all finite original357 heights; one actual conditioning',
            'depth_box':list(cut),'survival_lower':str(q),'group_numerator48':group['value'],'cap_numerators':caps,
            'outside_mean_coefficients':list(map(str,outside)),'outside_mean_increment':str(tail),
            'branches':branches,'H4_upper':str(bounds['4']),'H6_upper':str(bounds['6']),
            'direct_checks':direct_checks,'signed_floor':'zero for b=1+I3+I9 at thresholds4/6',
            'fixed11_13_consumer':scenario,
            'scalar17_19_gap':scalar_gap(F(scenario['supported_square_upper']))}
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate',nargs='?',type=Path,
                        default=HERE/'original9_convex_transfer_certificate.json')
    parser.add_argument('--source-directory',type=Path,default=HERE)
    parser.add_argument('--write',action='store_true')
    args=parser.parse_args()
    data=json.loads(args.certificate.read_text())
    require(data['schema']=='erdos7-original9-convex-transfer-v1'
            and data['rounded_Gamma13_upper']=='152329/1000','specified transfer certificate')
    result=evaluate(data,args.source_directory)
    if args.write:
        data['result']=result;args.certificate.write_text(json.dumps(data,indent=2)+'\n')
    else:require(data['result']==result,'exact convex branches, full tails, same-law transfer and scalar gap')
    print(json.dumps({'H4_upper':result['H4_upper'],'H6_upper':result['H6_upper'],
                      'Gamma13_upper':result['fixed11_13_consumer']['supported_square_upper'],
                      'qnew_lower':result['fixed11_13_consumer']['retained_mass_lower'],
                      'scalar17_19_necessary_seed_below':result['scalar17_19_gap']['smaller_root_upper'],
                      'branches':len(result['branches']),'direct_checks':len(result['direct_checks'])}),flush=True)


if __name__=='__main__':main()
