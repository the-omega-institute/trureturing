#!/usr/bin/env python3
"""PG1 weighted final-root floor and a shared source-survival denominator.

Recompute exact whole costs and weighted row geometry on the unchanged PG1 law.
All omitted higher357 depths and the entire new-prime multiplier tail are
included.  --write rebuilds the adjacent certificate; otherwise compare it.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from pathlib import Path
import argparse
import importlib.util
import json
import numpy as np

HERE=Path(__file__).resolve().parent

def load(path,name):
    spec=importlib.util.spec_from_file_location(name,path)
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    return mod

def require(ok,message):
    if not ok:raise ArithmeticError(message)

def whole_cost(A,B,FA,FB,R,v,roots,full_roots,z,scale):
    """Exact row maximum of (scale*L-5)+, including scaled singletons."""
    z3,z5,z7=z;u=z7+1;s=scale*(z3+1)*(z5+1)
    A=scale*A;B=scale*B;FA=scale*FA;FB=scale*FB
    if scale*(1+u)>=5:
        av=np.maximum(FA-5,0)@(R-v)+FA@v
        bv=int((FB@v).max())
        return {str(i):int(av[full_roots==i].max())+u*bv-5*int(v.sum()) for i in (1,2)}
    n=len(A);base=np.zeros((n,n),dtype=np.int64)
    first=base.copy();second=base.copy();together=base.copy()
    for k in range(len(R)):
        a=A[:,k,None];b=B[None,:,k];x=a+u*b
        ga=np.maximum(a-5,0);gx=np.maximum(x-5,0)
        base+=(R[k]-v[k])*ga+v[k]*gx
        low=(R[k]-v[k])*(np.maximum(a+s-5,0)-ga)
        ai=low+v[k]*(np.maximum(x+s-5,0)-gx)
        bi=v[k]*(np.maximum(x+u*s-5,0)-gx)
        ji=low+v[k]*(np.maximum(x+(1+u)*s-5,0)-gx)
        require(np.all(ji>=ai+bi),'scaled convex coincident singleton increment')
        np.maximum(first,ai,out=first);np.maximum(second,bi,out=second)
        np.maximum(together,ji,out=together)
    val=base+np.maximum(first+second,together)
    return {str(i):int(val[roots==i].max()) for i in (1,2)}

def evaluate(data,source_directory):
    PG=load(source_directory/'verify_point_geometry.py','point_geometry')
    CT=load(source_directory/'verify_original9_convex_transfer.py','convex_transfer')
    names=('certificates/mod3_conditioned_geometry_certificate.json',
           'certificates/original9_conditioned_geometry_certificate.json',
           'certificates/original9_convex_transfer_certificate.json')
    raw={name:read_artifact_bytes(source_directory/name) for name in names}
    hashes={name:sha256(value).hexdigest() for name,value in raw.items()}
    require(hashes==data['source_sha256'],'three canonical source hashes')
    source,m9,cx=(json.loads(raw[name]) for name in names)
    require(m9['source_sha256']==cx['mod3_source_sha256']==hashes[names[0]]
            and cx['original9_source_sha256']==hashes[names[1]],'same canonical PG1 sources')
    case=next(c for c in source['cases'] if c['name']=='PG1')
    q=F(m9['result']['survival_lower']);G=F(m9['result']['Gamma_upper'])
    qtail=F(cx['result']['fixed11_13_consumer']['retained_mass_lower'])
    C=F(data['floor_reference']);Wmax=C-1;B2=3*Wmax
    require(C==149 and q>0 and qtail>0,'fixed nonnegative floor and independent survival')
    emax=max(F(r['criterion_excess']) for r in m9['result']['records'])
    ehbase=max(F(r['criterion_excess']) for r in m9['result']['hinge2']['records'])
    require(33+emax/q==G and ehbase<0,'source square and strict signed hinge excess')
    h2base=3+ehbase
    P=F(1403,630);M=F(4,3)
    pi={1:F(28,33),**{n:F(50,3*11**n) for n in range(2,5)}}
    pt5=1-sum(pi.values());mt5=F(7,6)-sum(n*p for n,p in pi.items())
    pt3=1-pi[1]-pi[2];mt3=F(7,6)-pi[1]-2*pi[2];k3=2*mt3-5*pt3
    require(pt5>0 and mt5>=5*pt5 and mt3==F(31,726) and k3==F(2,121),
            'complete N>=5 and N>=3 multiplier tails')
    pts=np.array(case['points'],dtype=np.int64)
    xs=np.array(case['old_points'],dtype=np.int64)
    w=np.array(case['weight_numerators'],dtype=np.int64);den=case['weight_denominator']
    require(sum(map(int,w))==den and np.all(w>=0),'unchanged normalized low law')
    require(case['points']==[x for x in range(315) if all(x%d!=a for d,a in case['family'])],
            'actual low support')
    ri=np.array([xs.tolist().index(int(x%45)) for x in pts])
    cut=(8,5,4);ds,gamma,eta,rem,depths,probs,beta,eo=PG.coeffs(cut)
    rem[ds.index(35)]-=F(1,4)
    outside=[]
    for d,g in zip(ds,gamma):
        inside=F(1)
        for p,h,limit in zip((3,5,7),(2,1,1),cut):
            e,dd=0,d
            while dd%p==0:e+=1;dd//=p
            inside*=sum((F(p-1,p**(z+1))*(1+z)**int(e==h)
                         for z in range(limit+1)),F(0))
        outside.append(1+g-inside-1+beta)
    require(min(outside)>=0 and min(rem)>=0,'full nonnegative first-moment tails')
    GD=PG.group_setup({'survivors':pts.tolist(),'points':xs.tolist()},(9,45),35)
    def caps(vv):
        return [max(sum(int(a) for x,a in zip(pts,vv) if x%d==r)
                    for r in range(d)) for d in ds]
    def deletion(vv):
        require(np.all(vv>=0) and 48*sum(map(int,vv))<2**63,'deletion arithmetic range')
        cc=caps(vv);gg,_,_=PG.group_oracle(vv,GD)
        bound=F(gg['value'],48*den)+sum((r*F(c,den) for r,c in zip(rem,cc)),F(0))
        return {'upper':str(bound),'caps':cc,'group_numerator48':gg['value']}
    ordinary_deletion=deletion(w)
    require(1-F(ordinary_deletion['upper'])==q,'recomputed original357 survival')
    mods=(3,5,9,15)
    choices=list(product(*(sorted(set(int(x%d) for x in xs)) for d in mods)))
    feat=np.array([[[int(x%d==a) for x in xs] for d,a in zip(mods,row)]
                   for row in choices],dtype=np.int64)
    roots=np.array([row[0] for row in choices],dtype=np.int64)
    _,full_feat=PG.geometry(xs)
    full_roots=np.array([int(xs[np.flatnonzero(row[1])[0]]%3)
                         for row in full_feat],dtype=np.int64)
    safety=4*den*int(Wmax)*(6*78)**2
    require(safety<2**63,'all integer singleton intermediates fit signed64')
    cache={}
    for z3,z5 in product(range(9),range(6)):
        B=1+np.einsum('aer,e->ar',feat,
                      np.array([1,1+z5,1+z3,1+z5],dtype=np.int64))
        FB=np.einsum('aer,e->ar',full_feat,
                     np.array([1,1,1+z5,1+z3,1+z5,(1+z3)*(1+z5)],dtype=np.int64))
        cache[z3,z5]=(B,FB)

    def geometry(vv,keys,label,final_roots=None):
        """Fixed charge roots remain fixed throughout every auxiliary depth."""
        R=np.array([sum(int(a) for a,r in zip(vv,ri) if r==i)
                    for i in range(len(xs))],dtype=np.int64)
        v=np.array([max(int(a) for a,r in zip(vv,ri) if r==i)
                    for i in range(len(xs))],dtype=np.int64)
        require(np.all(R>=v),'weighted row relaxation')
        cc=caps(vv);tail=sum((a*F(c,den) for a,c in zip(outside,cc)),F(0))
        records=[];checks=[]
        for cj in sorted(set(map(int,xs%9))):
            nums={key:{str(i):[] for i in (1,2)} for key in keys}
            for z in depths:
                B,FB=cache[z[:2]]
                A=B-feat[:,2,:]+(xs%9==cj).astype(np.int64)
                FA=FB-full_feat[:,3,:]+(xs%9==cj).astype(np.int64)
                for key in keys:
                    scale=1 if key[0]=='h' else int(key[1:])
                    threshold=int(key[1:]) if key[0]=='h' else 5
                    if key[0]=='h':
                        got=CT.costs(A,B,FA,FB,R,v,roots,full_roots,z,threshold)
                    else:
                        got=whole_cost(A,B,FA,FB,R,v,roots,full_roots,z,scale)
                    for ci in (1,2):nums[key][str(ci)].append(got[str(ci)])
                    check=((final_roots is None and cj==1 and key in ('n1','n2')) or
                           (final_roots==(2,2) and cj==8 and key in ('h4','n1','n2')))
                    if check and z==(0,0,0):
                        for ci in (1,2):
                            require(CT.direct(scale*FA,scale*FB,R,v,full_roots,z,threshold,ci)
                                    ==got[str(ci)],'independent full-layout maximum')
                            checks.append({'charge_root3':ci,'charge_root9':cj,
                                           'cost':key,'depth':list(z),'numerator':got[str(ci)]})
            for ci in (1,2):
                values={}
                for key in keys:
                    nn=nums[key][str(ci)];scale=1 if key[0]=='h' else int(key[1:])
                    U=(1-beta)*F(nn[0],den)+sum((p*F(n,den) for p,n in zip(probs,nn)),F(0))+scale*tail
                    values[key]={'numerators':nn,'lambda_upper':str(U)}
                records.append({'charge_root3':ci,'charge_root9':cj,'costs':values})
            print(json.dumps({'geometry':label,'completed_charge_root9':cj}),flush=True)
        return {'caps':cc,'outside_first_increment':str(tail),'records':records,'direct_checks':checks}

    whole=geometry(w,('n1','n2','n3','n4'),'unweighted')
    UG={n:max(F(r['costs']['n'+str(n)]['lambda_upper']) for r in whole['records'])
        for n in range(1,5)}
    UH4=q*F(cx['result']['H4_upper'])
    directcharge=UH4/(6*q)+(sum(pi[n]*UG[n]/q for n in pi)+5*mt5-5*pt5)/7
    directsurvival=1-directcharge
    require(directsurvival>0,'direct whole-cost comparison survival')
    directgamma=1+(P*G-1)/directsurvival
    oldloss=UH4/(6*q)+(pi[1]*UG[1]/q+pi[2]*UG[2]/q+mt3*h2base+k3)/7
    require(0<oldloss<1-qtail,'strict independent signed whole-cost survival')
    stronggamma=1+(P*G-1)/(1-oldloss)
    whole.update({'lambda_upper':{str(n):str(U) for n,U in UG.items()},
                  'direct_charge':str(directcharge),'direct_Gamma13_upper':str(directgamma),
                  'signed_H2_charge':str(oldloss),'signed_H2_Gamma13_upper':str(stronggamma)})

    records=[]
    for square in m9['result']['records']:
        fi,fj=square['root3'],square['root9'];eij=F(square['criterion_excess'])
        Gij=33+eij/(q if eij>=0 else 1)
        J=P*G-M*(G-Gij);cheap=J-C+Wmax*oldloss
        rec={'final_root3':fi,'final_root9':fj,'source_square_excess':str(eij),
             'separate_denominator_unit_floor_excess':str(cheap)}
        if cheap<=0:
            U4=Wmax*UH4;U1=Wmax*UG[1];U2=Wmax*UG[2]
            eh=Wmax*ehbase;delta=F(0)
            rec['method']='uniform final floor'
        else:
            b=1+(pts%3==fi).astype(np.int64)+(pts%9==fj).astype(np.int64)
            factor=int(C)-b*b
            require(np.all(factor>=0) and int(factor.max())<=Wmax,
                    'nonnegative final-root weight')
            weighted=w*factor
            geo=geometry(weighted,('h2','h4','n1','n2'),f'final{fi}-{fj}',(fi,fj))
            for r in geo['records']:
                ci,cj=r['charge_root3'],r['charge_root9']
                gb=((pts%3==ci)&(pts%9==cj)).astype(np.int64)
                deletion_data=deletion(w*(int(B2)-factor*gb))
                signed=F(r['costs']['h2']['lambda_upper'])+F(deletion_data['upper'])-B2
                r['costs']['h2'].update({'signed_target':str(B2),
                                         'weighted_deletion':deletion_data,'criterion_excess':str(signed)})
            loss=deletion(w*(b*b-1))
            floor_mean=F(sum(int(a)*int(bb*bb-1) for a,bb in zip(w,b)),den)
            delta=max(F(0),floor_mean-F(loss['upper']))
            ehweighted=max(F(r['costs']['h2']['criterion_excess']) for r in geo['records'])
            eh=min(ehweighted,Wmax*ehbase)
            U4=min(max(F(r['costs']['h4']['lambda_upper']) for r in geo['records']),Wmax*UH4)
            U1=max(F(r['costs']['n1']['lambda_upper']) for r in geo['records'])
            U2=max(F(r['costs']['n2']['lambda_upper']) for r in geo['records'])
            rec.update({'method':'weighted final-original-root floor','geometry':geo,
                        'floor_increment_mu_mean':str(floor_mean),'floor_increment_deletion':loss,
                        'weighted_hinge2_excess':str(ehweighted)})
        # The same actual Q occurs in every source conditional observation:
        # Q*J <=33P Q+(P-M)e_max+M e_ij;
        # Q*H2(Wnu)<=3(C-1)Q+eh; Q*mass(Wnu)<=(C-1)Q-delta.
        # Choosing these bounds BEFORE division gives criterion <= A+B/Q.
        A=33*P-C+Wmax*(3*mt3+k3)/7
        B=(P-M)*emax+M*eij+U4/6+(pi[1]*U1+pi[2]*U2+mt3*eh-k3*delta)/7
        require(B>0,'common source denominator maximized at its independent lower bound')
        excess=A+B/q
        rec.update({'selected_lambda_H4':str(U4),'selected_lambda_G1':str(U1),
                    'selected_lambda_G2':str(U2),'selected_hinge2_excess':str(eh),
                    'positive_floor_residual':str(delta),'criterion_constant':str(A),
                    'criterion_inverse_Q_coefficient':str(B),'criterion_excess':str(excess)})
        records.append(rec)
        print(json.dumps({'final_roots':[fi,fj],'criterion_excess':float(excess)}),flush=True)
    worst=max(F(r['criterion_excess']) for r in records)
    bound=C+worst/(qtail if worst>=0 else 1)
    require(worst<0 and bound<F(data['rounded_Gamma13_upper']),
            'strict common-law final supported square improvement')
    return {'scope':'one unchanged actual PG1 nu; arbitrary finite original357 and11/13 heights; independent final and charge roots; one final conditioning',
            'source_sha256':hashes,'depth_box':list(cut),'source_survival_lower':str(q),
            'independent_tail_survival_lower':str(qtail),'ordinary_deletion':ordinary_deletion,
            'outside_first_coefficients':list(map(str,outside)),
            'source_square_max_excess':str(emax),'source_hinge2_max_excess':str(ehbase),
            'mean_tail_multiplier':str(M),'second_tail_multiplier':str(P),
            'new_multiplier_Nge3_mass':str(pt3),'new_multiplier_Nge3_mean':str(mt3),
            'maximum_integer_bound':safety,'unweighted_whole_cost':whole,'records':records,
            'maximum_criterion_excess':str(worst),'Gamma13_upper':str(bound)}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate',nargs='?',type=Path,default=HERE/'certificates/pg1_joint_tail_certificate.json')
    parser.add_argument('--source-directory',type=Path,default=HERE)
    parser.add_argument('--write',action='store_true')
    args=parser.parse_args();data=json.loads(read_artifact_text(args.certificate))
    require(data['schema']=='erdos7-pg1-joint-tail-v1','certificate schema')
    result=evaluate(data,args.source_directory)
    if args.write:
        data['result']=result;write_certificate_text(args.certificate, json.dumps(data,indent=2)+'\n')
    else:require(data['result']==result,'exact complete-tail geometry and shared-denominator certificate')
    print(json.dumps({'Gamma13_upper':result['Gamma13_upper'],
                      'Gamma13_decimal':float(F(result['Gamma13_upper'])),
                      'maximum_criterion_excess':result['maximum_criterion_excess'],
                      'unweighted_direct_Gamma13_upper':result['unweighted_whole_cost']['direct_Gamma13_upper'],
                      'weighted_final_root_pairs':sum(r['method']=='weighted final-original-root floor'
                                                      for r in result['records'])}),flush=True)

if __name__=='__main__':main()
