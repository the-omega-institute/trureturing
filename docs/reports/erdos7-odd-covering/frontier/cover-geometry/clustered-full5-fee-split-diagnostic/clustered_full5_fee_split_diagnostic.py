#!/usr/bin/env python3
"""Exact fixed-dual ablation of the unchanged 692 head gate.

Predeclared test: if the loss-only feasible-dual upper is below 193/100000,
then eliminating every nonunit query fee cannot repair this source/interface.
Otherwise this SAME witness does not exclude that route; no feasible field,
optimal value, lawful fee deletion, or unrestricted covering result follows.
No optimizer or retention-field search is used. All arithmetic is exact.
"""
from pathlib import Path
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import prod,lcm
import argparse,importlib.util,json,time,resource,platform
import numpy as np

CHECKS=0
def ck(x):
    global CHECKS
    CHECKS+=1
    if not x: raise ArithmeticError('fee split check '+str(CHECKS))

def load_pinned(path,expected):
    raw=path.read_bytes(); ck(sha256(raw).hexdigest()==expected)
    return json.loads(raw)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--base',type=Path,default=Path(__file__).resolve().parent.parent)
    ap.add_argument('--helper',type=Path)
    ap.add_argument('--witness',type=Path)
    ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    ap.add_argument('--metrics',type=Path)
    args=ap.parse_args();started=time.perf_counter()
    args.helper=args.helper or args.base/'clustered_full5_allfield_verify.py'
    args.witness=args.witness or args.base/'clustered_full5_allfield_dual.json'
    ck(sha256(args.helper.read_bytes()).hexdigest()=='edc32a8aff0e0fb8319e448da05a882b618d74ea97412cacdb5412bf1c7aca56')
    spec=importlib.util.spec_from_file_location('fixed692',args.helper)
    core=importlib.util.module_from_spec(spec);spec.loader.exec_module(core)
    witness=load_pinned(args.witness,'907c8b8f2a7636179893a4cdf1646be1eaf35c9da68dc0472f2c0308f0ea934e')
    base640=load_pinned(args.base/'remaining33_global_root_exclusion_certificate.json','36e1be912a058df44a9ce3b13c89d97574620176b921e037568ceb96dd0f87d4')
    pins=base640['dependencies']
    base=load_pinned(args.base/'actual_pair_activation_certificate.json',pins['actual_pair_activation_certificate.json'])
    v635=load_pinned(args.base/'conditional30_fixedstar_augmented_certificate.json',pins['conditional30_fixedstar_augmented_certificate.json'])
    c=F(1084133,201247200);g=F(200163067,201247200);target=F(193,100000)
    ck(g+c==1 and g==core.G)
    ck(c==F(base['constants']['continuation_c'])==F(v635['constants']['c'])==F(base640['constants']['c']))
    ck(g==F(base640['constants']['g']) and target==F(witness['expected']['target']))
    Q=core.Q;primes=(3,5)+Q
    def fees(labels):
        result=[F(0)]*512
        for modulus in labels:
            rem=modulus;ee=[]
            for p in primes:
                e=0
                while rem%p==0:rem//=p;e+=1
                ee.append(e)
            ck(rem==1 and max(ee)<=2)
            support=sum(1<<i for i,e in enumerate(ee[2:]) if e)
            cap=prod(F(1,q-1) if e==1 else F(1,q*(q-2)) for q,e in zip(Q,ee[2:]) if e)
            result[32*(4*ee[0]+ee[1])+support]+=cap
        return result
    L=list(map(F,base['complete_coefficients']['loss']))
    W=list(map(F,base['complete_coefficients']['weighted_nonunit_query']))
    pair=fees(base640['inventory']['paid_pairs90'])
    added=fees(base640['inventory']['paid370'])
    central=fees(base640['inventory']['paid_central3'])
    ck(pair==list(map(F,v635['paid_pair_loss_coefficients'])))
    ck(added==list(map(F,v635['stages']['mixed370']['added_loss_coefficients'])))
    ck([(i,x) for i,x in enumerate(central) if x]==[(192,F(1)),(288,F(1)),(320,F(1))])
    loss=[g*(l+p+d+b) for l,p,d,b in zip(L,pair,added,central)]
    query=[c*w for w in W]
    ck(len(loss)==len(query)==512 and min(loss)>=0 and min(query)>=0)
    ck([a+b for a,b in zip(loss,query)]==list(map(F,base640['combined512_coefficients'])))
    fullmode=[]
    for i,q in enumerate(Q):
        if i:
            j=256+(1<<i);amount=g/F(q*(q-2));loss[j]+=amount
            fullmode.append({'index':j,'q':q,'amount':str(amount),'component':'loss'})
    full=[a+b for a,b in zip(loss,query)]
    D=witness['denominator'];p=core.prepare(args.base,args.witness,D)
    scale_lcm=lcm(p['L'],*(x.denominator for x in loss+query));ratio=scale_lcm//p['L']
    ck(scale_lcm==ratio*p['L'])
    denominator=5*D*scale_lcm*p['Dc']
    selectors=[]
    for mode in range(16):
        ex,ey=divmod(mode,4)
        xm=((0,),(0,1),(0,1,2,4,5),(0,1,2,4,5))[ex]
        ym=((0,),(0,1,2,3),tuple(m for m in range(20) if m!=5),tuple(m for m in range(20) if m!=5))[ey]
        for left,right in product(xm,ym):
            ids=[i for i,(l,m) in enumerate(p['cells']) if (ex==0 or (l//3==left if ex==1 else l==left)) and (ey==0 or (m//5==right if ey==1 else m==right))]
            mult=F(1)
            if ex==3:mult*=(F(81,82) if left==4 else F(1))/F(2-(left==4),9)
            if ey==3:mult*=F(4,5)*(F(1875,1876) if right==10 else F(1))/F(4-(right==10),75)
            ck((mult*p['Dc']).denominator==1)
            selectors.append((ids,int(mult*p['Dc'])))
    ck(len(selectors)==559)
    scatter_loss=[{} for _ in p['cells']];scatter_query=[{} for _ in p['cells']]
    for mode,support,sid,column,weight in witness['rows']:
        j=32*mode+support;ids,mult=selectors[sid]
        kl=loss[j]*scale_lcm;kq=query[j]*scale_lcm
        ck(kl.denominator==kq.denominator==1 and loss[j]+query[j]==full[j])
        vl=int(kl)*weight*mult;vq=int(kq)*weight*mult
        for ci in ids:
            scatter_loss[ci][column]=scatter_loss[ci].get(column,0)+vl
            scatter_query[ci][column]=scatter_query[ci].get(column,0)+vq
    for ci,old in enumerate(p['scatter']):
        ck(set(old)==set(scatter_loss[ci])==set(scatter_query[ci]))
        for column,value in old.items():
            ck(scatter_loss[ci][column]+scatter_query[ci][column]==value*ratio)
    shape=p['category_shape'];rootcount=np.zeros(shape,dtype=np.uint8)
    for axis,size in enumerate(shape):
        sh=[1]*5;sh[axis]=size;rootcount+=(np.arange(size)<2).astype(np.uint8).reshape(sh)
    good=rootcount<=1
    names=('full','loss_only','query_only');totals={name:0 for name in names}
    source_num=0;actual_states=0;reports=[]
    ck(8*prod(q*(q-1) for q in Q)<2**63 and p['M0']<2**63)
    strides=[prod(p['token_shape'][k+1:]) for k in range(5)]
    for ci,(l,m) in enumerate(p['cells']):
        masses=np.full(shape,(2-(l==4))*(4-(m==10)),dtype=np.int64)
        for axis,row in enumerate(p['counts'][ci]):
            sh=[1]*5;sh[axis]=len(row);masses*=np.array(row,dtype=np.int64).reshape(sh)
        masses*=good;mask=masses>0
        if not np.any(mask):continue
        debits=[]
        for scat in (scatter_loss,scatter_query):
            tensor=np.zeros(p['token_shape'],dtype=object)
            for column,val in scat[ci].items():tensor.flat[column]=val
            d=core.transform(tensor,p['matrices'])[mask]
            ck(all(type(x) is int and x>=0 for x in d))
            flat_ids=np.flatnonzero(mask)
            for pos in sorted({0,len(d)//2,len(d)-1}):
                oid=int(flat_ids[pos]);cats=[]
                for size in reversed(shape):cats.append(oid%size);oid//=size
                cats.reverse();maps=[dict(p['matrices'][k][cats[k]]) for k in range(5)]
                direct=0
                for column,coef in scat[ci].items():
                    term=coef
                    for k in range(5):
                        term*=maps[k].get((column//strides[k])%p['token_shape'][k],0)
                        if not term:break
                    direct+=term
                ck(d[pos]==direct)
            debits.append(d)
        loss_d,query_d=debits;weights=masses[mask];row={}
        for name,d in zip(names,(loss_d+query_d,loss_d,query_d)):
            positive=np.maximum(g.numerator*denominator-g.denominator*d,0)
            total=int(np.sum(positive*weights));totals[name]+=total
            row[name]={'positive_numerator':str(total),'positive_states':int(np.count_nonzero(positive))}
        source_num+=int(np.sum(weights));actual_states+=len(weights)
        reports.append({'cell':[l,m],'source_num':int(np.sum(weights)),'actual_states':len(weights),'uppers':row})
    common_den=p['M0']*g.denominator*denominator
    upper={name:F(v,common_den) for name,v in totals.items()}
    ck(actual_states==2125830 and F(source_num,p['M0'])==F(305684996597,646498195200))
    ck(upper['full']==F(p['expected']['upper'])<target)
    ck(upper['full']<=upper['loss_only']<=g*F(source_num,p['M0']))
    ck(upper['full']<=upper['query_only']<=g*F(source_num,p['M0']))
    R=F(153832,151875)
    outcome='QUERY_ONLY_IMPROVEMENT_EXCLUDED_BY_THIS_DUAL' if upper['loss_only']<target else 'THIS_DUAL_DOES_NOT_EXCLUDE_QUERY_FEE_IMPROVEMENT'
    result={'status':'PASS','scope':'Exact 692 fixed-source fixed-witness fee ablation; hypothetical deleted fees, no feasible field or valid new continuation claimed.','outcome':outcome,'target':str(target),'c':str(c),'g':str(g),'source_mass':str(F(source_num,p['M0'])),'actual_states':actual_states,'fullmode8_additions':fullmode,'checks':CHECKS+core.CHECKS,'new_checks':CHECKS,'inherited_prepare_checks':core.CHECKS,'source_sha256':dict(p['pins'],**pins),'helper_sha256':sha256(args.helper.read_bytes()).hexdigest(),'witness_sha256':sha256(args.witness.read_bytes()).hexdigest(),'program_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'numpy_version':np.__version__,'split_coefficient_lcm':str(scale_lcm),'common_debit_denominator':str(denominator),'loss_coefficients':list(map(str,loss)),'query_coefficients':list(map(str,query)),'bounds':{name:{'upper':str(v),'upper_decimal':float(v),'below_target':v<target,'joint_central_cap_lifted_upper':str(R*v),'lifted_below_target':R*v<target} for name,v in upper.items()},'per_cell':reports}
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    rss=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    if platform.system()!='Darwin':rss*=1024
    if args.metrics: args.metrics.write_text(json.dumps({'seconds':time.perf_counter()-started,'peak_rss_bytes':rss,'program_sha256':result['program_sha256']},indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('loss_coefficients','query_coefficients','per_cell','source_sha256')},indent=2))

if __name__=='__main__':main()
