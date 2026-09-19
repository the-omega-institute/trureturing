#!/usr/bin/env python3
"""Complete original AP11/13 blocks sharpen the fixed full-Haar hinge account."""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from hashlib import sha256
from decimal import Decimal,localcontext
from functools import lru_cache
import argparse,importlib.util,json,sys
sys.dont_write_bytecode=True
DEFAULT_SOURCE='certificates/source_norms/high_rho_full_haar_thresholds.json'
DEFAULT_PROOF='profile-notes/whole-cover/335-original-ap-blocks-sharpen-the-fixed-full-haar-account.md'
DEFAULT_CERTIFICATE='certificates/source_norms/high_rho_original_ap_blocks.json'
PREFIX=((11,F(5,3)),(13,F(12,7)))

def require(ok,msg):
    if not ok:raise ValueError(msg)

def module(n,p):
    s=importlib.util.spec_from_file_location(n,p)
    require(s is not None and s.loader is not None,'Readable provider')
    m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m

def encode(v):
    if isinstance(v,F):return str(v)
    if isinstance(v,dict):return {str(k):encode(x) for k,x in v.items()}
    if isinstance(v,(list,tuple)):return [encode(x) for x in v]
    return v

def law(factors,cut):
    atoms={1:F(1)};mean=F(1)
    for p,c in factors:
        require(0<=c<=p,'Valid auxiliary count probability')
        nxt={}
        for a,m in atoms.items():
            for n in range(1,(cut-1)//a+1):
                q=1-c/p if n==1 else c*F(p-1,p**n)
                nxt[a*n]=nxt.get(a*n,F(0))+m*q
        atoms=nxt;mean*=1+c/F(p-1)
    tm=1-sum(atoms.values());tf=mean-sum(n*q for n,q in atoms.items())
    require(min(atoms.values())>=0 and tm>=0 and tf>=cut*tm,'Complete auxiliary tails')
    return atoms,tm,tf

def calculate(base,source,proof):
    io=module('apblocks_io',base/'certificate_io.py');src=module('apblocks_raw',base/'verify_joint_frontier.py')
    parent=json.loads(io.read_artifact_bytes(source),object_pairs_hook=io._unique)
    require(parent['schema']=='erdos7-high-rho-full-haar-thresholds-v1','Established333 source and schedule')
    parent_proof=base/'profile-notes/whole-cover/333-variable-full-haar-thresholds-retain-more-survivor-mass.md'
    parent_producer=base/'frontier/whole-cover/high_rho_full_haar_thresholds.py'
    for path,pin in parent['source_sha256'].items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest()==pin,'Current inherited source '+path)
    require(sha256(io.read_artifact_bytes(parent_proof)).hexdigest()==parent['ordinary_proof']['sha256']
            and sha256(io.read_artifact_bytes(parent_producer)).hexdigest()==parent['producer_sha256'],
            'Current333 proof and producer')
    g=parent['guard'];S=F(g['S_lower']);E=F(g['E_lower']);scale=F(g['centered_operator_factor']);M=F(g['centered_mean_upper'])
    ec=F(parent['denominator_mass_coefficient']);D=F(parent['denominator_constant'])
    require(F(g['delta_upper'])==F(1,4000) and F(g['rho_lower'])==F(1,10)
            and E==ec*S-D and E>0,'Same finite source and sole13 denominator')
    meanN=F(7,6)*F(8,7)
    require(meanN==src.moment(PREFIX,1),'Complete AP11/AP13 product mean')
    data=[]
    for i,j in product(range(2,5),repeat=2):
        be=tuple(F(1,4) if k==i else F(0) for k in range(5));la=tuple(F(1,72) if k==j else F(0) for k in range(5))
        dat=src.data(((F(1,2),F(0),F(0),F(0),F(0)),(F(0),F(1,4)),be,la,F(3,4)))
        require(dat[3:]==(F(1,4),F(3,20)) and src.raw357(F(0),dat)-F(1,4)==F(13,20),
                'Exact centered source mean at every whole-face vertex')
        data.append(((i,j),dat))
    ap_inventory={}
    @lru_cache(None)
    def ap_input(r):
        cut=src.ceilq(r);atoms,tm,tf=law(PREFIX,cut);floor=tf-r*tm
        records,outside=src.ap_original_block_inputs(PREFIX,cut,1)
        checks=[];active_sum=F(0)
        for (e,f),finite,active,tail in records:
            expected_active=(F(1) if e==0 else F(5,3*11**e))*(F(1) if f==0 else F(12,7*13**f))
            actual={}
            for n in range(1,cut):
                q=sum((src.ap_count_probability(11,F(5,3),u)*src.ap_count_probability(13,F(12,7),n//u)
                       for u in range(1,n+1) if n%u==0 and u>e and n//u>f),F(0))
                if q:actual[n]=q
            require((e+1)*(f+1)<cut and dict(finite)==actual and active==expected_active
                    and tail==active-sum(actual.values()) and tail>=0,
                    'Original AP exponent-block finite atoms and complete active tail')
            active_sum+=active
            checks.append(dict(exponents=(e,f),finite=actual,active=active,tail=tail))
        require(outside==meanN-active_sum and outside>=0,'All omitted original AP blocks paid by their full active mass')
        for n,q in atoms.items():
            require(sum(dict(finite).get(n,F(0)) for _,finite,_,_ in records)==n*q,
                    'Every finite AP outcome retains all of its original exponent labels')
        values=[]
        for _,dat in data:
            raw=src.raw_ap_hinge(r,PREFIX,dat);centered=raw-F(1,4)*floor
            parts=sum(src.zero7_raw(('ap_block',(('h',r),PREFIX,e,f)),dat) for (e,f),_,_,_ in records)
            require(centered==parts+outside*F(13,20) and centered>=0,
                    'Existing original-block API is exactly a sum of nonnegative centered source costs')
            values.append(centered)
        ap_inventory[str(r)]=dict(threshold=r,cutoff=cut,count_atoms=atoms,tail_mass=tm,tail_first=tf,
                                  unit_floor=floor,original_blocks=checks,outside_active_mass=outside,centered_vertex_values=values)
        return floor,tuple(values)
    rows=[];post=();total=F(0)
    for old in parent['rows']:
        p=old['prime'];t=F(old['threshold']);cap=F(old['cap']);cut=int(t)
        require(t.denominator==1 and tuple((pp,F(cc)) for pp,cc in old['incoming_post_factors'])==post,
                'Unchanged incoming full physical chain')
        atoms,tm,tf=law(post,cut);full,wm,wf=law(PREFIX+post,cut)
        check,tail=src.ap_product_distribution(post,cut)
        require(atoms==check and (tm,tf)==tail[:2],'Independent complete post-count tail')
        c=wf-t*wm;floor=tf-t*tm
        require(c==F(old['mass_coefficient']) and floor==F(old['post_floor']) and c>=floor>=0,
                'Unchanged full mass term and post-only conditioning floor')
        constants=[tf*meanN*M for _ in data];payments=[]
        for z,q in atoms.items():
            r=t/z;afloor,centers=ap_input(r)
            require(r>1,'Finite post-count source cost vanishes after centering at one')
            for i,a in enumerate(centers):constants[i]+=scale*q*z*a
            payments.append(dict(post_count=z,probability=q,threshold=r,ap_unit_floor=afloor))
        C=max(constants);shift=C+(c-floor)*S
        require(C>=0 and shift>=0 and ec*C+(c-floor)*D>0,'Safe sole13 normalization and source-mass monotonicity')
        H=floor+shift/E;b=H/(p-1-t);total+=b
        oldH=F(old['hinge_upper'])
        require(H<oldH,'Strict rowwise improvement over the same333 physical chain')
        rows.append(dict(prime=p,threshold=t,cap=cap,incoming_post_factors=post,
                         post_atoms=atoms,post_tail_mass=tm,post_tail_first=tf,post_floor=floor,
                         full_tail_mass=wm,full_tail_first=wf,mass_coefficient=c,
                         finite_payments=payments,tail_centered_payment=tf*meanN*M,
                         vertex_constants=constants,finite_constant=C,hinge_upper=H,charge_upper=b,
                         cumulative_charge_upper=total,mass_lower=1-total,
                         reference333_hinge_upper=oldH,hinge_improvement=oldH-H))
        print('prime',p,'mass',float(1-total),flush=True)
        post+=((p,cap),)
    byp={r['prime']:r for r in rows};m43=byp[43]['mass_lower'];m47=byp[47]['mass_lower'];deficit=-m47
    require(m43>F(parent['survival43_mass_lower']) and m47>F(parent['mass47_lower']) and m47<0,
            'Strict same-chain improvement, while47 remains unresolved')
    paths=[base/'certificate_io.py',base/'verify_joint_frontier.py',source,parent_proof,parent_producer,
           base/'profile-notes/06-a-common-matrix-bound-for-all-actual-rectangles.md',
           base/'profile-notes/j-source/329-a-finite-whole-j-neighborhood-covers-high-surplus.md',
           base/'profile-notes/whole-cover/330-a-finite-high-surplus-source-survives-through29.md']
    def key(p):
        try:return str(p.resolve().relative_to(base.resolve()))
        except ValueError:return str(p.resolve())
    raw=io.read_artifact_bytes(proof)
    out=dict(schema='erdos7-high-rho-original-ap-blocks-v1',
             scope='Same finite source, actualAP11/T4-AP13/T5 supported law, and fixed full-Haar continuation as333. Original AP11/AP13 exponent labels are collected within each outer post-count before source maximization. All complete count and original-label tails retained. Same sole13 denominator. Strictly stronger43 survival lower; positive47 correction budget remains. No optimum, actual independence, or unrestricted continuation claim.',
             source_sha256={key(p):sha256(io.read_artifact_bytes(p)).hexdigest() for p in paths},
             ordinary_proof=dict(sha256=sha256(raw).hexdigest(),byte_count=len(raw)),
             producer_sha256=sha256(io.read_artifact_bytes(Path(__file__))).hexdigest(),
             guard=g,schedule=parent['schedule'],denominator_mass_coefficient=ec,denominator_constant=D,
             ap_prefix=PREFIX,ap_product_mean=meanN,ap_input_inventory=ap_inventory,rows=rows,
             survival43_mass_lower=m43,mass47_lower=m47,overlap_correction47_required_strictly_greater_than=deficit,
             reference333_survival43_mass_lower=F(parent['survival43_mass_lower']),
             reference333_mass47_lower=F(parent['mass47_lower']),
             improvement47=m47-F(parent['mass47_lower']))
    return io,encode(out)

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    p.add_argument('--source',type=Path);p.add_argument('--proof',type=Path);p.add_argument('--certificate',type=Path)
    g=p.add_mutually_exclusive_group(required=True);g.add_argument('--write',action='store_true');g.add_argument('--check',action='store_true')
    a=p.parse_args();certificate=a.certificate or a.base/DEFAULT_CERTIFICATE
    io,out=calculate(a.base,a.source or a.base/DEFAULT_SOURCE,a.proof or a.base/DEFAULT_PROOF)
    if a.write:io.write_certificate_text(certificate,json.dumps(out,indent=2)+'\n')
    else:require(out==json.loads(io.read_artifact_bytes(certificate),object_pairs_hook=io._unique),'Complete original AP block account regenerates')
    with localcontext() as ctx:
        ctx.prec=30
        for k in ('survival43_mass_lower','mass47_lower','improvement47'):
            q=F(out[k]);print(k,Decimal(q.numerator)/Decimal(q.denominator))
    print('PASS complete original-AP-block same-chain account')

if __name__=='__main__':main()
