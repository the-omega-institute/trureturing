#!/usr/bin/env python3
"""Complete nonnegative raw hinges certify actual high-rho survival through29."""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from hashlib import sha256
from decimal import Decimal,localcontext
import argparse,importlib.util,json,sys
sys.dont_write_bytecode=True
DEFAULT_PROOF='profile-notes/330-a-finite-high-surplus-source-survives-through29.md'
DEFAULT_CERTIFICATE='certificates/source_norms/high_rho_survival_through29.json'
PREFIX=((11,F(5,3)),(13,F(12,7)))
POST=((17,F(2)),(19,F(9,5)))
SOURCE='certificates/source_norms/j_whole_face_high_rho_finite_guard.json'

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
        nxt={}
        require(p>1 and 0<=c<=p,'Probability comparator count')
        for n,pn in atoms.items():
            for v in range(1,(cut-1)//n+1):
                q=1-c/p if v==1 else c*F(p-1,p**v)
                nxt[n*v]=nxt.get(n*v,F(0))+pn*q
        atoms=nxt;mean*=1+c/F(p-1)
    tailmass=1-sum(atoms.values());tailfirst=mean-sum(n*p for n,p in atoms.items())
    require(min(atoms.values())>=0 and tailmass>=0 and tailfirst>=cut*tailmass,'Complete product-count tail moments')
    return atoms,tailmass,tailfirst

def calculate(base,source,proof):
    io=module('through29_io',base/'certificate_io.py');src=module('through29_raw',base/'verify_joint_frontier.py')
    parent=json.loads(io.read_artifact_bytes(source),object_pairs_hook=io._unique)
    require(parent['schema']=='erdos7-whole-j-high-rho-finite-guard-v1','Existing329 finite source contract')
    for path,pin in parent['source_sha256'].items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest()==pin,'Current inherited329 source '+path)
    parent_proof=base/'profile-notes/329-a-finite-whole-j-neighborhood-covers-high-surplus.md'
    parent_producer=base/'frontier/j_whole_face_high_rho_finite_guard.py'
    require(sha256(io.read_artifact_bytes(parent_proof)).hexdigest()==parent['ordinary_proof']['sha256']
            and sha256(io.read_artifact_bytes(parent_producer)).hexdigest()==parent['producer_sha256'],
            'Current329 ordinary proof and producer')
    original=parent['whole_face_account']
    require(len(original['rows'])==9,'Complete whole qJ1 raw account')
    P=F(original['uniform_P']);D=F(original['uniform_D']);n0=F(original['numerator_mass_coefficient']);ec=F(original['denominator_mass_coefficient']);off=F(original['offset'])
    delta=F(1,4000);rho=F(1,20);scale=1+7*delta
    require(F(parent['guard']['delta_upper'])==delta
            and F(parent['parameter_errors']['common_centered_operator_factor'])==scale
            and F(parent['parameter_errors']['S0_lower_error'])==F(263,360)*delta
            and F(parent['parameter_errors']['centered_mean_upward_error'])==F(91,60)*delta,
            'Exact established finite centered-operator and mass error constants')
    require(F(parent['actual_finite_witness']['delta'])<delta
            and F(parent['actual_finite_witness']['rho'])>=rho,
            'Existing finite329 family also meets the stronger source guard')
    require(PREFIX+POST==tuple((p,F(p-1,p-1-t)) for p,t in ((11,4),(13,5),(17,8),(19,8))),
            'All four prescribed physical full-Haar prefix caps')
    S=F(3,20)+rho-F(263,360)*delta
    centmean=F(13,20)+F(91,60)*delta
    Dup=scale*D+F(1,7986)*F(91,420)*delta
    Pup=scale*P;E=ec*S-Dup;N=n0*S+Pup;U=off+N/E;d=403-U
    require(E>0 and d>0 and min(Pup,Dup,n0,ec)>0,'One positive raw denominator and signed through19 comparison')
    obs=[]
    for name,t,post in (('H19_11',11,POST),('H13_8',8,()),('H17_8',8,POST[:1])):
        atoms,tm,tf=law(PREFIX+post,t);_,ftm,ftf=law(post,t)
        original_atoms,original_tails=src.ap_product_distribution(PREFIX+post,t)
        require(atoms==original_atoms and (tm,tf)==original_tails[:2],
                'Independent original product-law mass and first-tail moment reconstruction')
        floor=ftf-t*ftm;c=tf-t*tm
        require(c>=floor>=0,'Post-only conditioning floor and full-product affine coefficient')
        vertices=[]
        for ib,il in product(range(2,5),repeat=2):
            beta=tuple(F(1,4) if i==ib else F(0) for i in range(5));late=tuple(F(1,72) if i==il else F(0) for i in range(5))
            dat=src.data(((F(1,2),F(0),F(0),F(0),F(0)),(F(0),F(1,4)),beta,late,F(3,4)))
            require(dat[3:]==(F(1,4),F(3,20)),'Original whole-face containing vertex')
            payments={n:p*n*src.raw357(F(t,n),dat) for n,p in atoms.items()}
            vertices.append(dict(beta_cell=ib,late_cell=il,finite_terms=payments,nonlinear_sum=sum(payments.values())))
        nonlinear=max(v['nonlinear_sum'] for v in vertices)
        C=scale*nonlinear+tf*centmean
        shifted=C+(c-floor)*S
        upper=floor+shifted/E
        require(shifted>=0 and ec*C+(c-floor)*Dup>0,'Safe conditioning denominator substitution and monotone mass bound')
        obs.append(dict(name=name,threshold=t,post=post,complete_factors=PREFIX+post,count_atoms=atoms,tail_mass=tm,tail_first=tf,post_only_floor=floor,raw_affine_mass_coefficient=c,vertices=vertices,uniform_nonlinear_sum=nonlinear,finite_source_constant=C,shifted_numerator=shifted,upper=upper))
        print(name,float(upper),flush=True)
    H={r['name']:r['upper'] for r in obs}
    b17=H['H13_8']/8;b19=H['H17_8']/10;m=1-b17-b19
    require(0<b17+b19<1 and m>d/483,'Positive killed19 mass from complete physical assigned charges')
    criterion=F(451,196)*m+F(155,8624)*d-H['H19_11']
    s29=F(41,196)*m+F(155,94864)*d-H['H19_11']/11
    require(criterion>0 and s29==criterion/11 and s29>F(3,100),'Strict complete327 through29 sufficient criterion')
    def pin_key(p):
        try:return str(p.resolve().relative_to(base.resolve()))
        except ValueError:return str(p.resolve())
    pins={pin_key(p):sha256(io.read_artifact_bytes(p)).hexdigest() for p in (
        base/'certificate_io.py',base/'verify_joint_frontier.py',source,parent_proof,parent_producer,
        base/'profile-notes/31-one-original-zero-five-layout-across-both-actual-measures.md',
        base/'profile-notes/20-genuine-current-kernels-and-positive-charge.md',
        base/'profile-notes/22-comparing-the-two-killed-steps.md',
        base/'profile-notes/303-the-same-law-gamma19-scalar-comparison-needs-joint-observations.md',
        base/'profile-notes/327-actual-two-prime-survival-needs-a-masked-moment.md')}
    proof_raw=io.read_artifact_bytes(proof)
    out=dict(schema='erdos7-high-rho-survival-through29-v1',source_sha256=pins,
        ordinary_proof=dict(sha256=sha256(proof_raw).hexdigest(),byte_count=len(proof_raw)),
        producer_sha256=sha256(io.read_artifact_bytes(Path(__file__))).hexdigest(),
        scope='Actual finite effective9 source qJ>=1-1/4000 and rho>=1/20, no45/135 alignment. Same supported AP(4,5)13 law, prescribed physical pure-base17/T8 and19/T8 followed by actual killed parts, full-Haar23 and29 with delta=1/2. Complete original own tests and all prime-power tails. No prime31 or unrestricted continuation.',
        guard=dict(delta_upper=delta,rho_lower=rho,S_lower=S,centered_operator_scale=scale,centered_mean_upper=centmean),
        through19=dict(E_lower=E,N_upper=N,J_upper=U,signed_gap403=d,centered_P=Pup,denominator_D=Dup),
        observations=obs,assigned_charges=dict(b17_upper=b17,b19_upper=b19),
        killed19_mass_lower=m,unit_floor_mass_lower=d/483,signed_H11_slack=criterion,survival29_mass_lower=s29)
    return io,encode(out)

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[1]);p.add_argument('--source',type=Path);p.add_argument('--proof',type=Path);p.add_argument('--certificate',type=Path)
    g=p.add_mutually_exclusive_group(required=True);g.add_argument('--write',action='store_true');g.add_argument('--check',action='store_true');a=p.parse_args()
    certificate=a.certificate or a.base/DEFAULT_CERTIFICATE
    io,out=calculate(a.base,a.source or a.base/SOURCE,a.proof or a.base/DEFAULT_PROOF)
    if a.write:io.write_certificate_text(certificate,json.dumps(out,indent=2)+'\n')
    else:require(out==json.loads(io.read_artifact_bytes(certificate),object_pairs_hook=io._unique),'Complete exact through29 account regenerates')
    with localcontext() as ctx:
        ctx.prec=24
        vals={**out['through19'],'m19':out['killed19_mass_lower'],'criterion_slack':out['signed_H11_slack'],'s29':out['survival29_mass_lower']}
        for k,v in vals.items():
            q=F(v);print(k,Decimal(q.numerator)/Decimal(q.denominator))
    print('PASS complete finite high-rho survival through29')

if __name__=='__main__':main()
