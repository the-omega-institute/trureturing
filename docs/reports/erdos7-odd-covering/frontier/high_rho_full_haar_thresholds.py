#!/usr/bin/env python3
"""Exact same-source full-Haar threshold account through43 and its47 deficit."""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from hashlib import sha256
from decimal import Decimal,localcontext
import argparse,importlib.util,json,sys
sys.dont_write_bytecode=True
DEFAULT_PROOF='profile-notes/333-variable-full-haar-thresholds-retain-more-survivor-mass.md'
DEFAULT_CERTIFICATE='certificates/source_norms/high_rho_full_haar_thresholds.json'
DEFAULT_SOURCE='certificates/source_norms/j_whole_face_high_rho_finite_guard.json'
REFERENCE='certificates/source_norms/high_rho_physical_hinge_prime_scan.json'
PREFIX=((11,F(5,3)),(13,F(12,7)))
SCHEDULE=((17,6),(19,6),(23,8),(29,12),(31,12),(37,16),(41,18),(43,24),(47,24))

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
        require(p>1 and 0<=c<=p,'Nonnegative full comparison count law')
        nxt={}
        for n,pn in atoms.items():
            for v in range(1,(cut-1)//n+1):
                q=1-c/p if v==1 else c*F(p-1,p**v)
                nxt[n*v]=nxt.get(n*v,F(0))+pn*q
        atoms=nxt;mean*=1+c/F(p-1)
    tm=1-sum(atoms.values());tf=mean-sum(n*p for n,p in atoms.items())
    require(all(q>=0 for q in atoms.values()) and tm>=0 and tf>=cut*tm,
            'Complete probability and first-moment tail')
    return atoms,tm,tf

def calculate(base,source,proof):
    io=module('threshold_io',base/'certificate_io.py')
    src=module('threshold_raw',base/'verify_joint_frontier.py')
    read=lambda p:json.loads(io.read_artifact_bytes(p),object_pairs_hook=io._unique)
    parent=read(source)
    require(parent['schema']=='erdos7-whole-j-high-rho-finite-guard-v1','Established329 source contract')
    source_proof=base/'profile-notes/329-a-finite-whole-j-neighborhood-covers-high-surplus.md'
    source_producer=base/'frontier/j_whole_face_high_rho_finite_guard.py'
    reference_path=base/REFERENCE;reference=read(reference_path)
    require(reference['schema']=='erdos7-high-rho-physical-hinge-continuation-v1','Established331 reference contract')
    reference_proof=base/'profile-notes/331-complete-physical-hinges-continue-finite-sources-through43.md'
    reference_producer=base/'frontier/high_rho_physical_hinge_prime_scan.py'
    for obj,pdoc,pprod in ((parent,source_proof,source_producer),(reference,reference_proof,reference_producer)):
        for path,pin in obj['source_sha256'].items():
            require(sha256(io.read_artifact_bytes(base/path)).hexdigest()==pin,'Current inherited source '+path)
        require(sha256(io.read_artifact_bytes(pdoc)).hexdigest()==obj['ordinary_proof']['sha256']
                and sha256(io.read_artifact_bytes(pprod)).hexdigest()==obj['producer_sha256'],
                'Current inherited ordinary proof and producer')
    w=parent['whole_face_account'];delta=F(1,4000);rho=F(1,10);scale=1+7*delta
    require(F(parent['guard']['delta_upper'])==delta
            and F(parent['parameter_errors']['common_centered_operator_factor'])==scale
            and F(parent['parameter_errors']['S0_lower_error'])==F(263,360)*delta
            and F(parent['parameter_errors']['centered_mean_upward_error'])==F(91,60)*delta,
            'Exact finite-source error constants')
    require(len(w['rows'])==9,'Full containing source face')
    ec=F(w['denominator_mass_coefficient'])
    D=scale*F(w['uniform_D'])+F(1,7986)*F(91,420)*delta
    S=F(3,20)+rho-F(263,360)*delta;E=ec*S-D;M=F(13,20)+F(91,60)*delta
    require(E>0 and ec>0 and D>0,'One positive supported13 denominator')
    data=[]
    for i,j in product(range(2,5),repeat=2):
        beta=tuple(F(1,4) if k==i else F(0) for k in range(5))
        late=tuple(F(1,72) if k==j else F(0) for k in range(5))
        dat=src.data(((F(1,2),F(0),F(0),F(0),F(0)),(F(0),F(1,4)),beta,late,F(3,4)))
        require(dat[3:]==(F(1,4),F(3,20)),'Original whole-face containing vertex')
        data.append(((i,j),dat))
    rows=[];post=();total=F(0);Fsum=Csum=Ksum=F(0)
    for p,threshold in SCHEDULE:
        t=F(threshold);clip=t/(p-1);cap=F(p-1,p-1-threshold);factor=1/(p-1-t)
        require(0<clip<1 and cap==1/(1-clip) and cap<=p,
                'Actual normalized clipped kernel and admissible count cap')
        atoms,tm,tf=law(PREFIX+post,threshold);_,pm,pf=law(post,threshold)
        check_atoms,tails=src.ap_product_distribution(PREFIX+post,threshold)
        require(atoms==check_atoms and (tm,tf)==tails[:2],'Independent complete count-tail reconstruction')
        floor=pf-t*pm;c=tf-t*tm
        require(c>=floor>=0,'Post-only floor before the sole13 conditioning')
        vertices=[]
        for (i,j),dat in data:
            terms={n:q*n*src.raw357(t/n,dat) for n,q in atoms.items()}
            vertices.append(dict(beta_cell=i,late_cell=j,terms=terms,total=sum(terms.values())))
        nonlinear=max(v['total'] for v in vertices);C=scale*nonlinear+tf*M
        shifted=C+(c-floor)*S
        require(C>=0 and shifted>=0 and ec*C+(c-floor)*D>0,
                'Safe denominator substitution and decreasing hinge bound in actualS')
        H=floor+shifted/E;b=factor*H;total+=b;mass=1-total
        Fsum+=factor*floor;Csum+=factor*C;Ksum+=factor*(c-floor)
        A=(1-Fsum)*ec-Ksum;B=(1-Fsum)*D+Csum
        require(mass==(A*S-B)/E and ec*B-A*D>0,
                'Exact cumulative account and increasing mass lower in actualS')
        rows.append(dict(prime=p,threshold=t,clip_delta=clip,cap=cap,charge_factor=factor,
                         incoming_post_factors=post,full_factors=PREFIX+post,count_atoms=atoms,
                         tail_mass=tm,tail_first=tf,post_floor=floor,mass_coefficient=c,
                         vertex_payments=vertices,uniform_nonlinear=nonlinear,finite_constant=C,
                         hinge_upper=H,charge_upper=b,cumulative_charge_upper=total,mass_lower=mass,
                         survivor_numerator_A=A,survivor_numerator_B=B))
        post+=((p,cap),)
    byp={r['prime']:r for r in rows};m43=byp[43]['mass_lower'];m47=byp[47]['mass_lower'];deficit=-m47
    old43=next(r for r in reference['rows'] if r['prime']==43)
    oldmass=F(old43['mass_lower']['1/10'])
    require(m43>F('0.0560177338142069')>oldmass>0 and m47<0,
            'Strict improved43 lower and positive47 correction budget')
    require(F('0.014122793520217785')<deficit<F('0.014122793520217786'),
            'Outward rational bracket on the47 deficit')
    witness=reference['actual_finite_witness']
    require(F(witness['delta'])<delta and F(witness['rho'])>rho
            and F(witness['S'])-F(witness['S0'])==F(witness['rho']),
            'Existing finite actual source belongs to this guard')
    paths=[base/'certificate_io.py',base/'verify_joint_frontier.py',source,source_proof,source_producer,
           reference_path,reference_proof,reference_producer,
           base/'profile-notes/16-a-common-dual-test-law-for-redistributing-charged-bad-mass.md',
           base/'profile-notes/330-a-finite-high-surplus-source-survives-through29.md',
           base/'problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md']
    def key(p):
        try:return str(p.resolve().relative_to(base.resolve()))
        except ValueError:return str(p.resolve())
    pins={key(p):sha256(io.read_artifact_bytes(p)).hexdigest() for p in paths}
    raw=io.read_artifact_bytes(proof)
    out=dict(schema='erdos7-high-rho-full-haar-thresholds-v1',
             scope='One finite effective9 source qJ>=1-1/4000,rho>=1/10, both orientations and arbitrary45/135 arrangement. Same supportedAP11/T4-AP13/T5 law; every later kernel full-Haar with the fixed listed threshold. Complete original own labels, residues and prime-power heights; unnormalized killed chains. Positive survival through43;47 remains an explicit correction budget, not a survival or optimum claim.',
             source_sha256=pins,ordinary_proof=dict(sha256=sha256(raw).hexdigest(),byte_count=len(raw)),
             producer_sha256=sha256(io.read_artifact_bytes(Path(__file__))).hexdigest(),
             guard=dict(delta_upper=delta,rho_lower=rho,S_lower=S,E_lower=E,centered_mean_upper=M,centered_operator_factor=scale),
             denominator_mass_coefficient=ec,denominator_constant=D,schedule=SCHEDULE,rows=rows,
             survival43_mass_lower=m43,reference331_mass43_lower=oldmass,improvement43=m43-oldmass,
             mass47_lower=m47,overlap_correction47_required_strictly_greater_than=deficit,
             deficit47_outward_interval=(F('0.014122793520217785'),F('0.014122793520217786')),
             actual_finite_witness=witness)
    return io,encode(out)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[1]);p.add_argument('--source',type=Path)
    p.add_argument('--proof',type=Path);p.add_argument('--certificate',type=Path)
    g=p.add_mutually_exclusive_group(required=True);g.add_argument('--write',action='store_true');g.add_argument('--check',action='store_true')
    a=p.parse_args();cert=a.certificate or a.base/DEFAULT_CERTIFICATE
    io,out=calculate(a.base,a.source or a.base/DEFAULT_SOURCE,a.proof or a.base/DEFAULT_PROOF)
    if a.write:io.write_certificate_text(cert,json.dumps(out,indent=2)+'\n')
    else:require(out==json.loads(io.read_artifact_bytes(cert),object_pairs_hook=io._unique),'Complete exact threshold account regenerates')
    with localcontext() as ctx:
        ctx.prec=28
        for key in ('survival43_mass_lower','reference331_mass43_lower','mass47_lower','overlap_correction47_required_strictly_greater_than'):
            q=F(out[key]);print(key,Decimal(q.numerator)/Decimal(q.denominator))
    print('PASS complete same-source full-Haar threshold account')

if __name__=='__main__':main()
