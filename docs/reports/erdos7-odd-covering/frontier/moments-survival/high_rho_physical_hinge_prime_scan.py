#!/usr/bin/env python3
"""Complete-prime-power physical hinge continuation and its first stopping bound."""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from math import isqrt
from hashlib import sha256
import argparse,importlib.util,json,sys
sys.dont_write_bytecode=True
PREFIX=((11,F(5,3)),(13,F(12,7)))
INITIAL=((17,F(2)),(19,F(9,5)))
RHOS=(F(1,20),F(3,40),F(1,10))
DEFAULT_PROOF='profile-notes/321-384/331-complete-physical-hinges-continue-finite-sources-through43.md'
DEFAULT_CERTIFICATE='certificates/source_norms/moments-survival/high_rho_physical_hinge_prime_scan.json'

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

def primes(a,b):
    return [n for n in range(a,b+1) if n>1 and all(n%d for d in range(2,1+isqrt(n)))]

def calculate(base,proof):
    io=module('hingeprime_io',base/'certificate_io.py');src=module('hingeprime_src',base/'verify_joint_frontier.py')
    h330=module('hingeprime_330',base/'frontier/moments-survival/high_rho_survival_through29.py')
    parent_path=base/'certificates/source_norms/j-geometry/j_whole_face_high_rho_finite_guard.json'
    parent=json.loads(io.read_artifact_bytes(parent_path),object_pairs_hook=io._unique)
    require(parent['schema']=='erdos7-whole-j-high-rho-finite-guard-v1','Complete329 finite source contract')
    for path,pin in parent['source_sha256'].items():require(sha256(io.read_artifact_bytes(base/path)).hexdigest()==pin,'Fresh329 source '+path)
    parent_proof=base/'profile-notes/321-384/329-a-finite-whole-j-neighborhood-covers-high-surplus.md'
    parent_producer=base/'frontier/j-geometry/j_whole_face_high_rho_finite_guard.py'
    require(sha256(io.read_artifact_bytes(parent_proof)).hexdigest()==parent['ordinary_proof']['sha256']
            and sha256(io.read_artifact_bytes(parent_producer)).hexdigest()==parent['producer_sha256'],
            'Current329 ordinary proof and producer')
    whole=parent['whole_face_account'];delta=F(1,4000);scale=1+7*delta;M=F(13,20)+F(91,60)*delta
    ec=F(whole['denominator_mass_coefficient']);D=scale*F(whole['uniform_D'])+F(1,7986)*F(91,420)*delta
    P=scale*F(whole['uniform_P']);n0=F(whole['numerator_mass_coefficient']);off=F(whole['offset'])
    domains={rho:dict(S=F(3,20)+rho-F(263,360)*delta) for rho in RHOS}
    for d in domains.values():
        d['E']=ec*d['S']-D;d['J']=off+(n0*d['S']+P)/d['E'];require(d['E']>0 and d['J']<403,'One supported13 probability on each source guard')
    data=[]
    for i,j in product(range(2,5),repeat=2):
        be=tuple(F(1,4) if c==i else F(0) for c in range(5));la=tuple(F(1,72) if c==j else F(0) for c in range(5))
        data.append(((i,j),src.data(((F(1,2),F(0),F(0),F(0),F(0)),(F(0),F(1,4)),be,la,F(3,4)))))
    def observation(t,post):
        require(t.denominator==1 and t>=1,'Integer tail entrance for all odd-prime half thresholds')
        cut=int(t);atoms,tm,tf=h330.law(PREFIX+post,cut);_,pm,pf=h330.law(post,cut)
        check_atoms,tails=src.ap_product_distribution(PREFIX+post,cut)
        require(atoms==check_atoms and (tm,tf)==tails[:2],'Independent complete count law')
        floor=pf-t*pm;c=tf-t*tm;require(c>=floor>=0,'POST-only conditioning floor')
        vertices=[]
        for (i,j),dat in data:
            terms={n:p*n*src.raw357(t/n,dat) for n,p in atoms.items()}
            vertices.append(dict(beta_cell=i,late_cell=j,terms=terms,total=sum(terms.values())))
        nonlinear=max(v['total'] for v in vertices);C=scale*nonlinear+tf*M
        require(C>=0 and all(C+(c-floor)*d['S']>=0 for d in domains.values()),'Nonnegative shifted hinge numerator')
        require(ec*C+(c-floor)*D>0,'Physical hinge upper decreases with actualS')
        uppers={rho:floor+(C+(c-floor)*d['S'])/d['E'] for rho,d in domains.items()}
        return dict(threshold=t,post=post,full_factors=PREFIX+post,count_atoms=atoms,tail_mass=tm,tail_first=tf,post_floor=floor,mass_coefficient=c,vertex_payments=vertices,uniform_nonlinear=nonlinear,finite_constant=C,upper=uppers)
    rows=[];charges={rho:F(0) for rho in RHOS};post=()
    Fsum=Csum=Ksum=F(0)
    for p in (17,19,*primes(23,47)):
        t=F(8) if p in(17,19) else F(p-1,2)
        factor=F(1,p-9) if p in(17,19) else F(2,p-1)
        obs=observation(t,post)
        b={rho:factor*obs['upper'][rho] for rho in RHOS}
        for rho in RHOS:charges[rho]+=b[rho]
        mass={rho:1-charges[rho] for rho in RHOS}
        Fsum+=factor*obs['post_floor'];Csum+=factor*obs['finite_constant'];Ksum+=factor*(obs['mass_coefficient']-obs['post_floor'])
        A=(1-Fsum)*ec-Ksum;B=(1-Fsum)*D+Csum
        require(A>0 and ec*B-A*D>0,'Positive affine coefficient and increasing survivor mass lower in actualS')
        Scrit=B/A;rhocrit=Scrit-F(3,20)+F(263,360)*delta
        for rho in RHOS:
            S=domains[rho]['S'];require((A*S-B)/(ec*S-D)==mass[rho],'Exact shared-denominator cumulative identity')
        if p>=29:require(ec*Scrit-D>0,'Positive supported13 denominator at the strict continuation threshold')
        rows.append(dict(prime=p,kernel_kind='pure-base-T8' if p<23 else 'full-Haar-delta-half',charge_factor=factor,hinge=obs,charge_upper=b,cumulative_charge_upper=dict(charges),mass_lower=mass,
                         cumulative_floor=Fsum,cumulative_constant=Csum,cumulative_slope=Ksum,
                         survivor_numerator_A=A,survivor_numerator_B=B,critical_actual_mass=Scrit,critical_source_rho=rhocrit))
        print('p',p,'charge',[float(b[r]) for r in RHOS],'mass',[float(mass[r]) for r in RHOS],flush=True)
        post+=((p,F(p-1,p-9) if p in(17,19) else F(2)),)
    summary=[]
    for rho in RHOS:
        good=[r for r in rows if r['mass_lower'][rho]>0];bad=[r for r in rows if r['mass_lower'][rho]<=0]
        summary.append(dict(rho_lower=rho,last_positive_prime=good[-1]['prime'] if good else None,first_nonpositive_prime=bad[0]['prime'] if bad else None,mass_at_last_positive=good[-1]['mass_lower'][rho] if good else None,mass_at_first_nonpositive=bad[0]['mass_lower'][rho] if bad else None))
    require([(r['last_positive_prime'],r['first_nonpositive_prime']) for r in summary]==[(31,37),(37,41),(43,47)],'Exact positive-to-nonpositive boundaries')
    source_mass_max=F(1,4)+delta/2
    require(rows[-1]['critical_actual_mass']>source_mass_max,'The47 sufficient threshold exceeds the entire finite source actual-mass containing range')
    witness=parent['actual_finite_witness'];wS=F(witness['raw_mass']);wS0=F(witness['S0']);wrho=wS-wS0
    require(F(witness['delta'])<delta and wrho>max(RHOS),'Actual204-label source with inactive mixed7 meets every rho guard')
    paths=[base/'certificate_io.py',base/'verify_joint_frontier.py',parent_path,parent_proof,parent_producer,
           base/'frontier/moments-survival/high_rho_survival_through29.py',base/'profile-notes/321-384/330-a-finite-high-surplus-source-survives-through29.md',
           base/'profile-notes/257-320/302-a-positive-actual-source-neighborhood-keeps-j-below403.md',
           base/'profile-notes/257-320/311-imperfect-j-source-alignment-forces-a-sharp-sector-surplus.md',
           base/'problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md']
    pins={str(p.relative_to(base)):sha256(io.read_artifact_bytes(p)).hexdigest() for p in paths}
    proofraw=io.read_artifact_bytes(proof)
    out=dict(schema='erdos7-high-rho-physical-hinge-continuation-v1',scope='Actual finite source survival through31,37,41,43 under the displayed strict rho thresholds, source delta<=1/4000. Complete prime-power and product-law tails at every listed prime. Same supportedAP(4,5)13 law, actual pure-base17/19T8, then actual full-Haar clipped kernels with delta=1/2. All bad-charge upper bounds use their own incoming full physical law; all killed chains remain unnormalized.47 is the first bound outside the entire source actual-mass range. Nonpositive mass estimates signal failure of this sufficient bound only; no actual covering or unrestricted-prime assertion.',source_sha256=pins,
             ordinary_proof=dict(sha256=sha256(proofraw).hexdigest(),byte_count=len(proofraw)),producer_sha256=sha256(io.read_artifact_bytes(Path(__file__))).hexdigest(),
             source_delta=delta,rho_guards=RHOS,source_domains=domains,denominator_mass_coefficient=ec,denominator_constant=D,
             source_actual_mass_upper_containing=source_mass_max,rows=rows,summary=summary,
             actual_finite_witness=dict(height=witness['height'],original_label_count=witness['original_label_count'],delta=F(witness['delta']),S=wS,S0=wS0,rho=wrho,
               rule='Keep the329 original raw35 and pure7 labels and original mixed3*7^e/root0,9*7^e/cell1 carriers; replace both mixed seven cylinders by the pure7 G6,e cylinder. Every mixed class is contained in its actual pure7 exclusion, so S=s. The geometric carrier mixture and qJ are unchanged.'))
    return io,encode(out)

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2]);p.add_argument('--proof',type=Path);p.add_argument('--certificate',type=Path)
    g=p.add_mutually_exclusive_group(required=True);g.add_argument('--write',action='store_true');g.add_argument('--check',action='store_true');a=p.parse_args()
    certificate=a.certificate or a.base/DEFAULT_CERTIFICATE
    io,out=calculate(a.base,a.proof or a.base/DEFAULT_PROOF)
    if a.write:io.write_certificate_text(certificate,json.dumps(out,indent=2)+'\n')
    else:require(out==json.loads(io.read_artifact_bytes(certificate),object_pairs_hook=io._unique),'Exact complete cumulative hinge bounds regenerate')
    print('PASS bounded cumulative physical hinge account',[(r['rho_lower'],r['last_positive_prime'],r['first_nonpositive_prime']) for r in out['summary']])

if __name__=='__main__':main()
