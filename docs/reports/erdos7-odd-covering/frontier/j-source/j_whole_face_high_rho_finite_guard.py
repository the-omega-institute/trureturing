#!/usr/bin/env python3
"""Exact finite whole-J-face guard from the complete raw nine-point account."""
from fractions import Fraction as F
from pathlib import Path
from hashlib import sha256
from decimal import Decimal, localcontext
import argparse, importlib.util, json, sys
from itertools import product
sys.dont_write_bytecode = True
DEFAULT_PROOF='profile-notes/j-source/329-a-finite-whole-j-neighborhood-covers-high-surplus.md'
DEFAULT_CERTIFICATE='certificates/source_norms/j-source/j_whole_face_high_rho_finite_guard.json'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def module(name, path):
    spec=importlib.util.spec_from_file_location(name,path)
    require(spec is not None and spec.loader is not None,'Readable source provider')
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    return mod


def encode(v):
    if isinstance(v,F):return str(v)
    if isinstance(v,dict):return {str(k):encode(w) for k,w in v.items()}
    if isinstance(v,(tuple,list)):return [encode(w) for w in v]
    return v


def convert(v):
    if isinstance(v,list):return tuple(map(convert,v))
    if isinstance(v,str):
        try:return F(v)
        except ValueError:return v
    return v

def whole_face_account(base,io,src):
    inv=json.loads(io.read_artifact_bytes(base/'certificates/source_norms/j-source/j_aligned_complete_moment_comparison.json'),object_pairs_hook=io._unique)
    tags=convert(inv['original_cost_tags']);weights=list(map(F,inv['cost_weights']));cost1=[src.zero5_cost(t,1) for t in tags]
    cS,cQ,off=[F(inv[k]) for k in ('signed_mass_coefficient','complete_square_weight','offset')]
    k=403-off;s=F(1,4);S0=F(3,20);M=F(9,10)
    cnt=inv['count_law'];alpha,beta=F(cnt['remaining_hinge1_coefficient']),F(cnt['whole_constant_coefficient'])
    probs={int(n):F(v) for n,v in cnt['probabilities'].items()};ids={int(n):{int(t):F(v) for t,v in row.items()} for n,row in cnt['all_load_identities'].items()};tp=F(cnt['tail_probability'])
    apco=[{t:sum(probs[n]*ids[n].get(t,0)/n for n in range(j+1,5))+(tp if t==1 else 0) for t in (1,2,3,5)} for j in range(4)]
    n0=cS+cQ+sum(w*v for w,v in zip(weights,cost1));ec=1-beta/7;L=k*ec-n0
    require(L>0 and n0>0 and sum(sum(c.values()) for c in apco)+alpha==F(7,6),'Same centered complete comparison')
    rows=[]
    for ib,il in product(range(2,5),repeat=2):
        be=tuple(F(1,4) if i==ib else F(0) for i in range(5));la=tuple(F(1,72) if i==il else F(0) for i in range(5))
        par=((F(1,2),F(0),F(0),F(0),F(0)),(F(0),F(1,4)),be,la,F(3,4));dat=src.data(par)
        require(dat[3:]==(s,S0),'Full original J vertex source')
        costs=[src.zero7_raw(tag,dat) for tag in tags];sq=src.square357(F(0),dat);h={t:src.raw357(F(t),dat) for t in (1,2,3,4,5)}
        mean=src.raw357(F(0),dat);require(mean==M,'Generic complete raw mean; no alignment gain')
        ap=[sum(v*h[t] for t,v in c.items()) for c in apco]
        P=sum(w*(u-v*s) for w,u,v in zip(weights,costs,cost1))+cQ*(sq-s)
        D=h[4]/6+(sum(ap)+alpha*(M-s))/7
        threshold=(k*D+P)/L;N=n0*s+P;E=ec*s-D
        rows.append(dict(beta_cell=ib,late_cell=il,raw59=dict(costs=costs,square=sq,hinge4=h[4],AP11=ap,mean=M),P=P,D=D,mass_threshold=threshold,rho_threshold=threshold-S0,no_deletion_J_upper=off+N/E))
        print('fullJ vertex',ib,il,'rho_threshold',float(threshold-S0),'Jfull',float(off+N/E),flush=True)
    Sstar=max(r['mass_threshold'] for r in rows);Pmax=max(r['P'] for r in rows);Dmax=max(r['D'] for r in rows);Estar=ec*Sstar-Dmax
    require(Estar>0 and Sstar<s,'Positive nonempty whole-face high-rho region')
    out=dict(scope='Actual countable qJ=1 face, either orientation, with entire independent root1 beta/late simplexes. No alignment or literal135 cap improvement is used; generic raw mean9/10. Original complete raw operators and exact at-one centering only. No survivor LP, finite-qJ neighborhood, or optimality assertion.',rows=rows,positive_mass_coefficient=L,numerator_mass_coefficient=n0,denominator_mass_coefficient=ec,offset=off,uniform_mass_threshold=Sstar,uniform_rho_threshold=Sstar-S0,uniform_P=Pmax,uniform_D=Dmax,E_at_threshold=Estar)
    return encode(out)


def calculate(base,proof):
    io=module('highrho_finite_io',base/'certificate_io.py')
    src=module('whole_guard_source',base/'verify_joint_frontier.py')
    old=whole_face_account(base,io,src)
    require(len(old['rows'])==9,'Whole original qJ1 face nine-point inventory')
    k=403-F(old['offset'])
    n0=F(old['numerator_mass_coefficient'])
    ec=F(old['denominator_mass_coefficient'])
    L=F(old['positive_mass_coefficient'])
    P=F(old['uniform_P']);D=F(old['uniform_D'])
    star=F(old['uniform_mass_threshold'])
    require(k*D+P==L*star and min(n0,ec,L,P,D)>0,'Same complete positive403 account')
    a=F(1,7986)
    require(F(9,10)-F(1,4)==F(13,20),'Centered whole-face generic raw mean')
    require(F(1,10)+F(83,60)==F(89,60)<F(91,60),'Generic mean-cap error with no135 credit')
    require(F(1,2)+F(83,360)==F(263,360),'Same actual lower-mass error')
    minm=(F(1,2)-F(1,4))/9-F(1,72)
    # The smallest whole-face containing cell uses beta=1/4 and late=1/72.
    require(minm==F(1,72) and F(7,72)/minm==7,'Mass envelope and domination factor')
    guard=F(1,4000);rho=F(1,40);scale=1+7*guard
    Smin=F(3,20)+rho-F(263,360)*guard
    Pup=scale*P;Dup=scale*D+a*F(91,420)*guard
    E=ec*Smin-Dup;N=n0*Smin+Pup;margin=k*E-N
    J=F(old['offset'])+N/E
    price=L*F(263,360)+7*(k*D+P)+k*a*F(91,420)
    gap0=L*(F(3,20)+rho)-(k*D+P)
    require(margin==gap0-price*guard and E>F('0.0994684')
            and margin>F('0.0539') and J<F('402.459'),
            'Explicit positive finite-source403 guard')
    require(n0*Dup+ec*Pup>0,'Uniform ratio decreases at every larger actual mass')
    src=module('highrho_finite_raw',base/'verify_joint_frontier.py')
    Nheight=12;t=(1-F(1,3**(Nheight-2)))/18;q=(1-F(1,5**Nheight))/4;v=F(1,7**Nheight)
    par=((9*t,F(0),F(0),F(0),F(0)),(F(0),q),
         (F(0),F(0),F(1,5),q-F(1,5),F(0)),
         (F(0),F(0),F(1,135),F(0),t*q-F(1,135)),1-q)
    avail,n,pure,s,Dsource=src.data(par)
    T2=(max(avail)/18+(sum(pure)+max(pure[0]+pure[1],sum(pure[2:]))+max(pure))/4+F(1,72))/5
    carrier=n[0]+2*n[1]
    S0=s-T2-(1-v)*carrier/5
    Sw=s-(1-v)*carrier/(5+v)
    rhow=Sw-S0
    deltaw=1-(1-F(1,3**(Nheight-2)))**2*(1-F(1,5**Nheight))**4*(1-v)
    require(0<deltaw<guard and rhow>rho and Sw>0,
            'Existing311 raw family plus only3/9 mixed7 gives an actual finite guard witness')
    paths=('certificate_io.py','verify_joint_frontier.py',
           'profile-notes/71-global-j-k-control-faces-and-exact-escape-gaps.md',
           'profile-notes/136-a-whole-j-source-neighborhood-has-a-complete-labelwise-bound.md',
           'profile-notes/j-source/311-imperfect-j-source-alignment-forces-a-sharp-sector-surplus.md',
           'profile-notes/31-one-original-zero-five-layout-across-both-actual-measures.md',
           'profile-notes/42-whole-hinge-absorption-sharpens-actual-survival.md',
           'profile-notes/j-source/130-the-whole-j-face-forces-source-anti-alignment.md',
           'profile-notes/j-source/302-a-positive-actual-source-neighborhood-keeps-j-below403.md',
           'certificates/source_norms/j-source/j_aligned_complete_moment_comparison.json')
    pins={p:sha256(io.read_artifact_bytes(base/p)).hexdigest() for p in paths}
    proof_raw=io.read_artifact_bytes(proof)
    result=dict(schema='erdos7-whole-j-high-rho-finite-guard-v1',source_sha256=pins,
        ordinary_proof={'sha256':sha256(proof_raw).hexdigest(),'byte_count':len(proof_raw)},
        producer_sha256=sha256(io.read_artifact_bytes(Path(__file__))).hexdigest(),
        whole_face_account=old,
        scope='Actual finite effective9 source near either whole qJ face; no45/135 alignment, small-rho premise, survivor LP row, global source join, or later-prime claim.',
        parameter_errors=dict(root1_beta_completion=guard/4,root1_late_completion=guard/72,
            root1_mass_upward_per_cell=7*guard/72,availability_factor=1+3*guard,
            pure_factor=1+guard,common_centered_operator_factor=scale,
            s_absolute=guard/2,cap_absolute=83*guard/72,
            S0_lower_error=263*guard/360,centered_mean_upward_error=91*guard/60),
        guard=dict(qJ_lower=1-guard,delta_upper=guard,rho_lower=rho,S_lower=Smin),
        upper_account=dict(centered_P=Pup,denominator_D=Dup,N_upper=N,E_lower=E,
            margin403_lower=margin,J_upper=J,delta_price=price,margin_at_delta_zero=gap0,
            maximum_delta_from_this_margin=gap0/price),
        actual_finite_witness=dict(height=Nheight,raw_parameters=par,original_label_count=(Nheight+1)**2-1+3*Nheight,
            raw_mass=s,T2=T2,carrier_union_raw_mass=carrier,carrier_empty_weight=v,
            delta=deltaw,S=Sw,S0=S0,rho=rhow,
            rule='Use311 original raw35 labels and pure7 class6, retaining only mixed7 old cofactors3(root0,class1) and9(cell1,class2); all other mixed7 labels absent.'))
    return io,encode(result)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    p.add_argument('--proof',type=Path)
    p.add_argument('--certificate',type=Path)
    modes=p.add_mutually_exclusive_group(required=True)
    modes.add_argument('--write',action='store_true');modes.add_argument('--check',action='store_true')
    args=p.parse_args()
    certificate=args.certificate or args.base/DEFAULT_CERTIFICATE
    io,out=calculate(args.base,args.proof or args.base/DEFAULT_PROOF)
    if args.write:io.write_certificate_text(certificate,json.dumps(out,indent=2)+'\n')
    else:require(out==json.loads(io.read_artifact_bytes(certificate),object_pairs_hook=io._unique),'Exact finite guard replay')
    with localcontext() as ctx:
        ctx.prec=22
        for key in ('E_lower','margin403_lower','J_upper','maximum_delta_from_this_margin'):
            value=F(out['upper_account'][key]);print(key,Decimal(value.numerator)/Decimal(value.denominator))
    print('PASS finite high-rho raw guard and nonempty actual witness; no new source scan or LP')


if __name__=='__main__':main()
