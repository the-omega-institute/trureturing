#!/usr/bin/env python3
"""Bounded full-raw-source entry for high-rho actual aligned qJ=1 sources.

All numerical inputs are original function definitions and weights. No
survivor LP bound, mandatory deletion row, or coherent lower probe is used.
"""
from fractions import Fraction as F
from pathlib import Path
from itertools import product
from hashlib import sha256
import argparse, importlib.util, json, sys
sys.dont_write_bytecode=True
CERTIFICATE='certificates/source_norms/j-source/j_aligned_high_rho_raw_upper.json'
DEFAULT_PROOF='profile-notes/j-source/328-complete-raw-costs-cover-the-high-surplus-aligned-face.md'
INVENTORY='certificates/source_norms/j-source/j_aligned_complete_moment_comparison.json'
SOURCE_PROOFS=(
    'profile-notes/31-one-original-zero-five-layout-across-both-actual-measures.md',
    'profile-notes/42-whole-hinge-absorption-sharpens-actual-survival.md',
    'profile-notes/j-source/130-the-whole-j-face-forces-source-anti-alignment.md',
    'profile-notes/j-source/302-a-positive-actual-source-neighborhood-keeps-j-below403.md',
    'profile-notes/j-source/311-imperfect-j-source-alignment-forces-a-sharp-sector-surplus.md',
)

def require(ok,msg):
    if not ok: raise ValueError(msg)

def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    require(spec is not None and spec.loader is not None,'Readable original provider')
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod);return mod

def convert(v):
    if isinstance(v,list): return tuple(map(convert,v))
    if isinstance(v,str):
        try:return F(v)
        except ValueError:return v
    return v

def encode(v):
    if isinstance(v,F):return str(v)
    if isinstance(v,dict):return {str(k):encode(x) for k,x in v.items()}
    if isinstance(v,(tuple,list)):return [encode(x) for x in v]
    return v

def calculate(base,proof):
    io=module('highrho_io',base/'certificate_io.py')
    src=module('highrho_raw_source',base/'verify_joint_frontier.py')
    raw=io.read_artifact_bytes(base/INVENTORY)
    inv=json.loads(raw,object_pairs_hook=io._unique)
    tags=convert(inv['original_cost_tags']);weights=tuple(map(F,inv['cost_weights']))
    signed,csq,offset=[F(inv[k]) for k in ('signed_mass_coefficient','complete_square_weight','offset')]
    require(len(tags)==len(weights)==52 and min(weights)>0 and csq>0 and signed<0 and offset==src.WHOLE_CONST,'Original52 costs and signed comparison')
    count=inv['count_law'];a,b=[F(count[k]) for k in ('remaining_hinge1_coefficient','whole_constant_coefficient')]
    require((a,b)==(F(1,7986),F(1,87846)),'Complete count tail')
    probs={int(k):F(v) for k,v in count['probabilities'].items()}
    ids={int(k):{int(t):F(v) for t,v in row.items()} for k,row in count['all_load_identities'].items()}
    tp=F(count['tail_probability'])
    apco=[{t:sum(probs[n]*ids[n].get(t,0)/n for n in range(j+1,5))+(tp if t==1 else 0) for t in (1,2,3,5)} for j in range(4)]
    require(sum(sum(c.values()) for c in apco)+a==F(7,6),'Entire AP slope inventory')
    mass=F(1,4);rho0=F(3,20);target=F(403)-offset
    cost1=tuple(src.zero5_cost(t,1) for t in tags)
    for tag,f1 in zip(tags,cost1):
        degree,leading,constant,entrance=src.zero5_cost_metadata(tag)
        values=[src.zero5_cost(tag,n) for n in range(1,entrance+1)]
        require(degree in (1,2) and leading>=0 and min(values)>=f1>=0
                and all(x<=y for x,y in zip(values,values[1:]))
                and values[-1]==leading*entrance**degree+constant,
                'Every original cost is increasing from one through its complete polynomial tail')
    atone=csq+sum(w*f for w,f in zip(weights,cost1))
    n0=signed+atone
    ecoef=1-b/7
    slope=target*ecoef-n0
    require(n0>0 and slope>0,'Centered numerator and positive403 mass coefficient')
    mean=F(397,450)
    rows=[]
    for ib,il in product(range(2,5),repeat=2):
        beta=[F(0)]*5;late=[F(0)]*5
        beta[2]=F(1,5);beta[ib]+=F(1,20)
        late[2]=F(1,135);late[il]+=F(7,1080)
        par=((F(1,2),F(0),F(0),F(0),F(0)),(F(0),F(1,4)),tuple(beta),tuple(late),F(3,4))
        dat=src.data(par)
        require(dat[3]==mass and dat[4]==rho0 and min(dat[0]+dat[1])>=0,'Same qJ1 source containing vertex')
        uppers=[src.zero7_raw(tag,dat) for tag in tags]
        square=src.zero7_raw(('s',F(0)),dat)
        hinges={t:src.raw357(F(t),dat) for t in (1,2,3,4,5)}
        ap=[sum(v*hinges[t] for t,v in c.items()) for c in apco]
        generic_mean=src.zero7_raw(('h',F(0)),dat)
        require(generic_mean>=mean,'Sharper independent aligned raw mean cap is relevant')
        centered_costs=[u-f*mass for u,f in zip(uppers,cost1)]
        require(min(centered_costs)>=0 and square>=mass,'Nonnegative centered raw observations')
        payments=[w*u for w,u in zip(weights,centered_costs)]
        numerator_constant=sum(payments)+csq*(square-mass)
        denominator_constant=hinges[4]/6+(sum(ap)+a*(mean-mass))/7
        threshold=(target*denominator_constant+numerator_constant)/slope
        N=n0*mass+numerator_constant;E=ecoef*mass-denominator_constant
        margin=slope*mass-target*denominator_constant-numerator_constant
        ledger=[{'name':'cost-'+str(i),'raw_upper':uppers[i],'centered_upper':centered_costs[i],'403_margin_cost':p} for i,p in enumerate(payments)]
        ledger += [{'name':'square','raw_upper':square,'centered_upper':square-mass,'403_margin_cost':csq*(square-mass)},
                   {'name':'hinge4','raw_upper':hinges[4],'403_margin_cost':target*hinges[4]/6}]
        ledger += [{'name':'AP11-'+str(j),'raw_upper':ap[j],'403_margin_cost':target*ap[j]/7} for j in range(4)]
        ledger += [{'name':'mean-tail','raw_upper':mean,'403_margin_cost':target*a*(mean-mass)/7}]
        row=dict(beta_extra_cell=ib,late_extra_cell=il,parameters=par,raw_59=dict(costs=uppers,square=square,mean=mean,generic_mean=generic_mean,hinge4=hinges[4],AP11=ap),numerator_constant=numerator_constant,denominator_constant=denominator_constant,mass_threshold=threshold,rho_threshold=threshold-rho0,no_deletion=dict(N_upper=N,E_lower=E,margin403_lower=margin,J_upper=offset+N/E if E>0 else None),payments=sorted(ledger,key=lambda r:r['403_margin_cost'],reverse=True))
        rows.append(row)
        print('vertex',ib,il,'rho_threshold',float(threshold-rho0),'J',float(offset+N/E) if E>0 else None,flush=True)
    worst=max(rows,key=lambda r:r['mass_threshold'])
    pmax=max(r['numerator_constant'] for r in rows)
    dmax=max(r['denominator_constant'] for r in rows)
    estar=ecoef*worst['mass_threshold']-dmax
    require(estar>0 and worst['mass_threshold']<mass,'Positive denominator throughout the nonempty high-rho interval')
    guard=F(61,2500);smass=rho0+guard
    nguard=n0*smass+pmax;eguard=ecoef*smass-dmax
    guardmargin=target*eguard-nguard
    require(guard>worst['rho_threshold'] and eguard>0 and guardmargin>0
            and pmax>0 and dmax>0 and n0*dmax+ecoef*pmax>0,
            'Strict simple guard and decreasing valid uniform ratio upper')
    require(len(rows)==9 and all(len(r['raw_59']['costs'])==52 and len(r['raw_59']['AP11'])==4 for r in rows),
            'Exactly nine full59-target raw vertex accounts')
    files=('certificate_io.py','verify_joint_frontier.py',INVENTORY,*SOURCE_PROOFS)
    pins={p:sha256(io.read_artifact_bytes(base/p)).hexdigest() for p in files}
    proof_raw=io.read_artifact_bytes(proof)
    producer=sha256(io.read_artifact_bytes(Path(__file__))).hexdigest()
    return io,encode(dict(schema='erdos7-aligned-high-rho-raw-upper-v1',scope='Actual countable-label qJ=1 aligned source containing beta=1/5 e_L+1/20 simplex and late=1/135 e_L+7/1080 simplex. All original raw source cost operators; no survivor LP rows, no deletion credit except exact at-one centering. Nine-vertex interpolation of separately convex raw operators, complete exponent and count tails. rho equal to the exact threshold gives J<=403; strictly larger rho gives J<403. No finite actual source attains qJ=1; no numerical off-face neighborhood is supplied.',source_sha256=pins,ordinary_proof={'sha256':sha256(proof_raw).hexdigest(),'byte_count':len(proof_raw)},producer_sha256=producer,actual_mass_interval=(F(413,2700),mass),target_offset=offset,original_cost_tags=tags,cost_weights=weights,costs_at_one=cost1,original_signed_mass_coefficient=signed,original_square_weight=csq,count_law=count,centered_numerator_mass_coefficient=n0,denominator_mass_coefficient=ecoef,positive403_mass_coefficient=slope,aligned_raw_mean_upper=mean,rows=rows,uniform_mass_threshold=worst['mass_threshold'],uniform_rho_threshold=worst['rho_threshold'],controlling_vertices=[(r['beta_extra_cell'],r['late_extra_cell']) for r in rows if r['mass_threshold']==worst['mass_threshold']],uniform_numerator_constant=pmax,uniform_denominator_constant=dmax,denominator_lower_at_exact_threshold=estar,simple_strict_guard=dict(rho=guard,S=smass,N_upper=nguard,E_lower=eguard,margin403_lower=guardmargin,J_upper=offset+nguard/eguard),covers_high_rho=True))

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    parser.add_argument('--certificate',type=Path)
    parser.add_argument('--proof',type=Path,help='Default: --base/'+DEFAULT_PROOF)
    mode=parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write',action='store_true');mode.add_argument('--check',action='store_true')
    args=parser.parse_args()
    path=args.certificate or args.base/CERTIFICATE
    io,out=calculate(args.base,args.proof or args.base/DEFAULT_PROOF)
    if args.check:
        require(out==json.loads(io.read_artifact_bytes(path),object_pairs_hook=io._unique),'Exact full raw result regenerates')
    else:io.write_certificate_text(path,json.dumps(out,indent=2)+'\n')
    print('PASS raw arithmetic; high-rho coverage:',out['covers_high_rho'],'threshold',float(F(out['uniform_rho_threshold'])))

if __name__=='__main__':main()
