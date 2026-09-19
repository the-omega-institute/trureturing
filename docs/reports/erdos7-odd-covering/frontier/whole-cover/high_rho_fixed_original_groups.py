#!/usr/bin/env python3
"""Complete fixed-group original-label account on the unchanged333 chain."""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import prod
from hashlib import sha256
from decimal import Decimal,localcontext
import argparse,importlib.util,json,sys,time
sys.dont_write_bytecode=True
DEFAULT_SOURCE='certificates/source_norms/high_rho_full_haar_thresholds.json'
DEFAULT_REFERENCE='certificates/source_norms/high_rho_original_ap_blocks.json'
DEFAULT_PROOF='profile-notes/whole-cover/337-fixed-original-groups-retain-the-complete-count-law.md'
DEFAULT_CERTIFICATE='certificates/source_norms/high_rho_fixed_original_groups.json'
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
    if isinstance(v,(tuple,list)):return [encode(x) for x in v]
    return v

def probability(p,c,n):
    return 1-c/p if n==1 else c*F(p-1,p**n)

def law(factors,cut):
    require(cut>=2,'Positive integer cutoff above the unit')
    atoms={1:F(1)};mean=F(1)
    for p,c in factors:
        require(p>1 and 0<=c<=p,'Nonnegative normalized geometric comparison count')
        nxt={}
        for a,m in atoms.items():
            for n in range(1,(cut-1)//a+1):
                nxt[a*n]=nxt.get(a*n,F(0))+m*probability(p,c,n)
        atoms=nxt;mean*=1+c/F(p-1)
    tm=1-sum(atoms.values());tf=mean-sum(n*q for n,q in atoms.items())
    require(all(q>=0 for q in atoms.values()) and tm>=0 and tf>=cut*tm,'Complete count tails')
    return atoms,tm,tf,mean

def original_tuples(dim,budget,prefix=()):
    """Exactly prod(e_i+1)<=budget; the remaining product budget bounds each step."""
    if dim==0:
        yield prefix;return
    for n in range(1,budget+1):
        yield from original_tuples(dim-1,budget//n,prefix+(n-1,))

@lru_cache(None)
def tuple_count(dim,budget):
    if dim==0:return 1
    return sum(tuple_count(dim-1,budget//n) for n in range(1,budget+1))

def fixed_group_centered(src,group,r,data):
    """B_theta of all original group costs; complete finite/active tails, r>1."""
    require(r>1,'Centered fixed-group threshold above one')
    cut=src.ceilq(r);atoms,tm,tf,mean=law(group,cut)
    check,tails=src.ap_product_distribution(group,cut)
    require(atoms==check and (tm,tf)==tails[:2],'Independent complete group law')
    qtables=[{n:probability(p,c,n) for n in range(1,cut)} for p,c in group]
    values=[F(0)]*len(data);active_sum=F(0);coverage={n:F(0) for n in atoms}
    seen=0;finite_terms=0;zero_active=0;digest=sha256()
    for es in original_tuples(len(group),cut-1):
        seen+=1
        active=prod(F(1) if e==0 else c/F(p**e) for (p,c),e in zip(group,es))
        finite={};suffix=[1]*(len(group)+1)
        for j in range(len(group)-1,-1,-1):suffix[j]=suffix[j+1]*(es[j]+1)
        def rec(j,n,q):
            if j==len(group):
                finite[n]=finite.get(n,F(0))+q;return
            for v in range(es[j]+1,(cut-1)//(n*suffix[j+1])+1):
                rec(j+1,n*v,q*qtables[j][v])
        rec(0,1,F(1));tail=active-sum(finite.values())
        require(tail>=0 and all(q>=0 for q in finite.values()),'Complete original-tuple active tail')
        weights=tuple([(r/n,q) for n,q in sorted(finite.items()) if q]+([(F(1),tail)] if tail else []))
        require(sum(q for _,q in weights)==active and all(h>=1 and q>0 for h,q in weights),
                'Nonnegative convex cost with zero value at one')
        if active:
            for i,dat in enumerate(data):values[i]+=src.w357(weights,1,dat)
        else:
            zero_active+=1;require(not weights,'Zero-active tuple has no cost')
        for n,q in finite.items():coverage[n]+=q
        active_sum+=active;finite_terms+=sum(q>0 for q in finite.values())
        digest.update((json.dumps(encode((es,finite,active,tail)),sort_keys=True,separators=(',',':'))+'\n').encode())
    require(seen==tuple_count(len(group),cut-1),'Complete recursive original-tuple enumeration')
    require(all(coverage[n]==n*q for n,q in atoms.items()),'Every finite count outcome retains all its original labels')
    outside=mean-active_sum;require(outside>=0,'Complete omitted original-label coefficient')
    for i,dat in enumerate(data):
        source_mean=src.raw357(F(0),dat)-dat[3]
        require(source_mean==F(13,20),'Established exact-face centered mean')
        values[i]+=outside*source_mean
    return dict(group_factors=group,threshold=r,cutoff=cut,tuple_count=seen,
                zero_active_tuples=zero_active,finite_active_terms=finite_terms,
                count_atoms=atoms,tail_mass=tm,tail_first=tf,mean=mean,
                active_mass_sum=active_sum,outside_active_mass=outside,
                finite_label_coverage=coverage,tuple_inventory_sha256=digest.hexdigest(),
                centered_vertex_values=values)

def calculate(base,source,reference,proof):
    io=module('fixedgroup_io',base/'certificate_io.py');src=module('fixedgroup_raw',base/'verify_joint_frontier.py')
    read=lambda p:json.loads(io.read_artifact_bytes(p),object_pairs_hook=io._unique)
    parent=read(source);ref=read(reference)
    require(parent['schema']=='erdos7-high-rho-full-haar-thresholds-v1'
            and ref['schema']=='erdos7-high-rho-original-ap-blocks-v1','Established333 and335 contracts')
    parent_proof=base/'profile-notes/whole-cover/333-variable-full-haar-thresholds-retain-more-survivor-mass.md'
    parent_producer=base/'frontier/whole-cover/high_rho_full_haar_thresholds.py'
    reference_proof=base/'profile-notes/whole-cover/335-original-ap-blocks-sharpen-the-fixed-full-haar-account.md'
    reference_producer=base/'frontier/whole-cover/high_rho_original_ap_blocks.py'
    for obj,pdoc,pprod in ((parent,parent_proof,parent_producer),(ref,reference_proof,reference_producer)):
        for path,pin in obj['source_sha256'].items():
            require(sha256(io.read_artifact_bytes(base/path)).hexdigest()==pin,'Current inherited source '+path)
        require(sha256(io.read_artifact_bytes(pdoc)).hexdigest()==obj['ordinary_proof']['sha256']
                and sha256(io.read_artifact_bytes(pprod)).hexdigest()==obj['producer_sha256'],
                'Current inherited ordinary proof and producer')
    require(parent['guard']==ref['guard'] and parent['schedule']==ref['schedule'],'Identical source guard and physical chain')
    g=parent['guard'];S=F(g['S_lower']);E=F(g['E_lower']);scale=F(g['centered_operator_factor'])
    ec=F(parent['denominator_mass_coefficient']);D=F(parent['denominator_constant'])
    require(F(g['delta_upper'])==F(1,4000) and F(g['rho_lower'])==F(1,10)
            and E==ec*S-D and E>0,'Same finite source and sole13 denominator')
    data=[]
    for i,j in product(range(2,5),repeat=2):
        be=tuple(F(1,4) if k==i else F(0) for k in range(5));la=tuple(F(1,72) if k==j else F(0) for k in range(5))
        dat=src.data(((F(1,2),F(0),F(0),F(0),F(0)),(F(0),F(1,4)),be,la,F(3,4)))
        require(dat[3:]==(F(1,4),F(3,20)),'Whole source-face vertex')
        data.append(dat)
    references={r['prime']:r for r in ref['rows']};rows=[];post=();total=F(0);minimum_total=F(0)
    for old in parent['rows']:
        p=old['prime'];t=F(old['threshold']);cap=F(old['cap']);cut=int(t);group=PREFIX+post
        require(t.denominator==1 and t==F(references[p]['threshold'])
                and tuple((q,F(c)) for q,c in old['incoming_post_factors'])==post,
                'Same incoming physical law and fixed threshold')
        info=fixed_group_centered(src,group,t,data)
        _,pm,pf,_=law(post,cut);floor=pf-t*pm
        c=info['tail_first']-t*info['tail_mass']
        require(c==F(old['mass_coefficient']) and floor==F(old['post_floor']) and c>=floor>=0,
                'Full mass term and POST-only conditioning floor unchanged')
        if p==17:
            require(all(v==src.raw_ap_hinge(t,PREFIX,dat)-F(1,4)*c
                        for v,dat in zip(info['centered_vertex_values'],data)),
                    'Two-factor specialization equals the existing original-AP API')
        C=scale*max(info['centered_vertex_values']);shift=C+(c-floor)*S
        require(shift>=0 and ec*C+(c-floor)*D>0,'Safe sole13 normalization and source-mass monotonicity')
        H=floor+shift/E;b=H/(p-1-t);total+=b
        choices={'all_prior':b,'333':F(old['charge_upper']),'335':F(references[p]['charge_upper'])}
        minimum=min(choices.values());minimum_total+=minimum
        rows.append(dict(prime=p,threshold=t,clip_delta=t/(p-1),cap=cap,incoming_post_factors=post,
                         fixed_group=info,post_floor=floor,mass_coefficient=c,centered_constant=C,
                         hinge_upper=H,charge_upper=b,cumulative_charge_upper=total,mass_lower=1-total,
                         same_chain_charge_choices=choices,minimum_charge=minimum,
                         minimizing_sources=tuple(k for k,v in choices.items() if v==minimum),
                         minimum_cumulative_charge_upper=minimum_total,minimum_mass_lower=1-minimum_total))
        print('prime',p,'tuples',info['tuple_count'],'minimum_mass',float(1-minimum_total),flush=True)
        post+=((p,cap),)
    byp={r['prime']:r for r in rows};m43=byp[43]['minimum_mass_lower'];m47=byp[47]['minimum_mass_lower']
    require(m43>F(ref['survival43_mass_lower']) and F(ref['mass47_lower'])<m47<0,
            'Verified improvement for the tested grouping;47 still unresolved')
    require(F('-0.011415427749556867')<m47<F('-0.011415427749556866'),
            'Outward rational bracket of the remaining47 deficit')
    paths=[base/'certificate_io.py',base/'verify_joint_frontier.py',source,reference,parent_proof,parent_producer,
           reference_proof,reference_producer,
           base/'profile-notes/06-a-common-matrix-bound-for-all-actual-rectangles.md',
           base/'profile-notes/j-source/329-a-finite-whole-j-neighborhood-covers-high-surplus.md']
    def key(p):
        try:return str(p.resolve().relative_to(base.resolve()))
        except ValueError:return str(p.resolve())
    raw=io.read_artifact_bytes(proof)
    out=dict(schema='erdos7-high-rho-fixed-original-groups-v1',
             scope='Same finite source and fixed333 physical schedule; one tested choice groups every prior factor at each target. Complete original-label and product-count tails; POST-only floor at sole13 conditioning. Rowwise minimum uses only existing333,335 and the tested all-prior bounds. Strictly improved43 survival lower and smaller but positive47 correction budget. No optimization over other partitions or thresholds and no claim that all count regroupings fail.',
             source_sha256={key(p):sha256(io.read_artifact_bytes(p)).hexdigest() for p in paths},
             ordinary_proof=dict(sha256=sha256(raw).hexdigest(),byte_count=len(raw)),
             producer_sha256=sha256(io.read_artifact_bytes(Path(__file__))).hexdigest(),
             guard=g,schedule=parent['schedule'],denominator_mass_coefficient=ec,denominator_constant=D,rows=rows,
             all_prior_mass47_lower=byp[47]['mass_lower'],minimum_survival43_mass_lower=m43,
             minimum_mass47_lower=m47,overlap_correction47_required_strictly_greater_than=-m47,
             reference335_survival43_mass_lower=F(ref['survival43_mass_lower']),
             reference335_mass47_lower=F(ref['mass47_lower']),improvement47_over335=m47-F(ref['mass47_lower']))
    return io,encode(out)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    parser.add_argument('--source',type=Path);parser.add_argument('--reference335',type=Path)
    parser.add_argument('--proof',type=Path);parser.add_argument('--certificate',type=Path)
    mode=parser.add_mutually_exclusive_group(required=True);mode.add_argument('--write',action='store_true');mode.add_argument('--check',action='store_true')
    args=parser.parse_args();certificate=args.certificate or args.base/DEFAULT_CERTIFICATE;begun=time.monotonic()
    io,out=calculate(args.base,args.source or args.base/DEFAULT_SOURCE,args.reference335 or args.base/DEFAULT_REFERENCE,args.proof or args.base/DEFAULT_PROOF)
    if args.write:io.write_certificate_text(certificate,json.dumps(out,indent=2)+'\n')
    else:require(out==json.loads(io.read_artifact_bytes(certificate),object_pairs_hook=io._unique),'Complete fixed-group account regenerates')
    with localcontext() as context:
        context.prec=35
        for k in ('all_prior_mass47_lower','minimum_survival43_mass_lower','minimum_mass47_lower','improvement47_over335'):
            q=F(out[k]);print(k,Decimal(q.numerator)/Decimal(q.denominator))
    print('PASS complete fixed-original-group account; elapsed_seconds',round(time.monotonic()-begun,3))

if __name__=='__main__':main()
