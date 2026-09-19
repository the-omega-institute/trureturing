#!/usr/bin/env python3
"""Exact original-label maxima in the charged 315/17/19 family.

Uses only standard-library rational/integer arithmetic. The product first-exit
normal form, branch bound and all-height theorem are proved in marked_head_profile.md.
No Lean verification or bound over arbitrary source families is claimed.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from fractions import Fraction as F
from math import gcd,lcm,prod
from itertools import product
import json
Q=315
xs=[x for x in range(Q) if gcd(x,Q)==1]
ds=[d for d in range(2,Q+1) if Q%d==0]
doms=[]
for d in ds:
    factors=[]
    if d%9==0:factors.append((9,[1,2,4]))
    elif d%3==0:factors.append((3,[1,2]))
    if d%5==0:factors.append((5,[1,2]))
    if d%7==0:factors.append((7,[1,2]))
    doms.append([next(x for x in range(d) if all(x%m==r for (m,rr),r in zip(factors,rs))) for rs in product(*(rr for m,rr in factors))])
q=[];u=[];v=[];w=[]
for x in xs:
    k=sum(x%d==1 for d in [3,9,15,21,45,63,105,315])
    ts=[];qs=[]
    for p in [17,19]:
        alpha=F(k,p-1);delta=F(7,p-2)
        g=1/(1-min(alpha,delta)); beta=max(F(0),alpha-delta)/(1-delta)
        ts.append(g/(p-1));qs.append(1-beta)
    q.append(qs[0]*qs[1]);u.append(ts[0]*qs[1]);v.append(ts[1]*qs[0]);w.append(ts[0]*ts[1])
rows=[q,u,v,w]

def solve(weights,blocks=1):
    # Objective sum_{g,h} H_gh A_g A_h; weights symmetric.
    labels=[(g,d) for g in range(blocks) for d in ds]; n=len(labels)
    dd=doms*blocks
    # constant all unit terms.
    constant=F(sum(sum(weights[g][h]) for g in range(blocks) for h in range(blocks)),144)
    unary=[];pair={}
    for i,(g,d) in enumerate(labels):
        wi=[weights[g][g][k]+2*sum(weights[g][h][k] for h in range(blocks)) for k in range(144)]
        unary.append([F(sum(wi[k] for k,x in enumerate(xs) if x%d==r),144) for r in dd[i]])
    for i,(g,d) in enumerate(labels):
        for j,(h,e) in enumerate(labels[:i]):
            wi=[2*z for z in weights[g][h]]
            matrix=[[F(sum(wi[k] for k,x in enumerate(xs) if x%d==r and x%e==s),144) for s in dd[j]] for r in dd[i]]
            pair[i,j]=matrix
    allf=[constant]+[v for row in unary for v in row]+[v for mat in pair.values() for row in mat for v in row]
    scale=lcm(*(v.denominator for v in allf))
    unary=[[int(v*scale) for v in row] for row in unary]
    pair={ij:[[int(v*scale) for v in row] for row in mat] for ij,mat in pair.items()}
    for (i,j),mat in list(pair.items()):pair[j,i]=list(map(list,zip(*mat)))
    caps={ij:max(v for row in mat for v in row) for ij,mat in pair.items()}
    def val(x):return sum(unary[i][r] for i,r in enumerate(x))+sum(pair[i,j][x[i]][x[j]] for i in range(n) for j in range(i))
    bestx=[0]*n; best=val(bestx)
    # one-coordinate ascent from centered and each full zero-block atom option.
    for first in range(len(dd[len(ds)-1])):
        x=[0]*n;x[len(ds)-1]=first
        changed=True
        while changed:
            changed=False
            for i in range(n):
                v,r=max((val(x[:i]+[r]+x[i+1:]),r) for r in range(len(dd[i])))
                if v>val(x):x[i]=r;changed=True
        v=val(x)
        if v>best:best,bestx=v,x
    nodes=covered=pruned=0
    def visit(ids,adj,current,x):
        nonlocal nodes,covered,pruned,best,bestx
        nodes+=1
        completions=prod(len(dd[i]) for i in ids)
        if not ids:
            covered+=1
            if current>best:best,bestx=current,x[:]
            return
        pc=sum(caps[i,j] for a,i in enumerate(ids) for j in ids[:a])
        if current+sum(max(adj[i]) for i in ids)+pc<=best:
            pruned+=1;covered+=completions;return
        chosen=branches=None
        for i in ids:
            rest=[j for j in ids if j!=i];restpc=pc-sum(caps[i,j] for j in rest)
            possible=[];bounds=[]
            for r,ur in enumerate(adj[i]):
                bound=current+ur+restpc+sum(max(uj+v for uj,v in zip(adj[j],pair[i,j][r])) for j in rest)
                bounds.append(bound)
                if bound>best:possible.append((bound,r))
            if not possible:pruned+=1;covered+=completions;return
            if branches is None or len(possible)<len(branches):chosen,branches=i,possible
        i=chosen;rest=[j for j in ids if j!=i];ec=prod(len(dd[j]) for j in rest)
        covered+=(len(dd[i])-len(branches))*ec
        for bound,r in sorted(branches,reverse=True):
            if bound<=best:covered+=ec;continue
            nxt={j:[uj+v for uj,v in zip(adj[j],pair[i,j][r])] for j in rest}
            xx=x[:];xx[i]=r
            visit(rest,nxt,current+adj[i][r],xx)
    visit(list(range(n)),{i:r[:] for i,r in enumerate(unary)},0,[-1]*n)
    if covered!=prod(map(len,dd)):raise ValueError('bad coverage')
    return {'constant':str(constant),'integer_scale':scale,'nonconstant_maximum_integer':best,'pruned_nodes':pruned,'maximum':str(constant+F(best,scale)),'maximizer':[(g,d,dd[i][bestx[i]]) for i,(g,d) in enumerate(labels)],'nodes':nodes,'coverage':covered}



def need(ok,msg):
    if not ok:raise ArithmeticError(msg)

def unique(pairs):
    out={}
    for k,v in pairs:
        need(k not in out,'duplicate JSON key '+k)
        out[k]=v
    return out

def crt(a,d,b,e):
    return (a+d*((b-a)*pow(d,-1,e)%e))%(d*e)

def compute():
    need(len(xs)==144 and len(ds)==11,'literal old source and label count')
    forbidden=[(3,0),(5,0),(7,0),(17,0),(19,0)]
    cofactors=[3,9,15,21,45,63,105,315]
    for p in [17,19]:
        forbidden.extend((d*p,crt(1,d,i,p)) for i,d in enumerate(cofactors,1))
    need(len(set(d for d,a in forbidden))==21,'21 distinct odd forbidden moduli')
    need(all(d>1 and d%2 for d,a in forbidden),'odd nontrivial moduli')
    need(lcm(*(d for d,a in forbidden))==101745,'literal common period')
    b17=b19=F(0);mass=moment=F(0)
    for k,x in enumerate(xs):
        survivors=[];gs=[];qs=[];ts=[]
        for p in [17,19]:
            good=[y for y in range(1,p) if all(crt(x,315,y,p)%(d*p)!=a for d0,a in forbidden if d0%p==0 and d0!=p for d in [d0//p])]
            alpha=F(p-1-len(good),p-1);delta=F(7,p-2)
            g=1/(1-min(alpha,delta));beta=max(F(0),alpha-delta)/(1-delta)
            survivors.append(good);gs.append(g);qs.append(1-beta);ts.append(g/(p-1))
            if p==17:b17+=beta/144
            else:b19+=beta/144
        need(q[k]==qs[0]*qs[1] and u[k]==ts[0]*qs[1] and v[k]==ts[1]*qs[0] and w[k]==ts[0]*ts[1],'literal CRT killed row weights')
        need(16 in survivors[0] and 18 in survivors[1],'globally clean current roots')
        C=1+sum(x%d==1 for d in ds)
        atom=gs[0]*gs[1]/(144*16*18)
        for y,z in product(*survivors):
            n=crt(crt(x,315,y,17),315*17,z,19)
            need(all(n%d!=a for d,a in forbidden),'literal final support')
            mass+=atom
            moment+=atom*(C*(1+(y==16))*(1+(z==18)))**2
    need(b17==F(1,2304) and b19==F(1,2592),'both assigned charges')
    need(mass==F(13813,13824),'actual unnormalized final mass')
    # Positive centered-cylinder coefficients for all added-height weights.
    coeff={}
    for name,ff in [('u',u),('v',v),('w',w)]:
        values={sum(x%d==1 for d in cofactors):ff[i] for i,x in enumerate(xs)}
        f0,f1,f2,f4,f8=[values[k] for k in [0,1,2,4,8]]
        cc=[f0,f1-f0,f2-f1,f4-2*f2+f1,f8-3*f4+3*f2-f1]
        need(all(c>=0 for c in cc),'nonnegative centered coefficients')
        for i,x in enumerate(xs):
            value=cc[0]+cc[1]*(x%3==1)+cc[2]*sum(x%d==1 for d in [9,15,21])+cc[3]*sum(x%d==1 for d in [45,63,105])+cc[4]*(x%315==1)
            need(value==ff[i],'centered expansion on every actual row')
        coeff[name]=list(map(str,cc))
    R0=[a+b+c for a,b,c in zip(u,v,w)];qr=[a+b for a,b in zip(q,R0)]
    out={name:solve([[f]]) for name,f in [('q',q),('R0',R0),('qR0',qr)]}
    out['merged_gap']=str(F(out['q']['maximum'])+F(out['R0']['maximum'])-F(out['qR0']['maximum']))
    H=[[q,u,v,w],[u,u,w,w],[v,w,v,w],[w,w,w,w]]
    out['full']=solve(H,4)
    C=[1+sum(x%d==1 for d in ds) for x in xs]
    gam=lambda f:sum(a*c*c for a,c in zip(f,C))/144
    S=F(out['q']['maximum'])+3*gam(u)+3*gam(v)+9*gam(w)
    out['split']=str(S);out['exact_gap']=str(S-F(out['full']['maximum']))
    need(moment==F(out['full']['maximum'])==F(7061549,548352),'direct physical point scan attains exact optimization')
    need(F(out['exact_gap'])==F(1573,13824),'exact same-law split gap')
    Minf=gam(q)+F(425,128)*gam(u)+F(266,81)*gam(v)+F(425,128)*F(266,81)*gam(w)
    out['all_height']={'EqC2':str(gam(q)),'Gamma_u':str(gam(u)),'Gamma_v':str(gam(v)),'Gamma_w':str(gam(w)),'b17_infinite':'425/128','b19_infinite':'266/81','maximum_supremum':str(Minf),'split_gap_every_height':out['exact_gap']}
    out['source']={'period':315,'units':144,'original_period_height_one':101745,'forbidden':forbidden,'test_labels_height_one':48,'old_normal_form_domain':prod(map(len,doms)),'old_divisors':ds,'domains':doms,'charge17':str(b17),'charge19_physical17':str(b19),'final_mass':str(mass),'direct_centered_square':str(moment),'positive_centered_coefficients':coeff}
    return json.loads(json.dumps({'schema':'actual-bqc-exact-all-height-v1','results':out,'scope':'One actual 315-source family with arbitrary finite current heights obtained by redundant pure exclusions. All original labels remain independent. No uniform subtraction for arbitrary source or mixed-mask geometries, no unrestricted #7 conclusion, no Lean verification.'}))

if __name__=='__main__':
    import argparse
    from pathlib import Path
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--certificate',type=Path,default=(Path(__file__).resolve().parent / 'certificates/exact_bqc_certificate.json'))
    p.add_argument('--write',action='store_true')
    a=p.parse_args();out=compute()
    if a.write:write_certificate_text(a.certificate, json.dumps(out,indent=2)+'\n')
    else:need(json.loads(read_artifact_text(a.certificate),object_pairs_hook=unique)==out,'complete deterministic certificate match')
    print('PASS literal source/masks, charged kernels, full original-label maximum and all-height coefficients')
