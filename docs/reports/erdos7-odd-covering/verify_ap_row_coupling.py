#!/usr/bin/env python3
"""Exact actual-row certificates, a sharp family and a supported-mask consumer.

Standard library only. Universal row identities and comparison are ordinary
proofs in the adjacent report; this checks rational inputs and literal data,
not Lean or an unrestricted numerical noncoverage bound.
"""
from fractions import Fraction as F
import json
from pathlib import Path
import runpy

P = 19
S, theta, ell = F(1,18), F(18,37), F(37,361)
rho, delta = 1-ell, F(7,17)
b, kappa = F(19,162), F(37,361)
T = b-kappa*theta

def need(condition, message):
    if not condition:
        raise ValueError(message)

def unique(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, 'duplicate JSON key')
        result[key] = value
    return result

def weights(c,q):
    v=ell*c+rho*q
    return q+S*c*c/v, (1-theta)*c+theta*q

def row(lam,alpha):
    c0=1/lam; C=c0/(1-delta)
    beta=max(F(0),(alpha-delta)/(1-delta))
    aa=min(alpha,delta)
    c=c0/(1-aa); q=1-beta
    g,w=weights(c,q)
    g0,w0=weights(c0,F(1)); gd,wd=weights(C,F(1)); g1,_=weights(C,F(0))
    slope=(gd-g0)/delta
    Dc=F(0); Dg=F(0)
    if alpha<=delta:
        Dc=C*alpha*(delta-alpha)/(1-alpha)
        A=ell*c0; z=1-alpha; y=1-delta
        Dg=(S*c0*c0*alpha*(delta-alpha)*
            (A*A+A*rho*(1+y+z)+rho*rho*(y+z+y*z))/
            (y*z*(A+rho)*(A+rho*y)*(A+rho*z)))
    else:
        vd=ell*C+rho; v1=ell*C; v=ell*C+rho*q
        Dg=S*rho*rho*C*C*beta*(1-beta)/(vd*v1*v)
    need(c==c0+C*aa-Dc,'c identity')
    need(w==w0+(1-theta)*C*aa-theta*beta-(1-theta)*Dc,'w identity')
    need(g==g0+slope*aa-(gd-g1)*beta-Dg,'g identity')
    need(Dc>=0 and Dg>=0,'curvature signs')
    need(slope>0 and gd>g1 and gd>=g0,'endpoint ordering')
    return dict(c=c,q=q,g=g,w=w,a=aa,beta=beta,Dc=Dc,Dg=Dg)

def compute():
    checked=0
    for den in range(1,38):
        for num in range(den+1):
            for lam in [F(17,18),F(341,361),F(18,19),F(1)]:
                row(lam,F(num,den));checked+=1
    height=2; z=F(1,P**height); lam=1-S*(1-z)
    c0=1/lam; C=c0/(1-delta)
    source=[x for x in range(3**7) if x%3]
    D=len(source)
    classes=[(0,3**j) for j in range(1,8)]
    current=[]
    for e in range(1,height+1):
        pe=P**e; spine=8*(P**(e-1)-1)//18
        classes.append((spine,pe));current.append((0,e,spine))
        for j in range(1,8):
            pp=3**j; r=spine+j*P**(e-1)
            residue=1+pp*((r-1)*pow(pp,-1,pe)%pe)
            need(residue%pp==1 and residue%pe==r,'CRT residue')
            classes.append((residue,pp*pe));current.append((j,e,r))
    need(len(classes)==len({m for _,m in classes})==7+8*height,'literal distinct labels')
    pure={y for y in range(P**height) if all(y%(P**e)!=r for j,e,r in current if j==0)}
    need(F(len(pure),P**height)==lam,'actual pure mass')
    data=[]
    for k in range(8):
        mixed={y for y in pure if any(y%(P**e)==r for j,e,r in current if 1<=j<=k)}
        alpha=F(len(mixed),len(pure))
        need(alpha==k*S*(1-z)/lam,'literal mixed union')
        rr=row(lam,alpha)
        need(rr['q']==1,'all rows uncharged')
        need(rr['c']==F(P**height,len(pure)-len(mixed)),'actual good density')
        data.append(rr)
    ks=[sum(x%3**j==1 for j in range(1,8)) for x in source]
    probs=[F(ks.count(k),D) for k in range(8)]
    need(probs==[F(1,2)]+[F(1,3**k) for k in range(1,7)]+[F(1,2*3**6)],'source counts')
    maxima={}
    for key in ['one','a','c','g','w']:
        vals=[F(1) if key=='one' else data[k][key] for k in ks]
        masses=[]
        for depth in range(8):
            m=3**depth; buckets=[F(0)]*m
            for x,v in zip(source,vals): buckets[x%m]+=v/D
            need(max(buckets)==buckets[1%m],f'centred weighted cylinder {key} {depth}')
            masses.append(buckets[1%m])
        pair_upper=sum(F(2*e+1)*masses[e] for e in range(8))
        centered=sum(v*(k+1)**2/D for v,k in zip(vals,ks))
        need(pair_upper==centered,'all ordered original pair caps attained')
        maxima[key]=centered
    G=maxima['one']; Ma=maxima['a']
    g0,w0=weights(c0,F(1)); gd,wd=weights(C,F(1)); g1,_=weights(C,F(0))
    sg=(gd-g0)/delta
    F0=g0+T*c0+kappa*theta; Fa=sg+T*C; Fb=gd-g1+kappa*theta
    curve=sum(prob*(rr['Dg']+T*rr['Dc']) for prob,rr in zip(probs,data))
    raw=(gd+(b-kappa)*C+kappa*wd)*G
    priced=F0*G+Fa*Ma-curve
    exact_mw=maxima['g']+(b-kappa)*maxima['c']+kappa*maxima['w']
    need(exact_mw<priced<raw,'strict actual row-profile improvement')
    need(priced==raw-Fa*(delta*G-Ma)-curve,'common deficit form')
    sharp=[]
    for h in [1,2,3,10]:
        zh=F(1,P**h); lamh=1-S*(1-zh); alphah=7*S*(1-zh)/lamh
        rr=row(lamh,alphah)
        need(rr['c']==9/(5+4*zh) and rr['q']==1,'actual corner approach')
        sharp.append({'height':h,'lambda':lamh,'alpha':alphah,'c':rr['c'],'g':rr['g']})
    return {'p':P,'height':height,'classes':classes,'source_mass_denominator':D,
       'row_identity_checks':checked,'lambda':lam,'c0':c0,'C':C,'old_maxima':maxima,
       'F0':F0,'Fa':Fa,'Fb':Fb,'curve_floor':curve,'old_budget_deficit':delta*G-Ma,
       'rectangle_bound':raw,'row_profile_bound':priced,'exact_MW_bound':exact_mw,
       'row_profile_gain':raw-priced,'actual_corner_sequence':sharp,
       'sharp_limits':{'c':F(9,5),'g':F(2531,2170),'w':F(261,185),'v':F(1953,1805)}}

def encode(x):
    if isinstance(x,F):return str(x)
    if isinstance(x,dict):return {str(k):encode(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [encode(v) for v in x]
    return x

def supported_mask_consumer():
    root = Path(__file__).resolve().parent
    source = runpy.run_path(str(root/'verify_high_seven_density_bridge.py'))['verify'](
        root/'actual_deletion_profile_certificate.json', root/'marked_head_profile_certificate.json')
    need(source == json.loads((root/'high_seven_density_bridge_certificate.json').read_text(),
                              object_pairs_hook=unique), 'complete D7 source reconstruction')
    M0 = F(source['inputs']['M0'])
    H0 = {int(k): F(v) for k,v in source['inputs']['hinges'].items()}
    beta = F(source['extension']['deleted_mass_upper'])
    q0 = F(source['extension']['retained_mass_lower'])
    M7 = F(source['extension']['mean_upper'])
    D7 = F(source['extension']['density_domination'])
    b17 = F(source['high7_charge']['b17'])
    def H(t):
        if t <= 1:
            return M7-t
        for a,b in zip(sorted(H0), sorted(H0)[1:]):
            if a <= t <= b:
                original = ((b-t)*H0[a]+(t-a)*H0[b])/(b-a)
                return (original+beta)/q0
        raise ArithmeticError('unsupported original hinge query')
    rows=[]
    for h in range(1,8):
        pn={n: F(15,17) if n==1 else F(32,17**n) for n in range(1,h)}
        tail_mass = F(1) if h==1 else F(2,17**(h-1))
        tail_mean = F(9,8) if h==1 else tail_mass*(h+F(1,16))
        need(sum(pn.values())+tail_mass==1, 'full query comparison mass')
        need(sum(n*v for n,v in pn.items())+tail_mean==F(9,8), 'full query comparison mean')
        low_terms={n:v*n*H(F(h,n)) for n,v in pn.items()}
        tail=M7*tail_mean-h*tail_mass
        physical=sum(low_terms.values())+tail
        gap17=(8-h-H(F(h)))/(15*D7)
        gap19=((8-h)*(1-b17)-physical)/(17*D7)
        rows.append(dict(h=h, physical17_hinge=physical, tail_mass=tail_mass,
                         tail_mean=tail_mean, low_terms=low_terms, full_tail=tail,
                         signed_gap17=gap17, signed_gap19=gap19))
    best17=max(rows,key=lambda x:x['signed_gap17'])
    best19=max(rows,key=lambda x:x['signed_gap19'])
    need(best17['h']==best19['h']==4, 'best among the seven stated integer queries')
    need(best19['physical17_hinge']==F(27262754949126328889,9040993351032212500),
         'full high-seven physical17 hinge at four')
    gap17=best17['signed_gap17'];gap19=best19['signed_gap19']
    need(gap17==F(24340697834399,2393015625000000)>0, 'uniform actual17 mask deficit')
    need(gap19==F(172720421147338864700128617,68828762219888452600000000000)>0,
         'uniform actual19 mask deficit after actual killing')
    c0=F(1);C=c0/(1-delta)
    g0,_=weights(c0,F(1));gd,_=weights(C,F(1))
    Fa_min=(gd-g0)/delta+T*C
    need(Fa_min==F(38863139,113133429), 'least Fa endpoint')
    saving=Fa_min*gap19
    need(saving==F(989600137872264452151450945061,1147992611493680176933800000000000)
         > F(862026574,10**12), 'fixed positive RC saving')
    return dict(scope='Original357 part divides45*7^H, all finiteH and all11/13/17/19 cofactors. '
                      'Same actual AP13/killed17/killed19 laws. A restricted quantitative RC consumer; '
                      'no unrestricted299.661 bound or extra BM/OBE rebate.',
                source_sha256=source['source_sha256'],
                source_upstream_sections_sha256=source['upstream_sections_sha256'],
                source_mean=M0, auxiliary_density=D7, auxiliary17_charge=b17,
                rows=rows, actual_gap17=gap17, actual_gap19=gap19,
                Fa_min=Fa_min, fixed_RC_saving=saving)

if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('--write',type=Path);ap.add_argument('--check',type=Path)
    args=ap.parse_args()
    path=Path(__file__).with_name('ap_row_coupling_certificate.json')
    raw=compute();raw['supported_mask_consumer']=supported_mask_consumer();out=encode(raw)
    if args.check or not args.write:
        need(json.loads((args.check or path).read_text(),object_pairs_hook=unique)==out,'certificate mismatch')
    if args.write:args.write.write_text(json.dumps(out,indent=2)+'\n')
    print('PASS: exact AP row identities, literal family, full old-layout pair caps, sharp limits, '
          'and supported actual-mask deficits')
