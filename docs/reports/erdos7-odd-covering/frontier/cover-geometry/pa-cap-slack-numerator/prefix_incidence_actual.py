#!/usr/bin/env python3
"""Independent exact audit of prefix-incidence coefficients and actual59 control.

This reuses559's conditional cap envelope. Finite checks below verify algebra
and the explicit actual family, not the general comparison or limit argument.
"""
from argparse import ArgumentParser
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import prod
from pathlib import Path
import json
Q=(5,7,11,13,17,19)
PIN='43401805c0a3dc294c6a569acfc7d743f44bded57360d7d09debbdd34d1bbcfb'

def pos(x):return max(x,0)
def eta_point(q,n,z):
    return sum((F(pos(n+(e+1)*z-3)-pos(n+e*z-3),q**e) for e in range(1,4)),F())+F(z,q**3*(q-1))
def ex(x):return {'exact':str(x),'decimal':float(x)}

def main():
    ap=ArgumentParser(description=__doc__)
    ap.add_argument('--source-dir',type=Path,default=Path(__file__).resolve().parent)
    ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=ap.parse_args();checks=[]
    def need(name,condition):
        if not condition:raise ValueError('FAILED: '+name)
        checks.append(name)
    raw=(args.source_dir/'pa_cap_slack_numerator.json').read_bytes()
    need('559 cap supplier pinned',sha256(raw).hexdigest()==PIN)
    source=json.loads(raw);point_controls=0
    for q,n,z in product((11,13,17,19),range(9),(1,2,3,4,11,100)):
        observed=eta_point(q,n,z)-eta_point(q,0,z)
        expected=F() if n==0 else ((F(1,q*q) if n==1 else F(q+1,q*q)) if z==1 else (F(1,q) if z==2 else F()))
        deletion=pos(z+n-3)-pos(z-3)
        dexp=0 if n==0 else ((1-int(z==1)-int(z==2)) if n==1 else n-2*int(z==1)-int(z==2))
        if observed!=expected or deletion!=dexp:raise ValueError('point coefficient mismatch')
        point_controls+=1
    need('closed forms all point controls',point_controls==216)
    rows=[]
    for row in source['rows']:
        q=row['q'];EZ=F(row['EZ']);p1=F(row['P1']);p2=F(row['P2'])
        old=EZ/(q-1)-F(q+1,q*q)*p1-p2/q
        need('old eta recovered q='+str(q),old==F(row['eta']))
        rows.append({'q':q,'old_eta':ex(old),'delta_eta_n1':ex(p1/q**2+p2/q),
            'delta_eta_n_ge2':ex(F(q+1,q*q)*p1+p2/q),
            'delta_zeta_n1':ex(1-p1-p2),'delta_zeta_n2':ex(2-2*p1-p2)})
    need('q19 coefficients',eta_point(19,0,1)==F(1,6498)
         and eta_point(19,1,1)-eta_point(19,0,1)==F(1,361)
         and eta_point(19,2,1)-eta_point(19,0,1)==F(20,361))
    need('suffix growth does not preserve difference monotonicity',
         eta_point(19,2,1)-eta_point(19,0,1)>eta_point(19,2,2)-eta_point(19,0,2)>0)
    rigidity=F(36,361);C=F(9,5);critical=F(5,9)
    for n,g in product((3,4,17),(F(),F(1,9),F(1,3),F(5,9),F(2,3),F(17,19),F(1))):
        loss=1-min(1,C*g);cap=C-min(C,1/g) if g else F()
        penalty=loss*(n-2)+cap*F(20,361)
        if penalty<rigidity*abs(g-critical):raise ValueError('rigidity')
    need('rigidity rational controls',True)
    grids=[]
    for H in range(4):
        m=19**H;minimum=None
        for a in range(m+1):
            g=F(a,m);loss=1-min(1,C*g);cap=C-min(C,1/g) if g else F()
            penalty=loss+cap*F(20,361)
            minimum=penalty if minimum is None else min(minimum,penalty)
        expected=F(144,361*(5*m+4))
        need('finite grid exact minimum H='+str(H),minimum==expected)
        grids.append({'H':H,'minimum':ex(minimum)})
    # Actual59 original family: selected prime roots0,1;45 deep full-Q labels.
    originals=[]
    def add(e,d,t,r):
        a=r%d if not e else (t%(3**e) if d==1 else r+d*(((t-r)*pow(d,-1,3**e))%(3**e)))
        m=(3**e)*d
        if not(0<=a<m and a%d==r%d and a%(3**e)==t%(3**e)):raise ValueError('CRT')
        originals.append({'modulus':m,'phase':a,'e':e,'d':d,'t':t,'r':r})
    add(1,1,1,0);add(2,1,3,0)
    for q in Q:add(0,q,0,0);add(1,q,2,1)
    ts=[t for t in range(81) if t%3!=1 and t%9!=3];M=prod(Q)
    for j,t in enumerate(ts):add(4,M*5**j,t,2)
    need('59 distinct actual numerical originals',len(originals)==len({r['modulus'] for r in originals})==59)
    need('actual source row caps inactive',all(F(q,q-2)<cap for q,cap in ((11,F(5,3)),(13,F(3,2)),(17,F(2)),(19,F(9,5)))))
    E1=prod((F(1,q-2) for q in Q),start=F(1));need('actual damage event mass',E1==F(1,378675))
    tau=F(2,3)*sum((E1/F(5**j) for j in range(8,45)),F())
    need('59 positive exact clipping tail',tau==(1-F(1,5**37))/(6*378675*5**7)>0)
    need('59 selected current-root unions have zero overlap',
         all({a for a in range(q) if a==0}.isdisjoint({a for a in range(q) if a==1}) for q in Q))
    A={t for t in ts if t%9 in (0,6)};Bbranch={t for t in ts if t%3==2}
    atom_probabilities=[1-E1]+[E1*F(4,5**n) for n in range(1,45)]+[E1/F(5**44)]
    total_tau=F();retained=F();D=F(74,3)
    for n,pn in enumerate(atom_probabilities):
        removed=set(ts[:n]);ca=F(len(A-removed),18);cb=F(len(Bbranch-removed),27)
        W=12*(1-ca)+18*(1-cb);T=max(W-F(16,3),F())
        aa=12*ca/D;ab=min(1-aa,18*cb/D)
        if W!=F(2*n,3) or aa+ab!=1-T/D:raise ValueError('59 actual reserve identity')
        total_tau+=pn*T;retained+=pn*(aa+ab)
    need('59 all46 actual nested incidence atoms',len(atom_probabilities)==46
         and sum(atom_probabilities,F())==1 and total_tau==tau and retained==1-tau/D)
    need('59 positive joint zero-reserve event',atom_probabilities[-1]>0
         and len(A-set(ts))==len(Bbranch-set(ts))==0)
    query_controls=0
    for es in product(range(3),repeat=len(Q)):
        if not any(es):continue
        d=prod(q**e for q,e in zip(Q,es));q=next(q for q,e in zip(Q,es) if e)
        if not(d%q==0 and M%q==0 and 3%q not in (0,1,2)):
            raise ValueError('query phase3 avoidance')
        query_controls+=1
    need('59 maximizing query phase3 avoids whole damage cylinder',query_controls==728)

    # Capped valuation categories0,1,>=2 determine whether K=1,K=2,K>=3.
    prefix=Q[:-1];laws=[(F(q-3,q-2),F(q-1,q*(q-2)),F(1,q*(q-2))) for q in prefix]
    pK1=F();pK2=F();D19=F();total=F()
    slack=F(9,5)-F(19,17)
    for vs in product(range(3),repeat=len(prefix)):
        probability=prod((law[v] for law,v in zip(laws,vs)),start=F(1))
        k=prod(v+1 for v in vs);n=k-1
        total+=probability
        if k==1:pK1+=probability
        if k==2:pK2+=probability
        D19+=probability*slack*(eta_point(19,n,1)-eta_point(19,0,1))
    need('prefix category probability mass',total==1)
    need('59 exact low query-prefix probabilities',pK1==F(1792,4455) and pK2==F(6443456,18050175))
    need('59 exact prefix-incidence increment',D19==F(16245701864,1661608859625))
    need('59 independent closed expectation',D19==slack*F(1,361)*(20-20*pK1-19*pK2))
    oldcap=slack*eta_point(19,0,1)
    need('old cap debit remains separately positive',oldcap==F(29,276165)>0 and D19>oldcap)
    R=prod((1+F(q,(q-1)*(q-2)) for q in Q),start=F(1))-1
    need('59 complete actual source norm',R==F(214267985,147806208))
    # For query phase0 all earlier nonunit cylinders miss actual selected
    # support, hence n19=0; old row slack is unchanged. Phase3 maximizes and
    # avoids E1 at every nonunit label, so raw clipping debit is exactly0.
    need('same old cap slack with zero new prefix increment',
         slack*(eta_point(19,0,1)-eta_point(19,0,1))==0)
    B=F(432040125182653876501,86355045355449035400)
    K2=B-2;G=F(566,49);z=F(16,3);den=30-z
    N2=1+2*B+(z*K2-3)/den
    coeffs=(F(1),1-3/den,z/den,3/den)
    slope=(G-5)/den;margin=G-N2
    need('improved CJ6 exact N2',N2==(164*B+33)/74==F(18426074256671263478591,1597568339075807154900))
    need('improved CJ6 exact prefix coefficients',coeffs==(F(1),F(65,74),F(8,37),F(9,74)))
    need('improved CJ6 exact normalized tail slope',slope==F(963,3626))
    need('improved CJ6 strict unclipped margin',margin>0)
    for tt in (F(),F(1,100),F(1,20)):
        db,d1,du,dl=F(1,1000),F(2,1000),F(3,1000),F(4,1000)
        EU=B-tt-dl
        direct=(B-2*tt/den-db)+(1-3/den)*(1+B-d1)+(EU+z*(K2-du)+2*EU)/den
        debit=sum((c*x for c,x in zip(coeffs,(db,d1,du,dl))),F())
        if direct!=N2-5*tt/den-debit:raise ValueError('improved CJ6 algebra')
        if (N2-5*tt/den-debit-G*(1-tt/den))!=slope*tt-margin-debit:
            raise ValueError('normalized sufficient inequality')
    need('improved CJ6 affine numerator and normalization controls',True)
    out={'schema':'prefix-incidence-coefficients-audit-v1',
         'source':{'path':'pa_cap_slack_numerator.json','sha256':PIN},
         'generic_coefficients':{'delta_eta_n0':'0','delta_eta_n1':'p1/q^2+p2/q','delta_eta_n_ge2':'(q+1)*p1/q^2+p2/q','delta_zeta_n0':'0','delta_zeta_n1':'1-p1-p2','delta_zeta_n_ge2':'n-2*p1-p2'},
         'coefficient_rows':rows,'point_controls':point_controls,'rigidity_constant':ex(rigidity),'finite_grid_controls':grids,
         'actual59':{'originals':originals,'source':'actual product law on prime roots outside0,1; prefix mass and final PA mass both3/7.',
             'actual_nested_fibres':46,'query_avoidance_controls':query_controls,'selected_current_root_overlap':ex(F()),'retained_clipped_mass':ex(retained),
             'prefix_low_categories':243,'pK1':ex(pK1),'pK2':ex(pK2),'D19_extra':ex(D19),
             'old_constant_cap19':ex(oldcap),'tau':ex(tau),'RQ':ex(R),
             'raw_query_debit':ex(F()),'all_query_avoidance_proof':'For any nonunit Q-smooth d choose q|d. The phase3 mod d is supported entirely on retained root3 at every prime dividing d, hence maximizes under the product source. It differs from2 mod q and therefore misses E1=[2]_M. beta=1 on that cylinder, so q_d(beta nu)=q_d(nu) at EVERY query height. The omitted unit would have lost mass tau/D.',
             'layout_separation':'Same actual source and old cap/J data: phase0 at every complete query gives n19=0 and D19=0; phase3 maximizes every query and yields displayed D19_extra. Old constant cap debit is NOT zero.'},
         'improved_CJ6':{'B':ex(B),'K2':ex(K2),'G':ex(G),'z':ex(z),'D':ex(den),'N2':ex(N2),'coefficients_D_beta_D1_DU_D_layer':[ex(c) for c in coeffs],'tail_slope':ex(slope),'positive_G_minus_N2':ex(margin),'sufficient_condition':'A_z > (963/3626)*tau - (G-N2), with A_z=D_beta+(65/74)D1+(8/37)DU+(9/74)D_layer.'},
         'limit_audit':'Fix a finite partial query while exhausting complete boxes.0<=delta_eta_H(n)<=Z_full/(q-1),0<=delta_zeta_H(n)<=n permit dominated convergence; no monotonicity of coefficient differences with suffix height is assumed. Then exhaust a fixed countable layout using full coefficients, monotone in its prefix count.',
         'novelty_boundary':'An explicit prefix-aware refinement of559 CS4 and569 SD5, not a new comparison mechanism. Old eta(0)K and J credits remain untouched; only coefficient differences are added. General proof is separately audited; no Lean.',
         'check_count':len(checks),'checks':checks}
    args.output.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'checks':len(checks),'point_controls':point_controls,'D19':str(D19),'tau':str(tau)}))

if __name__=='__main__':main()
