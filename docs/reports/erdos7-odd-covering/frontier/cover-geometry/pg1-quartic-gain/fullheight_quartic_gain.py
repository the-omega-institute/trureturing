"""Exact full-height quartic reserves and finite complete-label checks.

The accompanying proof supplies the universal height and query claims.
Geometric moments include infinite tails. No numerical sampling is a
certificate for an unrestricted covering theorem.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from math import comb, factorial, gcd, prod
from pathlib import Path

T = F(1, 2**37)


def need(condition, reason):
    if not condition:
        raise ValueError(reason)


def geometric_moment(k, p):
    row = [1]
    for n in range(1, k+1):
        row = [0]+[(row[j-1] if j-1 < len(row) else 0)
                   + j*(row[j] if j < len(row) else 0) for j in range(1,n+1)]
    return sum((F(row[j]*factorial(j), (p-1)**j) for j in range(k+1)), F(0))


def power_series(k, z):
    if k == 0:
        return 1/(1-z)
    row = [1]
    for n in range(2, k+1):
        row = [(i+1)*(row[i] if i < len(row) else 0)
               +(n-i)*(row[i-1] if i else 0) for i in range(n)]
    return sum((a*z**(i+1) for i,a in enumerate(row)), F(0))/(1-z)**(k+1)


def shifted(k, p, a):
    first = sum((comb(k,j)*a**(k-j)*geometric_moment(j,p) for j in range(k+1)), F(0))
    second = (1-F(1,p))*sum((comb(k,j)*a**(k-j)*power_series(j,F(1,p))
                             for j in range(k+1)), F(0))
    need(first == second, 'Stirling and Eulerian geometric sums agree')
    return first


def old_moment(k):
    return prod((shifted(k,3,3),shifted(k,5,2),shifted(k,7,2),
                 1+(shifted(k,11,2)-1)/10,1+(shifted(k,13,2)-1)/12))


def constants(mu, mu2, t=T, rare_depth=98):
    need(t > 0 and type(rare_depth) is int and rare_depth >= 1,'positive transfer and rare depth')
    root = {k:old_moment(k)*shifted(k,17,2) for k in (2,3,4,5)}
    haar = {k:old_moment(k)*shifted(k,17,1) for k in (4,8)}
    need(root[2] == F(638455140323,248832000) and
         root[3] == F(104829447952912991,402653184000),'same FI3 old-height moment source')
    need(haar[4] == F(3528039728534972593,637009920000),'same FI6 Haar comparison')
    epsilon = F(3,2)*mu*t
    gaps = {'spoke':15*mu2*F(14,187),'pure':F(15,17),'spine':F(15,289)}
    reserves = {n:g-mu*t*root[4]-epsilon for n,g in gaps.items()}
    tail_reserve = epsilon-F(17,3)*mu*t*t*root[5]
    rare_reserve = 3**rare_depth*epsilon**2-64*haar[8]
    need(all(v>0 for v in reserves.values()),'all non-clean pure-root exceptional reserves positive')
    need(tail_reserve > 0,'complete fifth moment pays the cubic deficit tail')
    need(rare_reserve > 0,'complete Haar eighth moment preserves half the gain')
    need(t < F(41,952) and t/4 < F(1,17),'actual recipient capacity and donor mass')
    return dict(transfer=t,epsilon=epsilon,root_moments=root,haar_moments=haar,
                exceptional_reserves=reserves,recipient_tail_reserve=tail_reserve,
                rare_depth=rare_depth,rare_squared_reserve=rare_reserve)


def crt(a,m,b,n):
    need(gcd(m,n)==1,'coprime CRT coordinates')
    return (a+m*((b-a)*pow(m,-1,n)%n))%(m*n)


def load_source(report_root):
    spec=importlib.util.spec_from_file_location('e7_fullheight_io',report_root/'certificate_io.py')
    io=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(io)
    raw=io.read_artifact_bytes(report_root/'certificates/mod3_conditioned_geometry_certificate.json')
    digest=sha256(raw).hexdigest()
    need(digest=='9a0e265a456ab133389202abd5ef91ac6826957f74c24b1e8bd055a97cea0a0a',
         'pinned complete PG1 logical DATA')
    cases=[x for x in json.loads(raw)['cases'] if x['name']=='PG1']
    need(len(cases)==1,'one PG1 source')
    s=cases[0]
    old=dict(s['family'])
    need(sorted(old)==[d for d in range(2,316) if 315%d==0],'complete low old labels')
    need(s['points']==[x for x in range(315) if all(x%d!=a for d,a in old.items())],
         'literal low surviving set')
    need(len(s['points'])==75 and sum(s['weight_numerators'])==s['weight_denominator']==1000000007,
         'same normalized low source')
    mu=dict(zip(s['points'],(F(v,s['weight_denominator']) for v in s['weight_numerators'])))
    return old,mu,digest


def finite_checks(old,t):
    # One extra3 digit and nonzero11/13 roots, with ALL64 old divisor slots.
    M=945*11*13
    ds=sorted(3**a*5**b*7**c*11**d*13**e
              for a,b,c,d,e in product(range(4),range(2),range(2),range(2),range(2)))
    need(len(ds)==64 and len(set(ds))==64 and ds[-1]==M,'complete finite old inventory')
    originals={d:0 if d%11==0 or d%13==0 else old[gcd(d,315)]%d for d in ds[1:]}
    for d,a in originals.items():
        ancestor=11 if d%11==0 else 13 if d%13==0 else gcd(d,315)
        forbidden=0 if ancestor in (11,13) else old[ancestor]
        need(d%ancestor==0 and a%ancestor==forbidden,'every additional actual old class is redundant')
    rows=[crt(crt(314+315*j,945,u,11),945*11,v,13)
          for j,u,v in product(range(3),range(1,11),range(1,13))]
    need(len(rows)==len(set(rows))==360,'one actual conditional source on E')
    need(all(all(x%d!=a for d,a in originals.items()) for x in rows),'all conditional rows actually survive')
    samples=[]
    for H in (1,2):
        pe=17**H
        c=1/(1-2*F(1-F(1,pe),16))
        for seed in range(8):
            # Retain every full label; fix pure17 to a clean root.
            query={(d,e):((314 if seed%2==0 else 314+7*seed+d)%d,
                           0 if e==0 else ((2 if (d+seed+e)%3 else 12)
                           +17*((d+seed)%17) if e>=2 else (2 if (d+seed)%3 else 12)))
                   for d in ds for e in range(H+1)}
            query[(1,1)]=(0,12)
            need(len(query)==64*(H+1),'every old and current full label has its own phase')
            deficit=increment=tail=F(0)
            matches=0
            for x in rows:
                A=sum(x%d==query[(d,0)][0] for d in ds)
                recipient=[(e,b) for (d,e),(a,b) in query.items() if e>0 and b%17==2 and x%d==a]
                counts=[sum(e==j for e,b in recipient) for j in range(1,H+1)]
                level=A
                cap=F(0)
                for e,n in enumerate(counts,1):
                    cap+=F((level+n)**3-level**3,17**e)
                    level+=n
                actual3=actual4=actual5=0
                for y in range(2,pe,17):
                    Z=sum(y%(17**e)==b for e,b in recipient)
                    X=A+Z
                    actual3+=X**3-A**3
                    actual4+=X**4-A**4
                    actual5+=X**5
                    need(3*(X**4-A**4)<=4*X*(X**3-A**3),'pointwise cubic/quartic relation')
                    need(t*(X**4-A**4)-F(4,17)*(X**3-A**3)<=F(17,3)*t*t*X**5,
                         'fifth-moment tail inequality on actual complete loads')
                    matches+=1
                denominator=17**(H-1)
                need(cap>=F(actual3,17*denominator),'same-layout nested triple caps dominate root-conditional load')
                deficit+=4*c*cap
                increment+=F(actual4,denominator)*t
                tail+=F(actual5,denominator)*F(17,3)*t*t
            need(increment-deficit<=tail,'finite full-inventory cubic deficit pays recipient increase')
            samples.append(dict(height=H,layout_seed=seed,full_labels=len(query),
                                actual_conditional_points=matches,
                                mean_cubic_deficit=deficit/len(rows),
                                mean_recipient_increment=increment/len(rows),
                                mean_fifth_tail=tail/len(rows)))
    return dict(old_period=M,old_divisors=ds,old_originals=originals,conditional_rows=len(rows),samples=samples)


def rare_witness():
    Q=3**100
    cofactors=[Q,5*Q,7*Q,35*Q,11*Q]
    rows=[dict(modulus=17*d,phase=crt(314%d,d,r,17),old_cofactor=d,root=r)
          for d,r in zip(cofactors,(12,13,14,15,16))]
    need(len({x['modulus'] for x in rows})==5,'five distinct original rare-event labels')
    for x in rows:
        need(x['phase']%Q==314 and x['phase']%17==x['root'],'one fixed global CRT phase per label')
    need(314%11!=0 and 314%13!=0,'rare old cylinder contains actual supported coordinates')
    return dict(old_event_modulus=Q,old_event_phase=314,probability_upper=F(1,3**98),changed_originals=rows)


def run(report_root):
    old,mu,digest=load_source(report_root)
    need(mu[314]==F(16622259,1000000007) and mu[2]==F(13119398,1000000007),'same selected actual masses')
    c=constants(mu[314],mu[2])
    rejected=[]
    for name,operation in (
            ('zero transfer',lambda:constants(mu[314],mu[2],F(0))),
            ('insufficient fifth-moment budget',lambda:constants(mu[314],mu[2],2*T)),
            ('insufficient rare-event budget',lambda:constants(mu[314],mu[2],T,97)),
            ('noncoprime CRT interface',lambda:crt(1,3,2,9))):
        try:operation()
        except ValueError:rejected.append(name)
        else:raise ValueError('Invalid computation accepted: '+name)
    return dict(schema='e7-fullheight-quartic-v1',source_data_sha256=digest,constants=c,
                finite_complete_label_checks=finite_checks(old,T),rare_actual_witness=rare_witness(),
                invalid_controls_rejected=rejected,lean_verification=False,
                scope='Specified FI2 family, arbitrary finite old and17 heights; no general-family source gain')


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report-root',type=Path)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    report_root=args.report_root if args.report_root else Path(__file__).resolve().parents[3]
    result=json.loads(json.dumps(run(report_root),default=str))
    if args.output:
        args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    else:
        need(result==json.loads(Path(__file__).with_suffix('.json').read_text()),'retained result matches fresh computation')
    print('PASS: full geometric moments, common-source reserves, complete-label samples and rare CRT witness')
