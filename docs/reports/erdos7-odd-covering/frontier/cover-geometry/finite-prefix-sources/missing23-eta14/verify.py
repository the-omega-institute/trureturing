"""Exact arithmetic and all-label routing for one missing23 comparison node.

Numerical current/envelope inputs are inherited finite-comparison bounds.
Use geometry_replay.py for integer-geometry replay; this checker does not claim
that merely reading those inputs independently regenerates their maxima.
"""
from collections import Counter, defaultdict
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from pathlib import Path
import argparse, hashlib, json

ROOT=Path(__file__).resolve().parent

# This literal pin fixes every numerical prerequisite, source and retained raw
# support-rebuild result. Dynamic hash reporting alone would not certify input.
MANIFEST_SHA256 = "812771d19270ad2447fbacd1d59a045ba6a04d5bb9580d86679678490adce091"
def check_inputs():
    raw=(ROOT/'inputs.sha256.json').read_bytes()
    if hashlib.sha256(raw).hexdigest()!=MANIFEST_SHA256:
        raise ValueError('fixed input manifest mismatch')
    manifest=json.loads(raw)
    for name,expected in manifest.items():
        if Path(name).is_absolute() or '..' in Path(name).parts:
            raise ValueError('invalid manifest-relative path')
        if hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=expected:
            raise ValueError('pinned input mismatch: '+name)
check_inputs()
DATA=json.loads((ROOT/'bounds.json').read_text())
CUTOFF=20
A=(2,4,2,14); B=(2,4,5,14); C=(2,4,8,14)
DOMAIN=tuple(product((1,2),range(1,5),(2,4,5,7,8),(14,)))
CELLS=tuple(x for x in range(135) if x%3 and x%9!=1 and x%27!=4 and x%5 and x%15!=2 and x%45!=8)

def demand(condition,message):
    if not condition:raise ValueError(message)

def ceil_fraction(x,scale=10**10):
    demand(x>=0,'nonnegative upper bound')
    return F(-(-x.numerator*scale//x.denominator),scale)

def full(p,t):
    cap=F(p-1,p-1-t)
    return ({m:1-cap/p if m==1 else cap*F(p-1,p**m) for m in range(1,CUTOFF)},1+cap/F(p-1),F(1))

def mul(a,b):
    table=defaultdict(F)
    for m,x in a[0].items():
        for n,y in b[0].items():
            if m*n<CUTOFF:table[m*n]+=x*y
    return dict(table),a[1]*b[1],a[2]*b[2]

UNIT=({1:F(1)},F(1),F(1))
POS7=({m:F(9,7**m) for m in range(2,CUTOFF)},F(13,28),F(3,14))
POS11=({m:F(50,3*11**m) for m in range(2,CUTOFF)},F(7,22),F(5,33))
ENVS={tuple(map(int,k.split(','))):(F(r['mass']),F(r['whole']),{F(t):F(x) for t,x in r['values'].items()}) for k,r in DATA['ordinary_envelopes'].items()}

def upper(t,e):
    a,w,values=e
    if t<=1:return w-t*a
    if t in values:return values[t]
    lo=max(x for x in values if x<t);hi=min(x for x in values if x>t)
    return ((hi-t)*values[lo]+(t-lo)*values[hi])/(hi-lo)

def hinge(t,d,e):
    low={m:x for m,x in d[0].items() if m<t}
    p=sum(low.values(),F(0));w=sum((m*x for m,x in low.items()),F(0))
    demand(0<=p<=d[2] and 0<=w<=d[1],'true positive multiplier remainder')
    answer=sum((m*x*upper(F(t,m),e) for m,x in low.items()),F(0))+(d[1]-w)*e[1]-t*(d[2]-p)*e[0]
    demand(answer>=0,'nonnegative hinge bound')
    return answer

def continuation(flat):
    if flat:
        parts={(0,0,0):(POS7,F(1)),(1,0,0):(UNIT,F(1,14))}
        prefix=((11,4),(13,4))
    else:
        parts={(a,b,0):(mul(UNIT if a else POS7,UNIT if b else POS11),F(1,14**a*33**b)) for a,b in product((0,1),repeat=2)}
        prefix=((13,4),)
    for p,t in prefix:parts={k:(mul(d,full(p,t)),c) for k,(d,c) in parts.items()}
    losses=[]
    for p,t in ((17,8),(19,8),(29,16)):
        h=sum((c*hinge(t,d,ENVS[k]) for k,(d,c) in parts.items()),F(0))
        losses.append(ceil_fraction(h/F(p-1-t)))
        parts={k:(mul(d,full(p,t)),c) for k,(d,c) in parts.items()}
    queries={t:sum((c*hinge(t,d,ENVS[k]) for k,(d,c) in parts.items()),F(0)) for t in (16,20)}
    return losses,queries

@lru_cache(None)
def three_cell_correction(t,m):
    answer=F(0)
    for u_positive,v_positive in product((False,True),repeat=2):
        weight=(1 if u_positive else 4)*(1 if v_positive else 16)
        scale=F(1,(1 if u_positive else 6)*(1 if v_positive else 20))
        us=tuple((u,F(2,3**(u+1))) for u in range(1,t)) if u_positive else ((0,F(1)),)
        vs=tuple((v,F(4,5**(v+1))) for v in range(1,t)) if v_positive else ((0,F(1)),)
        for v,pv in vs:
            a=m*(6+3*v)-t
            value=sum((pu*(2*max(0,-a)+max(0,-a-m*(1+u)*(2+v))) for u,pu in us),F(0))
            if u_positive:value+=F(1,3**t)*2*max(0,-a)
            answer+=scale*weight*pv*value
    return answer

def three_cell_hinge(t,d):
    return d[1]*F(189,8)-t*d[2]*3+sum((p*three_cell_correction(t,m) for m,p in d[0].items() if 6*m<t),F(0))

def perturbation(prior,divisor):
    nu7=({m:F(9,14) if m==1 else F(9,7**m) for m in range(1,CUTOFF)},F(31,28),F(6,7))
    d=mul(nu7,full(prior,4));losses=[]
    for p,t in ((17,8),(19,8),(29,16)):
        losses.append(three_cell_hinge(t,d)/F(divisor*(p-1-t)))
        d=mul(d,full(p,t))
    return losses

def swap(x):return x[:2]+({2:5,5:2}.get(x[2],x[2]),)+x[3:]

def field(x):
    support=tuple(z for z in CELLS if all(z%m==a for m,a in zip((3,5,9,15),x)))
    expected={A:(29,74,119),B:(14,59,104),C:(44,89,134)}.get(x,())
    demand(support==expected,'exact four-way intersection classification')
    return x if support else None

def load_table(rows):
    result={tuple(r['xi']):F(r['cost']) for r in rows}
    demand(set(result)==set(DOMAIN) and len(rows)==40,'complete unique eta14 table')
    return result

def verify():
    demand(DATA['model']['node']==[2,4,1,8,1,2,1,0,13] and DATA['model']['xi7']==[1,4,7,14],'fixed comparison-node scope')
    demand(DATA['model']['thresholds']==[2,4,4,8,8,16] and DATA['model']['query']==16,'single source schedule and query')
    # Prefix permutation preserves each original source category and the anchor.
    crt={(x%27,x%5):x for x in range(135)}
    def perm(x):
        z=x%27
        z+=3 if z%9==2 else -3 if z%9==5 else 0
        return crt[z,x%5]
    demand({perm(x) for x in CELLS}==set(CELLS),'core transport')
    for xi in DOMAIN:
        demand(swap(xi) in DOMAIN,'closed projection transport')
        demand(all((x%m==a)==(perm(x)%m==b) for x in range(135) for m,a,b in zip((3,5,9,15),xi,swap(xi))),'individual selected-class transport')
        field(xi)
    for q,t in ((17,8),(19,8),(29,16)):
        cap=F(q-1,q-1-t)
        demand(all(min(F(1),cap*F(q-1-s,q))-cap/q==1-cap/q for s in range(5)),'constant later zero comparison')
    l7=F(DATA['current7']);l11=load_table(DATA['current11'])
    l13={k:load_table(v) for k,v in DATA['current13'].items()}
    uniform={int(k):max(load_table(v).values()) for k,v in DATA['uniform_currents'].items()}
    ordinary,query=continuation(True);charged,charged_query=continuation(False)
    h16=query[16]
    lift11=perturbation(13,11);lift13=perturbation(11,13)
    demand(lift11[0]==F(1243323,10250240),'independent flat17 enlargement')
    flat17=ceil_fraction(uniform[17]+lift11[0])
    cc=list(map(F,DATA['CC']['losses']))
    demand(cc[0]==l7 and cc[1]==l11[C] and tuple(DATA['CC']['xi11'])==C and tuple(DATA['CC']['xi13'])==C,'CC source identity')
    demand(cc[2]==F(DATA['CC']['current13']) and cc[3:]==list(map(F,DATA['CC']['released17_19_29'])),'CC duplicated numerical inputs agree')
    rows=[];counts=Counter();old_residual=0
    for x11,x13 in product(DOMAIN,repeat=2):
        mapped=swap(x13) if x11==B else x13
        cost13=l13['B2'][mapped] if x11 in (A,B) else l13['flat'][x13]
        fixed=[l7,l11[x11],cost13]
        if x11 in (A,B):old=fixed+[uniform[17],charged[1],charged[2]];oldh=charged_query[20]
        else:old=fixed+[flat17,ordinary[1],ordinary[2]];oldh=query[20]
        oldd=F(135,4)-sum(old,F(0))
        if 10*oldd>oldh:
            costs=old;route='ordinary'
        else:
            old_residual+=1;options=[]
            for b11,b13 in ((A,B),(B,A)):
                changed11=field(x11)!=b11;changed13=field(x13)!=b13
                late=[]
                for i,p in enumerate((17,19,29)):
                    delta=(lift11[i] if changed11 else 0)+(lift13[i] if changed13 and i>0 else 0)
                    late.append(min(uniform[p]+delta,ordinary[i]))
                options.append(fixed+late)
            costs=min(options,key=lambda r:sum(r,F(0)));route='transfer'
            if x11==C and x13==C:costs=cc;route='CC-release'
        live=F(135,4)-sum(costs,F(0))
        demand(live>0,'positive live lower bound')
        g=14*sum(costs,F(0))+h16;slack=14*F(135,4)-g
        demand(slack>0,'uniform query16 route fails')
        upper16=15+h16/live
        micro=[int(ceil_fraction(x,10**6)*10**6) for x in costs]
        live_micro=33750000-sum(micro);h_micro=int(ceil_fraction(h16,10**6)*10**6)
        slack_micro=14*live_micro-h_micro
        demand(slack_micro>0,'rounding must retain strict positivity')
        counts[route]+=1
        rows.append(dict(xi11=list(x11),xi13=list(x13),route=route,loss_micro=micro,live_lower_micro=live_micro,slack_lower_micro=slack_micro,query_upper=str(ceil_fraction(upper16)),query_upper_decimal=float(ceil_fraction(upper16))))
    demand(len(rows)==1600 and old_residual==38,'full1600 partition and38 residuals')
    demand(dict(counts)=={'ordinary':1562,'transfer':37,'CC-release':1},'complete branch routing')
    worst=max(rows,key=lambda r:F(r['query_upper']))
    return dict(scope='One fixed node A1, xi7=A, all40 eta14 physical projections independently at11/13/17/19/29; not all anchors, xi7 or eta values.',source_thresholds=[2,4,4,8,8,16],query=16,route_counts=dict(counts),covered_label_pairs=1600,remaining_projection_choices_per_pair=40**3,total_parameter_tuples=40**5,H16=str(h16),H16_decimal=float(h16),H16_upper_micro=int(ceil_fraction(h16,10**6)*10**6),worst=worst,minimum_micro_slack=min(r['slack_lower_micro'] for r in rows),bounds_sha256=hashlib.sha256((ROOT/'bounds.json').read_bytes()).hexdigest(),verification='Exact arithmetic and complete label routing, conditional on the inherited numerical current/envelope bounds; geometry is a separate replay surface.',routes=rows)

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path);args=parser.parse_args()
    result=verify()
    if args.output:args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='routes'},indent=2))
