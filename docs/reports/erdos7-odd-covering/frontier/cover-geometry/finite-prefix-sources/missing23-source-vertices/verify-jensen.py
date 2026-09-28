"""Exact uniform exchange-gap lower bound for the fixed full44-cell source.

At each stage retain the positive-depth comparison components of the
preceding charged primes among7,11,13. Their cell field is1, their physical
tuple remains fixed, and the later multiplier laws are those of
missing23/query16. No joint-head geometry is enumerated. Product laws here
are comparator tensors, not a claim of independent actual prime events.
"""
from fractions import Fraction as F
import json


def need(condition,message):
    if not condition:
        raise ValueError(message)


MODS=(3,9,27,5,15,45,135)
CELLS=tuple(x for x in range(135) if x%3 and x%9!=1 and x%27!=4
            and x%5 and x%15!=2 and x%45!=8)
need(len(CELLS)==44,'fixed native carrier')
CRT={(x%27,x%5):x for x in range(135)}


def sigma(x):
    r=x%27
    if r%9==4:
        r+=3
    elif r%9==7:
        r-=3
    return CRT[r,x%5]


def weights(z,positive5):
    return tuple(F(4-3*(x%27==z),6)*
                 (1 if positive5 else
                  F(16-5*(x%5==1)-4*(x%3==2 and x%5==1),20))
                 if x in CELLS else F(0) for x in range(135))


def head_maxima(weights):
    return tuple(max(sum((weights[x] for x in range(135) if x%g==r),F(0))
                     for r in range(g)) for g in MODS)


incidences=[]
for positive5 in (False,True):
    a,b=weights(13,positive5),weights(7,positive5)
    sa=tuple(a[sigma(x)] for x in range(135))
    ha,hs,hb=map(head_maxima,(a,sa,b))
    gap=tuple(F(4,7)*x+F(3,7)*y-z for x,y,z in zip(ha,hs,hb))
    expected=F(2) if positive5 else F(59,40)
    need(gap==(F(0),expected,F(0),F(0),F(0),F(0),F(0)),
         'only modulo9 contributes')
    # The synthetic mixture and the actual new source have the same
    # mod9/column masses, so every physical selected offset cancels in J.
    v=tuple(F(4,7)*x+F(3,7)*y for x,y in zip(a,sa))
    need(all(sum(v[x] for x in range(135) if x%9==r and x%5==c)
             ==sum(b[x] for x in range(135) if x%9==r and x%5==c)
             for r in range(9) for c in range(5)),
         'joint branch/column offset cancellation')
    incidences.append(dict(positive5=positive5,A=list(map(str,ha)),
        sigmaA=list(map(str,hs)),B=list(map(str,hb)),gap=list(map(str,gap))))

JOINT_GAP=F(59,40)+F(1,5)*2
need(JOINT_GAP==F(15,8),'all positive5 depths included')


def multiplier(p,t,positive=False):
    cap=F(p-1,p-1-t)
    p1=1-cap/p
    low={m:(F(0) if positive else p1) if m==1
         else cap*F(p-1,p**m) for m in range(1,16)}
    return low,(cap/p if positive else F(1)),1+cap/F(p-1)-(p1 if positive else 0)


def multiply(a,b):
    low={m:sum((v*w for i,v in a[0].items() for j,w in b[0].items()
                if i*j==m),F(0)) for m in range(1,16)}
    return low,a[1]*b[1],a[2]*b[2]


def tail(dist,threshold):
    low,mass,mean=dist
    removed={m:w for m,w in low.items() if m<threshold and w}
    tail_mass=mass-sum(removed.values(),F(0))
    tail_mean=mean-sum((m*w for m,w in removed.items()),F(0))
    need(tail_mean>=threshold*tail_mass>=0,'complete exact multiplier tail')
    return tail_mass,tail_mean,removed


parts=[]
dist=multiplier(7,2,True)
for p,t in ((11,4),(13,4)):
    mass,mean,removed=tail(dist,t)
    c=F(p-1,p)
    gain=F(14,p-1-t)*JOINT_GAP*(mean-c*mass)
    parts.append(dict(stage=p,threshold=t,tail_mass=str(mass),
        tail_mean=str(mean),removed_atoms={str(k):str(v) for k,v in removed.items()},
        gain=str(gain)))
    dist=multiply(dist,multiplier(p,t,True))
need(all(not w or m>=8 for m,w in dist[0].items()),'positive-depth minimum8')
for p,t in ((17,8),(19,8),(29,16)):
    mass,mean,removed=tail(dist,t)
    c=F(p-1,p)
    gain=F(14,p-1-t)*JOINT_GAP*(mean-c*mass)
    parts.append(dict(stage=p,threshold=t,tail_mass=str(mass),
        tail_mean=str(mean),removed_atoms={str(k):str(v) for k,v in removed.items()},
        gain=str(gain)))
    dist=multiply(dist,multiplier(p,t))
mass,mean,removed=tail(dist,16)
parts.append(dict(stage='H16',threshold=16,tail_mass=str(mass),
    tail_mean=str(mean),removed_atoms={str(k):str(v) for k,v in removed.items()},
    gain=str(JOINT_GAP*mean)))
total=sum((F(x['gain']) for x in parts),F(0))
need(total==F(17380330052871025,23681506976038912),'exact six-part common exchange gap')
delta=F(116,15625)
print(json.dumps(dict(scope=__doc__,moduli=MODS,incidences=incidences,
    joint_mod9_gap=str(JOINT_GAP),parts=parts,
    later_four_part_sum=str(sum((F(x['gain']) for x in parts[2:]),F(0))),
    uniform_J_lower_bound=str(total),uniform_J_decimal=float(total),
    sufficient_dplus_bound=str(F(7,3)*total),
    strict_margin_dplus_threshold=str(F(7,3)*(total+delta)),
    boundary='A uniform same-source Gplus difference bound below the displayed threshold is still missing; no full physical-tuple or unrestricted Erdos7 conclusion is asserted.'),indent=2))
