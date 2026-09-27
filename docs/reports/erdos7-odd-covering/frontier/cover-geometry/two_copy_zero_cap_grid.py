"""Exact PA cap-grid complement containing at least one zero threshold.
Stage thresholds range over 0..4, 0..5, 0..7, 0..8; queries over 1..8.
Schedules with all thresholds positive are excluded."""
from fractions import Fraction as F
from itertools import product
from functools import lru_cache
import json

@lru_cache(None)
def hinge(coords,t):
    mass=mean=F(1);low={1:F(1)} if t>1 else {}
    for p,c,u in coords:
        mass*=1-u;mean*=1-u+c/(p-1)
        probs={1:1-u-c/p}
        probs.update({n:c*F(p-1,p**n) for n in range(2,t)})
        nxt={}
        for x,v in low.items():
            for y,w in probs.items():
                if x*y<t:nxt[x*y]=nxt.get(x*y,F(0))+v*w
        low=nxt
    return mean-t*mass+sum((t-x)*v for x,v in low.items())

corners=list(product((F(0),F(1,2)),(F(0),F(1,3))))
best=None;count=valid=0;target=F(257,51)
for ts in product(range(0,5),range(0,6),range(0,8),range(0,9)):
    if 0 not in ts:continue
    count+=1;rows=[]
    for u,v in corners:
        cs=((5,F(1),u),(7,F(1),v));m=(1-u)*(1-v)-F(1,12)
        for p,t in zip((11,13,17,19),ts):
            m-=F(2,p-1-2*t)*hinge(cs,t)
            cs+=((p,F(p-1,p-1-2*t),F(0)),)
        if m<=0:break
        rows.append((u,v,cs,m))
    if len(rows)!=4:continue
    valid+=1
    for qt in range(1,9):
        vals=[qt-1+hinge(cs,qt)/m for u,v,cs,m in rows]
        r=max(vals)
        if best is None or r<best[0]:
            best=(r,ts,qt,[(str(u),str(v),str(m),str(val)) for (u,v,cs,m),val in zip(rows,vals)])
print(json.dumps({'schedules':count,'positive_schedules':valid,'target':str(target),'best_R':str(best[0]),'best_R_decimal':float(best[0]),'stages':best[1],'query_threshold':best[2],'corners':best[3],'crosses_target':best[0]<target},indent=2))
