"""Exact controls for adaptive prefix bounds and event-address jump trees.
No external inputs, old checker imports, or broad filesystem access.
"""
from fractions import Fraction as F
import argparse
from math import prod
from random import Random
from pathlib import Path
import json

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', required=True)
args = parser.parse_args()

checks = 0

def need(ok, msg):
    global checks
    checks += 1
    if not ok:
        raise ValueError(msg)

def contains(p, v, t):
    return v[0] <= t[0] and (t[1]-v[1]) % p**v[0] == 0

def canon(p, cs):
    out = []
    for c in sorted(set((d,a%p**d) for d,a in cs)):
        if not any(contains(p,b,c) for b in out):
            out.append(c)
    return out

def intersection(p, a, b):
    if contains(p,a,b): return b
    if contains(p,b,a): return a
    return None

def haar(p, cs):
    return sum((F(1,p**d) for d,a in canon(p,cs)),F(0))

def intersect_union(p, aa, bb):
    return canon(p,[c for a in aa for b in bb
                    if (c:=intersection(p,a,b)) is not None])

class Model:
    def __init__(self, holes, stars, events):
        self.holes = {q:canon(q,cs) for q,cs in holes.items()}
        self.stars = canon(5,stars)
        self.events = list(events)
        self.qs = sorted(q for q in holes if q != 5)
        self.norm = {q:1/(1-haar(q,cs)) for q,cs in self.holes.items()}
        self.deleted5 = canon(5,self.holes[5]+self.stars)
        need(len({e['label'] for e in events}) == len(events),'Original identity retained')
        self.nodes = sorted({(0,0)} | {e['t'] for e in events})
        self.children = {v:[] for v in self.nodes}
        for t in self.nodes[1:]:
            par = max((v for v in self.nodes if v != t and contains(5,v,t)),key=lambda v:v[0])
            self.children[par].append(t)
    def qm(self,q,cs):
        aa=canon(q,cs)
        return self.norm[q]*(haar(q,aa)-haar(q,intersect_union(q,aa,self.holes[q])))
    def w(self,v):
        return self.norm[5]*(haar(5,[v])-haar(5,intersect_union(5,[v],self.deleted5)))
    def data(self,v):
        active={q:canon(q,[e['c'] for e in self.events if e['q']==q and contains(5,e['t'],v)]) for q in self.qs}
        pending=[e for e in self.events if e['t'] != v and contains(5,v,e['t'])]
        envelope={q:canon(q,active[q]+[e['c'] for e in pending if e['q']==q]) for q in self.qs}
        return active,pending,envelope
    def bounds(self,v):
        aa,pending,ee=self.data(v)
        av={q:self.qm(q,aa[q]) for q in self.qs}
        ev={q:self.qm(q,ee[q]) for q in self.qs}
        lo=self.w(v)*(1-prod(1-av[q] for q in self.qs))
        en=self.w(v)*(1-prod(1-ev[q] for q in self.qs))
        raw=lo
        for e in pending:
            q=e['q']
            novelty=self.qm(q,[e['c']])-self.qm(q,intersect_union(q,[e['c']],aa[q]))
            raw+=self.w(e['t'])*novelty*prod(1-av[r] for r in self.qs if r!=q)
        return lo,min(en,raw),en,raw
    def exact_tree(self,v=(0,0)):
        aa,_,_=self.data(v)
        f=1-prod(1-self.qm(q,aa[q]) for q in self.qs)
        shell=self.w(v)-sum((self.w(c) for c in self.children[v]),F(0))
        need(shell>=0,'Nonnegative exact jump shell')
        return shell*f+sum((self.exact_tree(c) for c in self.children[v]),F(0))
    def refinement(self):
        frontier={(0,0)}
        exact=F(0)
        out=[]
        while True:
            bs={v:self.bounds(v) for v in frontier}
            lo=exact+sum((b[0] for b in bs.values()),F(0))
            hi=exact+sum((b[1] for b in bs.values()),F(0))
            out.append((lo,hi,len(frontier)))
            if not frontier: break
            v=max(frontier,key=lambda v:bs[v][1]-bs[v][0])
            frontier.remove(v)
            aa,_,_=self.data(v)
            f=1-prod(1-self.qm(q,aa[q]) for q in self.qs)
            exact+=(self.w(v)-sum((self.w(c) for c in self.children[v]),F(0)))*f
            frontier.update(self.children[v])
        return out
    def reference(self):
        # Independent finite enumeration of coordinate support, no antichain mass calls.
        depths={q:max([d for d,a in self.holes[q]]+[e['c'][0] for e in self.events if e['q']==q]+[0]) for q in self.qs}
        depths[5]=max([d for d,a in self.holes[5]+self.stars]+[e['t'][0] for e in self.events]+[0])
        survivors={q:[x for x in range(q**depths[q]) if not any(x%q**d==a for d,a in self.holes[q])] for q in depths}
        out=F(0)
        for x in survivors[5]:
            if any(x%5**d==a for d,a in self.stars): continue
            active=[e for e in self.events if x%5**e['t'][0]==e['t'][1]]
            covered={q:sum(any(e['q']==q and z%q**e['c'][0]==e['c'][1] for e in active) for z in survivors[q]) for q in self.qs}
            out+=F(1,len(survivors[5]))*(1-prod(1-F(covered[q],len(survivors[q])) for q in self.qs))
        return out

def validate(m):
    ref=m.reference()
    need(m.exact_tree()==ref,'Jump-tree exact value equals independent leaf enumeration')
    rows=m.refinement()
    lastlo,lastup=F(0),m.w((0,0))
    for lo,hi,n in rows:
        need(lastlo<=lo<=ref<=hi<=lastup,'Adaptive sandwich and refinement monotonicity')
        lastlo,lastup=lo,hi
    need(rows[-1][0]==rows[-1][1]==ref,'Terminal interval exact')
    for v in m.nodes:
        lo,up,en,raw=m.bounds(v)
        aa,_,_=m.data(v)
        f=1-prod(1-m.qm(q,aa[q]) for q in m.qs)
        shell=m.w(v)-sum((m.w(c) for c in m.children[v]),F(0))
        cs=[m.bounds(c) for c in m.children[v]]
        need(shell*f+sum((b[2] for b in cs),F(0))<=en,'Envelope upper individually monotone')
        need(shell*f+sum((b[3] for b in cs),F(0))<=raw,'Novelty upper individually monotone')
    return {'labels':len(m.events),'tree_nodes':len(m.nodes),'leaf_count':5**max([e['t'][0] for e in m.events]+[0]),'exact':str(ref),'initial_upper':str(rows[0][1]),'steps':len(rows)-1,'intervals':[[str(lo),str(hi)] for lo,hi,n in rows]}

rng=Random(770057)
fixtures=[]
for trial in range(32):
    holes={q:[(1,0),(2,1+q),(2,0)] for q in (5,7,11)} # Includes nested/duplicate hole coverage.
    stars=[(1,2),(2,3+5)]
    events=[]
    choices=[(q,a,e,t) for q in (7,11) for a in range(1,4) for e in range(1,3) for t in (1,3)]
    rng.shuffle(choices)
    for q,a,e,t in choices[:rng.randrange(2,13)]:
        events.append({'label':t*5**a*q**e,'q':q,'t':(a,rng.randrange(5**a)),'c':(e,rng.randrange(q**e))})
    fixtures.append(validate(Model(holes,stars,events)))
    # Safe insertion rebuild: actual identity/source registry preserved, all bounds recertified.
    q,a,e,t=next(z for z in choices if z[3]*5**z[1]*z[0]**z[2] not in {x['label'] for x in events})
    events.append({'label':t*5**a*q**e,'q':q,'t':(a,rng.randrange(5**a)),'c':(e,rng.randrange(q**e))})
    validate(Model(holes,stars,events))

heights={5:5,7:5,11:4}
holes={q:[(e,0 if e==1 else 1+q**(e-1)) for e in range(1,h+1)] for q,h in heights.items()}
stars=[(e,2 if e==1 else 3+5**(e-1)) for e in range(1,6)]
# Newly tests the adaptive algorithm; does not rerun the earlier checker.
source_events=[{'label':55,'q':11,'t':(1,4),'c':(1,4)}, {'label':525,'q':7,'t':(2,4),'c':(1,4)}]
m=Model(holes,stars,source_events)
rows=m.refinement()
exact=m.exact_tree()
need(all(lo<=exact<=hi for lo,hi,n in rows),'Conditional-overlap example intervals valid')
need(all(rows[i+1][0]>=rows[i][0] and rows[i+1][1]<=rows[i][1] for i in range(len(rows)-1)),'Conditional-overlap example monotone')
raw=sum((m.w(e['t'])*m.qm(e['q'],[e['c']]) for e in source_events),F(0))
credit=raw-exact
need(credit==F(399466375,432601753328),'New bound recovers actual cross-depth overlap credit')
need(m.bounds((1,4))[1]==exact,'Inherited novelty bound extracts credit before deepest split')

# Height-1000 control: no ambient leaf enumeration; literal labels remain integers.
high_events=[
    {'label':55,'q':11,'t':(1,4),'c':(1,4)},
    {'label':3*5**1000*7,'q':7,'t':(1000,4),'c':(1,4)},
    {'label':3*5**1000*11,'q':11,'t':(1000,9),'c':(1,5)}]
hm=Model({q:[(1,0)] for q in (5,7,11)},[(1,2)],high_events)
hx=F(1,40)+F(1,16*5**999)
need(len(hm.nodes)==4,'Height-1000 event tree has four nodes')
need(hm.exact_tree()==hx,'Height-1000 exact closed form without leaf enumeration')
hr=hm.refinement()
need(all(lo<=hx<=hi for lo,hi,n in hr),'Height-1000 adaptive sandwich')
need(all(hr[i+1][0]>=hr[i][0] and hr[i+1][1]<=hr[i][1] for i in range(len(hr)-1)),'Height-1000 refinement monotone')
need(hm.bounds((1,4))[1]==hx,'Height-1000 novelty upper exact before deep split')
high_result={'max_five_depth':1000,'labels':['55','3*5^1000*7','3*5^1000*11'],'nodes':len(hm.nodes),'exact_expression':'1/40 + 1/(16*5^999)','ambient_leaves_expression':'5^1000','exact_numerator':str(hx.numerator),'exact_denominator':str(hx.denominator),'steps':len(hr)-1}

result={'contract':'Finite actual support-{5,q} events, fixed same-source coordinate laws, exact pure-hole unions. No optimization over unknown phases and no unrestricted covering theorem.','height_1000_example':high_result,'seed':770057,'random_initial_sources':32,'random_insertion_sources':32,'checks':checks,'fixtures':fixtures,'conditional_overlap_example':{'nodes':len(m.nodes),'ambient_five_leaves':5**5,'exact':str(exact),'independent_charge':str(raw),'credit':str(credit),'intervals':[[str(lo),str(hi)] for lo,hi,n in rows]}}
Path(args.output).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'checks':checks,'sources':64,'credit':str(credit),'example_intervals':result['conditional_overlap_example']['intervals'],'max_random_nodes':max(f['tree_nodes'] for f in fixtures),'max_random_leaves':max(f['leaf_count'] for f in fixtures)},sort_keys=True))
