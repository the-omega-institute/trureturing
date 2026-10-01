"""Standalone exact checker for Nine Prime Divisors in Odd Distinct Covering Systems.

Requires Python >= 3.10 and a C++17 compiler. Uses only the standard library.
No previous paper, result table, solver, floating-point optimizer, or network
resource is an input. Geometry cache entries are keyed by their full input.
Run --fresh to regenerate every integer maximum; the default reuses the cache.
"""
from collections import Counter, defaultdict
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from itertools import product
from pathlib import Path
import argparse
import json
import shutil
import subprocess
import time

if not __debug__:
    raise RuntimeError('Assertions are proof checks; do not run with -O.')
ROOT = Path(__file__).resolve().parent.parent
CACHE = ROOT/'cache'
P = (7,11,13,17,19,23)
T = (2,4,4,8,8,12)
CAP = tuple(F(p-1,p-1-t) for p,t in zip(P,T))
RATIOS = tuple(sorted({F(t,m) for t in T for m in range(1,t)}))
MODS = (3,9,27,5,15,45)
REGIONS = tuple(product((False,True),repeat=2))
PROJECTIONS = tuple(product((1,2),range(1,5),(2,4,5,7,8),(1,4,7,8,11,13,14)))
ROWS3 = tuple(r for r in range(27) if r%3 and r%9!=1 and r!=4)
ETA165 = (1,4,7,8,11,13,14)
INTEGER_QUERIES = 0
GENERATED = 0
GEOMETRY_SIZES = {}


def up(x):
    assert x >= 0
    return F(-(-x.numerator*10**10//x.denominator),10**10)


def depth(p,positive,stop):
    if not positive:
        return ((0,F(1)),),(F(1),F(0)),(F(0),F(0)),(F(1),F(0))
    atoms = tuple((j,F(p-1,p**(j+1))) for j in range(1,stop))
    retained = sum(w for j,w in atoms),sum(j*w for j,w in atoms)
    tail = F(1,p**stop),F(1,p**stop)*(stop+F(1,p-1))
    whole = F(1,p),F(1,p-1)
    assert tuple(retained[i]+tail[i] for i in range(2)) == whole
    return atoms,retained,tail,whole


@lru_cache(None)
def cells(a,b,r):
    return tuple(x for x in range(135) if x%3 and x%9!=1 and x%27!=b
                 and x%5 and x%15!=a and (r<0 or x%45!=r))


def rreps(a,b,c):
    representatives = {}
    for r in range(45):
        if r%3 and r%9!=1 and r%5 and r%15!=a:
            sig = r%3,r%9==b%9,r%5==a,r%5==c
            representatives.setdefault(sig,r)
    return tuple(representatives.values())


def weights(node,region):
    a,b,c,r,j,d,k,i,z = node
    return tuple((1 if region[0] else 4-3*(x%27==z)) *
                 (1 if region[1] else 16-4*(x%5==c)-(x%5==j)-(4-i)*(d!=0 and x%3==d and x%5==k))
                 for x in cells(a,b,r))


def counts(cs,projection):
    return tuple(sum(x%m==v for m,v in zip((3,5,9,15),projection)) for x in cs)


def coefficients(mode,u,v,m=1):
    if mode in ('current','common'):
        return (F(1,7),F(1,7),1+u,v+F(1,7),v+F(1,7),1+v,(1+u)*(1+v))
    co = [m,m,m*(1+u),m*(1+v),m*(1+v),m*(1+v),m*(1+u)*(1+v)]
    if mode=='label':
        co[4] -= F(10,11)
    return tuple(co)


def geometry(cs,ws,mode,region,projection,m,eta):
    global INTEGER_QUERIES,GENERATED
    assert 1 <= len(cs) <= 135 and len(cs)==len(ws)
    assert all(0 <= w <= 704 for w in ws)
    uv = tuple(product(range(1,12) if region[0] else (0,),range(1,9) if region[1] else (0,)))
    ts = RATIOS if mode=='ordinary' else (F(1 if mode=='current' else 2 if mode=='common' else 4),)
    off = tuple(6*s for s in counts(cs,projection)) if mode=='current' else tuple(10*(x%15==eta) for x in cs) if mode=='label' else (0,)*len(cs)
    lines = [str(len(cs))]+[f'{x} {w} {o}' for x,w,o in zip(cs,ws,off)]
    labels = []
    for u,v in uv:
        co = coefficients(mode,u,v,m)
        for t in ts:
            den = t.denominator if mode=='ordinary' else 11 if mode=='label' else 7
            base = den if mode=='ordinary' else 11*m if mode=='label' else 13 if mode=='common' else 0
            ico = [int(den*x) for x in co]
            assert all(F(x,den)==y for x,y in zip(ico,co))
            assert den>0 and t>=0 and all(x>=0 for x in ico)
            assert 0 <= base+max(off,default=0)+sum(ico) < 8192
            lines.append(' '.join(map(str,[len(labels),den,base,*ico,int(den*t)])))
            labels.append((u,v,t,den))
    payload = '\n'.join(lines)+'\n'
    key = sha256(payload.encode()).hexdigest()
    GEOMETRY_SIZES[key] = len(labels)
    path = CACHE/(key+'.json')
    if path.exists():
        raw = json.loads(path.read_text())
    else:
        run = subprocess.run([str(ROOT/'checks/geometry')],input=payload,capture_output=True,text=True,check=True)
        raw = [list(map(int,line.split())) for line in run.stdout.splitlines()]
        path.write_text(json.dumps(raw,separators=(',',':'))+'\n')
        GENERATED += 1
    assert len(raw)==len(labels)
    assert all(row[0]==i and row[1]==lab[3] and 0<=row[2]<2**30 for i,(row,lab) in enumerate(zip(raw,labels)))
    INTEGER_QUERIES += len(raw)
    table = {(u,v,t):F(row[2],den) for (u,v,t,den),row in zip(labels,raw)}
    inc = tuple(max(sum(w for x,w in zip(cs,ws) if x%g==rr) for rr in range(g)) for g in MODS)
    mass,maxweight = sum(ws),max(ws)
    offset = F(1,7)*sum(w*o for w,o in zip(ws,off)) if mode=='current' else F(1,11)*sum(w*o for w,o in zip(ws,off)) if mode=='label' else F(0)
    base = F(13,7) if mode=='common' else 0 if mode=='current' else m
    def linear(u,v):
        co = coefficients(mode,u,v,m)
        return base*mass+sum(c*h for c,h in zip(co,inc))+co[6]*maxweight+offset
    return table,linear,mass,ts


@lru_cache(maxsize=16000)
def envelope(node,mode='ordinary',projection=(),killed=False,m=1,eta=-1):
    cs = cells(node[0],node[1],node[3])
    un = counts(cs,projection) if projection else ()
    vals = None
    mass = whole = F(0)
    for region in REGIONS:
        ws = weights(node,region)
        if killed:
            ws = tuple(w*(11,11,9,6,3)[n] for w,n in zip(ws,un))
        table,linear,g_mass,ts = geometry(cs,ws,mode,region,projection,m,eta)
        if vals is None:
            vals = {t:F(0) for t in ts}
        ud,ur,ut,ua = depth(3,region[0],12)
        vd,vr,vt,va = depth(5,region[1],9)
        scale = F(1,(1 if region[0] else 6)*(1 if region[1] else 20))
        def integral(aa,bb):
            return aa[0]*bb[0]*linear(aa[1]/aa[0],bb[1]/bb[0]) if aa[0] and bb[0] else F(0)
        tail = integral(ut,va)+integral(ur,vt)
        assert tail >= 0
        mass += scale*ua[0]*va[0]*g_mass
        whole += scale*integral(ua,va)
        for t in ts:
            vals[t] += scale*(sum(p*q*table[u,v,t] for u,p in ud for v,q in vd)+tail)
    return mass,whole,vals


def update(dist,mean,p,cap):
    out = defaultdict(F)
    for m,w in dist.items():
        for e in range(31//m):
            pr = 1-cap/p if e==0 else cap*F(p-1,p**(e+1))
            out[m*(e+1)] += w*pr
    return dict(out),mean*(1+cap/F(p-1))


@lru_cache(None)
def distributions(skip7=False):
    dist,mean = {1:F(1)},F(1)
    out = []
    for p,cap in zip(P,CAP):
        out.append((dist,mean))
        if not (skip7 and p==7):
            dist,mean = update(dist,mean,p,cap)
    return tuple(out)


def expectation(env,dist,mean,t):
    mass,whole,vals = env
    low = [(m,w) for m,w in dist.items() if m<t]
    prob = sum(w for m,w in low)
    first = sum(m*w for m,w in low)
    return sum(w*m*vals[F(t,m)] for m,w in low)+(mean-first)*whole-t*(1-prob)*mass


def reserve(node):
    a,b,c,r,j,d,k,i,row = node
    z = F(1,2) if row>=0 else F(0)
    gamma15 = 3*(a==1)+(b%3==a%3)+z*(row%3==a%3)
    gamma45 = F(b%9==r%9)+z*(row%9==r%9)
    D = lambda h:F(c==h,5)+F(j==h,20)
    value = F(135,4)+gamma15+(9-gamma15)*D(a)
    if r>=0:
        value += gamma45+(3-gamma45)*D(r%5)
    if d:
        B = sum(1-z*(x%27==row) for x in cells(a,b,r) if x%3==d and x%5==k)
        value += F(9,5)-B*F(4-i,20)
    return value


@lru_cache(maxsize=3000)
def ordinary(node):
    env = envelope(node)
    return tuple(up(expectation(env,dist,mean,t)/(p-1-t))
                 for p,t,(dist,mean) in zip(P,T,distributions()))


def spatial(node,projection):
    costs = list(ordinary(node))
    costs[0] = up(envelope(node,'current',projection)[2][F(1)]/4)
    env = envelope(node)
    killed = envelope(node,'ordinary',projection,True)
    for q in range(1,6):
        dist,mean = distributions(True)[q]
        old = expectation(env,dist,mean,T[q])
        new = expectation(killed,dist,mean,T[q])
        saving = (11*old-new)/(14*(P[q]-1-T[q]))
        assert saving>=0
        costs[q] -= saving
        assert costs[q]>=0
    return tuple(costs)


def fixed165(node,projection,eta):
    total = envelope(node,'label',projection,True,1,eta)[2][F(4)]/14
    total += F(9,49)*envelope(node,'label',projection,False,2,eta)[2][F(4)]
    total += F(9,343)*envelope(node,'label',projection,False,3,eta)[2][F(4)]
    mass,whole,_ = envelope(node)
    cs = cells(node[0],node[1],node[3])
    correction = F(0)
    for region in REGIONS:
        ws = weights(node,region)
        scale = F(1,(1 if region[0] else 6)*(1 if region[1] else 20))
        scale *= (F(1,3) if region[0] else 1)*(F(1,5) if region[1] else 1)
        h15 = max(sum(w for x,w in zip(cs,ws) if x%15==r) for r in range(15))
        correction += scale*(sum(w for x,w in zip(cs,ws) if x%15==eta)-h15)
    total += F(25,1372)*whole+F(3,686)*(F(10,11)*correction-4*mass)
    return up(total/6)


def main():
    start = time.monotonic()
    def progress(message):
        print(f'[{time.monotonic()-start:.1f}s] {message}',flush=True)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fresh',action='store_true',help='regenerate every integer maximum')
    args = parser.parse_args()
    if args.fresh and CACHE.exists():
        shutil.rmtree(CACHE)
    CACHE.mkdir(parents=True,exist_ok=True)
    compiler = shutil.which('c++') or shutil.which('g++') or shutil.which('clang++')
    if compiler is None:
        raise RuntimeError('A C++17 compiler is required.')
    progress('Compiling the C++17 integer enumerator ('+
             ('fresh reconstruction' if args.fresh else 'reuse available geometry cache')+').')
    subprocess.run([compiler,'-O3','-std=c++17',str(ROOT/'checks/geometry.cpp'),'-o',str(ROOT/'checks/geometry')],check=True)
    progress('Enumerator compiled; checking finite domains and incidences.')
    assert len(RATIOS)==15 and len(PROJECTIONS)==280 and len(ROWS3)==14
    incidence_rows = {(2,2):(48,24,12,4,14,8,3), (2,4):(47,27,12,4,14,9,3),
                      (1,2):(50,32,12,4,14,8,3), (1,4):(51,36,12,4,14,9,3)}
    for (a,b),expected in incidence_rows.items():
        cs=cells(a,b,-1)
        actual=(len(cs),)+tuple(max(sum(x%g==r for x in cs) for r in range(g)) for g in MODS)
        assert actual==expected
    assert rreps(2,4,1)==(4,7,8,11,16,22,31,34)
    assert ROWS3==(2,5,7,8,11,13,14,16,17,20,22,23,25,26)
    prime_set=(3,5,7,11,13,17,19,23)
    selected=(15,21,35,45,63,75,105,165)
    def pure_power(n):
        for p in prime_set:
            q=p
            while q<n:q*=p
            if q==n:return True
        return False
    totals=[sum((F(1,d) for d in range(2,m) if m%d==0 and (pure_power(d) or d in selected)),F(0)) for m in selected]
    assert totals==list(map(F,('8/15','10/21','12/35','32/45','40/63','16/25','86/105','38/55')))
    for residue in range(75):
        if residue%3:
            overlap=sum(x%75==residue and (x%9==1 or x%27==2) for x in range(675))
            assert overlap==(3 if residue%3==1 else 1)
    ledger = []
    def add(phase,key,R,L):
        assert len(L)==6 and all(x>=0 for x in L)
        margin=R-sum(L)
        assert margin>0
        rr,ll=1000*R,1000*sum(L)
        lower=rr.numerator//rr.denominator
        upper=-(-ll.numerator//ll.denominator)
        assert lower-upper>=4
        ledger.append([phase,list(key),lower,upper])
    basic = defaultdict(list)
    basic_count=0
    progress('Starting 32 basic vertex evaluations.')
    for a,b in product((1,2),(2,4)):
        for c in (a,3-a):
            for j in range(1,5):
                node=(a,b,c,-1,j,0,0,0,-1)
                R,L=reserve(node),ordinary(node)
                basic[a,b,c].append((node,R,L))
                basic_count+=1
                if basic_count%8==0:progress(f'Basic vertices: {basic_count}/32.')
    remaining=[]
    for group,rows in basic.items():
        if all(R>sum(L) for node,R,L in rows):
            for node,R,L in rows:add('basic',(*group,node[4]),R,L)
        elif group==(2,2,1):
            for node,R,L in rows:add('basic75',(*group,node[4]),R+F(1,5),L)
        else:
            remaining.append(group)
    assert set(remaining)=={(1,4,2),(2,4,1),(2,4,2)}
    pending=[]
    mixed_count=0
    progress('Starting 700 mixed vertex evaluations.')
    for a,b,c in remaining:
        for r in rreps(a,b,c):
            for d,k in product((1,2),range(1,5)):
                if (d,k)==(a%3,a%5):continue
                for j,i in [(j,0) for j in range(1,5)]+[(k,1)]:
                    node=(a,b,c,r,j,d,k,i,-1)
                    R,L=reserve(node),ordinary(node)
                    mixed_count+=1
                    if (a,b,c)!=(2,4,1):add('mixed',node[:8],R,L)
                    elif R>sum(L):add('anchor',node[3:8],R,L)
                    else:pending.append((node,R,L))
                    if mixed_count%50==0:progress(f'Mixed vertices: {mixed_count}/700.')
    assert mixed_count==700 and len(pending)==96
    print('Basic and mixed anchors passed; 96 pending canonical vertices.',flush=True)
    coarse_bad=[]
    for node,R,L in pending:
        common=up(envelope(node,'common')[2][F(2)]/4)
        cs=cells(node[0],node[1],node[3])
        _,_,c,r,j,d,k,i,_=node
        wtotal=[20-4*(x%5==c)-(x%5==j)-(4-i)*(x%3==d and x%5==k) for x in cs]
        for proj in PROJECTIONS:
            score=sum(w*max(s-1,0) for w,s in zip(wtotal,counts(cs,proj)))
            charges=(common+F(3*score,280),)+L[1:]
            if R>sum(charges):add('coarse',node[3:8]+proj,R,charges)
            else:coarse_bad.append((node,proj,R))
    assert len(coarse_bad)==1040
    print('26880 coarse comparisons passed; 1040 need spatial evaluation.',flush=True)
    refined=[]
    for n,(node,proj,R) in enumerate(coarse_bad,1):
        L=spatial(node,proj)
        if R>sum(L):add('spatial',node[3:8]+proj,R,L)
        else:refined.extend((node[:-1]+(z,),proj) for z in ROWS3)
        if n%100==0:print('Spatial',n,'/1040;',round(time.monotonic()-start,1),'s',flush=True)
    assert len(refined)==518
    final=[]
    for n,(node,proj) in enumerate(refined,1):
        R,L=reserve(node),spatial(node,proj)
        if R>sum(L):add('pure3',node[3:8]+proj+(node[-1],),R,L)
        else:final.append((node,proj,R,L))
        if n%100==0:print('Pure-3',n,'/518;',round(time.monotonic()-start,1),'s',flush=True)
    assert len(final)==12
    reps={}
    for node,proj,R,L in final:
        assert node[3]==8 and node[4] in (1,3) and node[5:8]==(2,1,0) and node[-1] in (13,22)
        assert proj in ((1,4,7,14),(2,4,2,14),(2,4,5,14))
        name=('A' if proj==(1,4,7,14) else 'B')+str(node[4])
        if name in reps:assert (R,L)==reps[name][2:]
        if node[-1]==13 and proj[2]!=5:reps[name]=(node,proj,R,L)
    assert set(reps)=={'A1','B1','A3','B3'}
    closing=[]
    for name,(node,proj,R,L) in sorted(reps.items()):
        available=R-sum(x for j,x in enumerate(L) if j!=1)
        for eta in ETA165:
            cost=fixed165(node,proj,eta)
            add('closing',(name,eta),R,L[:1]+(cost,)+L[2:])
            closing.append(dict(state=name,eta=eta,available=str(available),cost=str(cost)))
    # Directly verify the elementary prefix permutations used in the paper.
    crt={(x%27,x%5):x for x in range(135)}
    for node,proj,R,L in final:
        def transform(x):
            y=x%27
            if proj[2]==5 and y%9 in (2,5):y+=3 if y%9==2 else -3
            if node[-1]==22 and y in (13,22):y=35-y
            return crt[y,x%5]
        perm=[transform(x) for x in range(135)]
        assert sorted(perm)==list(range(135)) and all(perm[x]%15==x%15 for x in range(135))
        cs=cells(node[0],node[1],node[3])
        assert {perm[x] for x in cs}==set(cs)
        target=(1,4,7,14) if proj==(1,4,7,14) else (2,4,2,14)
        assert all(counts((x,),proj)==counts((perm[x],),target) for x in cs)
        for g in (*MODS,135):
            images=[{perm[x]%g for x in range(135) if x%g==r} for r in range(g)]
            assert all(len(s)==1 for s in images) and len({next(iter(s)) for s in images})==g
        for reg in REGIONS:
            old=dict(zip(cs,weights(node,reg)))
            new=dict(zip(cs,weights(node[:-1]+(13,),reg)))
            assert all(old[x]==new[perm[x]] for x in cs)
    phase=Counter(r[0] for r in ledger)
    assert phase==dict(basic=16,basic75=4,mixed=420,anchor=184,coarse=25840,spatial=1003,pure3=506,closing=28)
    assert len({(r[0],tuple(r[1])) for r in ledger})==28001
    minimum=min(r[2]-r[3] for r in ledger)
    assert minimum==4
    floor=lambda x:x.numerator//x.denominator
    ceil=lambda x:-(-x.numerator//x.denominator)
    assert min(floor(1000*F(r['available'])) for r in closing)==5310
    assert max(ceil(1000*F(r['cost'])) for r in closing)==5299
    output=ROOT/'certificate'
    output.mkdir(exist_ok=True)
    certificate=dict(mass_denominator=135000,row_format=['phase','configuration','reserve_lower','loss_upper'],rows=ledger)
    (output/'integer_certificate.json').write_text(json.dumps(certificate,separators=(',',':'))+'\n')
    (output/'closing.json').write_text(json.dumps(closing,indent=2)+'\n')
    result=dict(passed=True,thresholds=T,caps=list(map(str,CAP)),distinct_ratios=len(RATIOS),
                basic_vertices=32,mixed_vertices=700,coarse_evaluations=26880,spatial_evaluations=1040,
                pure3_evaluations=518,residual_vertices=12,closing_expectations=28,
                ledger_entries=len(ledger),phase_counts=dict(phase),minimum_integer_surplus=minimum,
                minimum_constructed_mass='1/33750',closing_budget_lower=5310,closing_loss_upper=5299,
                geometry_calls_integer_queries=INTEGER_QUERIES,new_geometry_files=GENERATED,
                distinct_geometry_batches=len(GEOMETRY_SIZES),
                distinct_integer_queries=sum(GEOMETRY_SIZES.values()),
                run_mode='fresh' if args.fresh else 'cache_reuse',
                elapsed_seconds_display_only=time.monotonic()-start)
    (output/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2),flush=True)


if __name__=='__main__':main()
