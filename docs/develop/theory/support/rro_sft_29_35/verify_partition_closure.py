#!/usr/bin/env python3
"""Exact finite checks for the PR #8336 paper-level partition extension.
No floating-point arithmetic, external packages, or remote writes.
These tests are not a proof of the universal statements or a Lean receipt.
"""
from __future__ import annotations
import argparse, hashlib, itertools, json, random
from collections import deque
from pathlib import Path

SEED = 2026092408336

def partitions(n: int, cap: int | None = None):
    if n == 0:
        yield ()
        return
    for a in range(min(n, cap if cap is not None else n), 0, -1):
        for rest in partitions(n - a, a):
            yield (a,) + rest

def padded(p, n):
    return tuple(p) + (0,) * (n - len(p))

def distance(p, q):
    n = max(len(p), len(q))
    return max((abs(a-b) for a,b in zip(padded(p,n),padded(q,n))), default=0)

def geodesic(p, q):
    if sum(p) != sum(q) or not p or not q:
        raise ValueError('Use nonempty partitions of the same positive integer.')
    n = sum(p)
    a, b = padded(p,n), padded(q,n)
    path = [tuple(p)]
    while a != b:
        d = distance(a,b)
        lo = [max(0, a[i]-1, b[i]-(d-1), min(a[i],b[i])) for i in range(n)]
        hi = [min(a[i]+1, b[i]+(d-1), max(a[i],b[i])) for i in range(n)]
        assert all(lo[i] <= hi[i] for i in range(n))
        assert sum(lo) <= n <= sum(hi)
        budget = n-sum(lo)
        nxt = lo[:]
        for i in range(n):
            add = min(budget, hi[i]-nxt[i])
            nxt[i] += add
            budget -= add
        assert budget == 0 and sum(nxt) == n
        assert all(nxt[i] >= nxt[i+1] for i in range(n-1))
        assert distance(a,nxt) <= 1 and distance(nxt,b) == d-1
        assert all(min(a[i],b[i]) <= nxt[i] <= max(a[i],b[i]) for i in range(n))
        a = tuple(nxt)
        path.append(tuple(v for v in a if v))
    assert len(path)-1 == distance(p,q)
    return path

def zeros(n,k):
    return [[0]*k for _ in range(n)]

def matmul(a,b):
    n,k = len(a), len(b)
    m = len(b[0]) if b else 0
    assert all(len(row)==k for row in a)
    out=zeros(n,m)
    for i in range(n):
        for h,x in enumerate(a[i]):
            if x:
                for j,y in enumerate(b[h]):
                    if y:
                        out[i][j] += x*y
    return out

def jordan(p):
    a=zeros(sum(p),sum(p)); start=0
    for size in p:
        for j in range(size-1): a[start+j][start+j+1]=1
        start += size
    return a

def adjacent_factors(p,q):
    if sum(p) != sum(q) or distance(p,q)>1:
        raise ValueError('Partitions must have equal mass and distance at most one.')
    n=sum(p); a=zeros(n,n); b=zeros(n,n)
    ro=co=0
    for r,c in zip(padded(p,n),padded(q,n)):
        if r==c:
            for j in range(r): a[ro+j][co+j]=1
            for j in range(r-1): b[co+j][ro+j+1]=1
        elif r==c+1:
            for j in range(c):
                a[ro+j][co+j]=1
                b[co+j][ro+j+1]=1
        elif c==r+1:
            for j in range(r):
                a[ro+j][co+j+1]=1
                b[co+j][ro+j]=1
        else:
            raise AssertionError('Unmatched block dimensions.')
        ro += r; co += c
    assert ro==co==n
    assert matmul(a,b)==jordan(p) and matmul(b,a)==jordan(q)
    return a,b

class Group:
    def __init__(self,name,elements,mul,identity):
        self.name=name; self.elements=elements; self.q=len(elements)
        ids={x:i for i,x in enumerate(elements)}
        self.e=ids[identity]
        self.mul=[[ids[mul(a,b)] for b in elements] for a in elements]
        self.inv=[next(j for j in range(self.q) if self.mul[i][j]==self.e and self.mul[j][i]==self.e) for i in range(self.q)]
        assert all(self.mul[self.mul[a][b]][c]==self.mul[a][self.mul[b][c]] for a,b,c in itertools.product(range(self.q),repeat=3))

def groups():
    ans=[]
    for q in (2,3): ans.append(Group(f'C{q}',list(range(q)),lambda a,b,q=q:(a+b)%q,0))
    ps=list(itertools.permutations(range(3)))
    ans.append(Group('S3',ps,lambda a,b:tuple(a[b[i]] for i in range(3)),(0,1,2)))
    ans.append(Group('D8',list(itertools.product(range(4),range(2))),lambda a,b:((a[0]+(-1 if a[1] else 1)*b[0])%4,(a[1]+b[1])%2),(0,0)))
    return ans

def gmultiply(a,b,g):
    n,k,m=len(a),len(b),len(b[0]); q=g.q
    out=[[[0]*q for _ in range(m)] for _ in range(n)]
    for i in range(n):
        for h in range(k):
            for j in range(m):
                for x,v in enumerate(a[i][h]):
                    if v:
                        for y,w in enumerate(b[h][j]):
                            if w: out[i][j][g.mul[x][y]] += v*w
    return out

def endpoint(p,g):
    n=sum(p); j=jordan(p); q=g.q
    return [[[q**3*n + q*((q if h==g.e else 0)-1)*j[i][k] for h in range(q)] for k in range(n)] for i in range(n)]

def positive_factor(p,g):
    q=g.q
    return [[[q+((q if h==g.e else 0)-1)*v for h in range(q)] for v in row] for row in p]

def uniform(a):
    return all(len(set(x))==1 for row in a for x in row)

class Step:
    """One-vertex labelled exchanges U V = V U = q*u_H.
    Independent within-label permutations preserve every actual edge identity.
    """
    def __init__(self,g,rng):
        self.g=g; q=g.q
        self.ul=[rng.randrange(q) for _ in range(q)]
        self.vl=list(range(q))
        self.tf,self.ti=self.bijection(self.ul,self.vl,rng)
        self.ef,self.ei=self.bijection(self.vl,self.ul,rng)
    def bijection(self,left,right,rng):
        fs=[[] for _ in range(self.g.q)]
        for i,x in enumerate(left):
            for j,y in enumerate(right): fs[self.g.mul[x][y]].append((i,j))
        forward={}; backward={}
        for h, pairs in enumerate(fs):
            assert len(pairs)==self.g.q
            rng.shuffle(pairs)
            for c,pair in enumerate(pairs):
                edge=h*self.g.q+c
                forward[pair]=edge; backward[edge]=pair
        return forward,backward

def phi_r(steps,a,r):
    out=[]
    for st,uprime in zip(steps,r):
        u,v=st.ti[a]; out.append(u); a=st.ef[v,uprime]
    return tuple(out),a

def phi_s(steps,b,s):
    out=[]
    for st,vprime in zip(reversed(steps),s):
        v,u=st.ei[b]; out.append(v); b=st.tf[u,vprime]
    return tuple(out),b

def peel_a(steps,word):
    r=[]; vs=[]; word=list(word)
    for st in steps:
        factors=[st.ti[a] for a in word]
        r.append(factors[0][0]); vs.append(factors[-1][1])
        word=[st.ef[factors[i][1],factors[i+1][0]] for i in range(len(factors)-1)]
    assert not word
    return tuple(r),tuple(reversed(vs))

def fill_a(steps,r,s):
    word=[]; L=len(steps)
    for j in reversed(range(L)):
        st=steps[j]; factors=[st.ei[a] for a in word]
        us=[r[j]]+[u for v,u in factors]
        vs=[v for v,u in factors]+[s[L-1-j]]
        word=[st.tf[u,v] for u,v in zip(us,vs)]
    return tuple(word)

def peel_b(steps,word):
    s=[]; us=[]; word=list(word)
    for st in reversed(steps):
        factors=[st.ei[a] for a in word]
        s.append(factors[0][0]); us.append(factors[-1][1])
        word=[st.tf[factors[i][1],factors[i+1][0]] for i in range(len(factors)-1)]
    assert not word
    return tuple(s),tuple(reversed(us))

def fill_b(steps,s,r):
    word=[]; L=len(steps)
    for j,st in enumerate(steps):
        factors=[st.ti[a] for a in word]
        vs=[s[L-1-j]]+[v for u,v in factors]
        us=[u for u,v in factors]+[r[j]]
        word=[st.ef[v,u] for v,u in zip(vs,us)]
    return tuple(word)

def slide(steps,word,boundary,kind):
    out=list(word); f=phi_r if kind=='r' else phi_s
    for i in reversed(range(len(word))): boundary,out[i]=f(steps,word[i],boundary)
    return boundary,tuple(out)

def forward(steps,word,coords,g):
    word=list(word); coords=list(coords)
    for st in steps:
        fac=[st.ti[a] for a in word]
        coords=[g.mul[h][st.ul[u]] for h,(u,v) in zip(coords,fac)][:-1]
        word=[st.ef[fac[i][1],fac[i+1][0]] for i in range(len(fac)-1)]
        assert all(coords[i+1]==g.mul[coords[i]][word[i]//g.q] for i in range(len(word)-1))
    return tuple(word),tuple(coords)

def backward(steps,word,coords,g):
    word=list(word); coords=list(coords)
    for st in reversed(steps):
        fac=[st.ei[a] for a in word]
        coords=[g.mul[coords[i]][g.inv[st.ul[fac[i-1][1]]]] for i in range(1,len(word))]
        word=[st.tf[fac[i-1][1],fac[i][0]] for i in range(1,len(fac))]
        assert all(coords[i+1]==g.mul[coords[i]][word[i]//g.q] for i in range(len(word)-1))
    return tuple(word),tuple(coords)

def path_coords(word,g,h):
    out=[h]
    for a in word[:-1]: out.append(g.mul[out[-1]][a//g.q])
    return tuple(out)

def run(max_n=12):
    report={'seed':SEED,'arithmetic':'exact integers; no floating point',
            'scope':'finite checks only; not universal proof, Lean validation, independent review, or a remote commit'}
    pairs=edges=bfs_checks=geodesic_steps=0
    for n in range(1,max_n+1):
        ps=list(partitions(n)); adjacency={p:[] for p in ps}
        for p in ps:
            for q in ps:
                d=distance(p,q); path=geodesic(p,q)
                pairs+=1; geodesic_steps+=len(path)-1
                if d==1:
                    adjacent_factors(p,q); edges+=1; adjacency[p].append(q)
                if p[0]==q[0]: assert all(x[0]==p[0] for x in path)
        for p in ps:
            seen={p:0}; queue=deque([p])
            while queue:
                q=queue.popleft()
                for nxt in adjacency[q]:
                    if nxt not in seen: seen[nxt]=seen[q]+1; queue.append(nxt)
            assert len(seen)==len(ps)
            for q in ps:
                assert seen[q]==distance(p,q); bfs_checks+=1
    report['partitions']={'max_n':max_n,'ordered_pairs':pairs,'geodesic_steps':geodesic_steps,
                          'ordered_adjacent_factorizations':edges,'independent_bfs_pair_checks':bfs_checks}
    algebra_pairs=depths=0
    gs=groups()
    for g in gs:
        for n in range(1,6):
            ps=list(partitions(n))
            for p in ps:
                a=endpoint(p,g)
                assert all(min(entry)>0 and sum(entry)==g.q**4*n for row in a for entry in row)
                power=a
                for j in range(1,p[0]+1):
                    assert uniform(power)==(j>=p[0]); depths+=1
                    if j<p[0]: power=gmultiply(power,a,g)
                for q in ps:
                    if distance(p,q)!=1: continue
                    u,v=adjacent_factors(p,q)
                    u,v=positive_factor(u,g),positive_factor(v,g)
                    assert all(min(e)>0 for mat in (u,v) for row in mat for e in row)
                    assert gmultiply(u,v,g)==a
                    assert gmultiply(v,u,g)==endpoint(q,g)
                    algebra_pairs+=1
    report['group_algebra']={'groups':[g.name for g in gs], 'max_n':5,
                             'positive_ordered_factor_pairs':algebra_pairs,'uniformization_power_checks':depths}
    rng=random.Random(SEED); compatible=recover=code_recover=equivariance=0
    for g in gs:
        for L in range(1,5):
            for _ in range(4):
                steps=[Step(g,rng) for _ in range(L)]
                for _ in range(32):
                    word=tuple(rng.randrange(g.q*g.q) for _ in range(L))
                    r=tuple(rng.randrange(g.q) for _ in range(L))
                    s=tuple(rng.randrange(g.q) for _ in range(L))
                    ro,sm=peel_a(steps,word)
                    so,rm=peel_b(steps,word)
                    assert fill_a(steps,ro,sm)==word and peel_a(steps,fill_a(steps,r,s))==(r,s)
                    assert fill_b(steps,so,rm)==word and peel_b(steps,fill_b(steps,s,r))==(s,r)
                    recover+=4
                    assert slide(steps,word,r,'r')==(ro,fill_b(steps,sm,r))
                    assert slide(steps,word,s,'s')==(so,fill_a(steps,rm,s))
                    compatible+=2
                    longword=tuple(rng.randrange(g.q*g.q) for _ in range(2*L+1))
                    coords=path_coords(longword,g,rng.randrange(g.q))
                    fw,fc=forward(steps,longword,coords,g)
                    bw,bc=backward(steps,fw,fc,g)
                    assert bw==(longword[L],) and bc==(coords[L],)
                    bw,bc=backward(steps,longword,coords,g)
                    fw,fc=forward(steps,bw,bc,g)
                    assert fw==(longword[L],) and fc==(coords[L],)
                    code_recover+=2
                    h=rng.randrange(g.q); hc=tuple(g.mul[h][c] for c in coords)
                    aw,ac=forward(steps,longword,coords,g)
                    hw,hout=forward(steps,longword,hc,g)
                    assert hw==aw and hout==tuple(g.mul[h][c] for c in ac)
                    equivariance+=1
    report['labelled_certificates']={'groups':[g.name for g in gs],'lags':[1,2,3,4],
        'chains_per_group_lag':4,'samples_per_chain':32,'input_sampling':'seeded; not exhaustive',
        'compatibility_equations':compatible,'triangle_inverse_identities':recover,
        'window_code_recovery_checks':code_recover,'left_equivariance_checks':equivariance}
    report['example']={'lambda':[4,4],'mu':[4,1,1,1,1], 'distance':3,
                        'geodesic':[list(p) for p in geodesic((4,4),(4,1,1,1,1))],
                        'equal_tau':4,'rank_profile_lambda':[sum(max(x-j,0) for x in (4,4)) for j in range(5)],
                        'rank_profile_mu':[sum(max(x-j,0) for x in (4,1,1,1,1)) for j in range(5)]}
    report['sentinel']='ALL_PARTITION_AND_PATH_CLOSURE_CHECKS_PASSED'
    return report

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n',type=int,default=12)
    parser.add_argument('--output',type=Path,default=Path('verification.json'))
    args=parser.parse_args()
    if not 1<=args.max_n<=16: parser.error('--max-n must be between 1 and 16')
    result=run(args.max_n)
    result['script_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    args.output.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,ensure_ascii=False,indent=2))
