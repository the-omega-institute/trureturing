#!/usr/bin/env python3
"""Exact finite regression checks for the parity/port-transport paper proofs.
No finite run is a proof of the unrestricted rectangular-grid conjecture.
"""
from __future__ import annotations
import argparse, collections, hashlib, itertools, json, random
from pathlib import Path

def bits(x):
    while x:
        b=x&-x; yield b.bit_length()-1; x^=b

def pairing_options(ports):
    if not ports: return [()]
    a=ports[0]; out=[]
    for j in range(1,len(ports)):
        b=ports[j]
        for rest in pairing_options(ports[1:j]+ports[j+1:]):out.append(((a,b),)+rest)
    return out

def routing(n, edges, r, xy, rng):
    deg=[0]*n; local=[[] for _ in range(n)]; links={}; terminals={}; positions={}
    def add(a,b,weight):
        links.setdefault(a,[]).append((b,weight));links.setdefault(b,[]).append((a,weight))
    for e,(v,w) in enumerate(edges):
        p=(0,e,0);q=(0,e,1);local[v].append(p);local[w].append(q)
        deg[v]+=1;deg[w]+=1;positions[p]=v;positions[q]=w;add(p,q,1)
    leaves=[];holes=0
    for v in range(n):
        if r[v]==0:
            assert deg[v]<=1
            if deg[v]:terminals[local[v][0]]='L';leaves.append(v)
        else:
            assert deg[v]<=2*r[v]
            for j in range(2*r[v]-deg[v]):
                p=(1,v,j);local[v].append(p);terminals[p]='H';positions[p]=v;holes+=1
            opts=pairing_options(local[v])
            for a,b in opts[rng.randrange(len(opts))]:add(a,b,0)
    for p in positions:assert len(links[p])==(1 if p in terminals else 2)
    seen=set();a=b=c=o=used=0
    paths=[]
    for start in terminals:
        if start in seen:continue
        prev=None;cur=start;length=0;seen.add(cur)
        while True:
            nxt=[(p,w) for p,w in links[cur] if p!=prev]
            if not nxt:break
            assert len(nxt)==1
            dest,weight=nxt[0];length+=weight;prev,cur=cur,dest
            assert cur not in seen;seen.add(cur)
            if cur in terminals:break
        assert cur!=start and cur in terminals
        kind=''.join(sorted((terminals[start],terminals[cur])))
        sv,tv=positions[start],positions[cur]
        if xy is not None:
            sx,sy=xy[sv];tx,ty=xy[tv]
            assert length%2==((sx+sy-tx-ty)%2)
        if kind=='LL':a+=1;o+=length%2
        elif kind=='HH':b+=1
        else:c+=1
        used+=length;paths.append((kind,length,sv,tv))
    for start in positions:
        if start in seen:continue
        todo=[start];count=0;seen.add(start)
        while todo:
            p=todo.pop()
            for q,w in links[p]:
                count+=w
                if q not in seen:seen.add(q);todo.append(q)
        assert count%2==0
        if xy is not None:assert (count//2)%2==0
        used+=count//2
    q=len(edges)-sum(r)
    assert used==len(edges) and q==a-b
    assert len(leaves)==2*a+c and holes==2*b+c
    assert 2*q==len(leaves)-holes
    return dict(a=a,b=b,c=c,o=o,leaves=leaves,holes=holes,q=q,paths=paths)

def distance_between_leaves(n,edges,leaves):
    adj=[[] for _ in range(n)]
    for v,w in edges:adj[v].append(w);adj[w].append(v)
    best=None;ls=set(leaves)
    for start in leaves:
        dist={start:0};todo=collections.deque([start])
        while todo:
            v=todo.popleft()
            for w in adj[v]:
                if w in dist:continue
                dist[w]=dist[v]+1;todo.append(w)
                if w in ls and (best is None or dist[w]<best):best=dist[w]
    return best

def check_transport(n,edges,r,xy,extra,rng):
    z=routing(n,edges,r,xy,rng);ell=len(z['leaves']);D=sum(r)+extra;q=z['q']
    assert extra>=ell
    assert all(not(v in z['leaves'] and w in z['leaves']) for v,w in edges)
    assert D>=3*q+4*z['b']+2*z['c']+z['o']
    d=distance_between_leaves(n,edges,z['leaves'])
    if d is None:assert q<=0
    else:assert d>=2 and D>=(d+1)*q
    return z,d

def grid(m,n):
    adj=[0]*(m*n);edges=[]
    for v in range(m*n):
        i,j=divmod(v,n)
        for w in (v+1 if j+1<n else -1,v+n if i+1<m else -1):
            if w>=0:adj[v]|=1<<w;adj[w]|=1<<v;edges.append((v,w))
    return adj,edges

def feasible_pairs(m,n):
    adj,_=grid(m,n)
    def ok(T,A):return all((adj[v]&A).bit_count()<=1 for v in bits(T))
    def go(left,T,A,M):
        if not left:yield T,A,M;return
        bit=left&-left;v=bit.bit_length()-1;rest=left^bit
        yield from go(rest,T,A,M)
        if ok(T|bit,A|bit):yield from go(rest,T|bit,A|bit,M)
        for w in bits(adj[v]&rest):
            wb=1<<w
            if ok(T,A|bit|wb):yield from go(rest^wb,T,A|bit|wb,M+((v,w),))
    yield from go((1<<(m*n))-1,0,0,())

def grid_core(m,n,T,M,rng):
    assert m%2==n%2==0
    adj,_=grid(m,n);A=T
    flat=[v for e in M for v in e]
    assert len(set(flat))==len(flat) and all(not(T>>v&1) for v in flat)
    for v,w in M:assert adj[v]>>w&1;A|=(1<<v)|(1<<w)
    assert all((adj[v]&A).bit_count()<=1 for v in bits(T))
    N=m*n//4;tile=lambda v:(v//n//2)*(n//2)+(v%n//2)
    t=[0]*N;h=[0]*N;s=[0]*N;E=[]
    for v in bits(T):t[tile(v)]+=1
    assert max(t)<=2
    for v,w in M:
        a,b=tile(v),tile(w)
        if a==b:h[a]+=1
        elif t[a]==t[b]==2:raise AssertionError('two saturated tiles')
        elif t[a]==2:s[b]+=1
        elif t[b]==2:s[a]+=1
        else:E.append((a,b))
    r=[2-t[i]-h[i]-s[i] for i in range(N)];assert min(r)>=0
    xy=[divmod(i,n//2) for i in range(N)]
    z,d=check_transport(N,E,r,xy,sum(h)+sum(s),rng)
    assert z['q']==T.bit_count()+len(M)-m*n//2
    return dict(r=r,edges=E,t=t,h=h,s=s,d=d,counts={k:z[k] for k in ('a','b','c','o','q','holes')},leaves=z['leaves'])

def rank_mod(A,p):
    A=[row[:] for row in A];rows=len(A);cols=len(A[0]) if rows else 0;r=0
    for j in range(cols):
        pivot=next((i for i in range(r,rows) if A[i][j]%p),None)
        if pivot is None:continue
        A[r],A[pivot]=A[pivot],A[r];inv=pow(A[r][j]%p,-1,p);A[r]=[(x*inv)%p for x in A[r]]
        for i in range(rows):
            if i!=r:
                k=A[i][j];A[i]=[(x-k*y)%p for x,y in zip(A[i],A[r])]
        r+=1
    return r

def arithmetic_checks():
    graphs=0
    for n in range(1,6):
        possible=list(itertools.combinations(range(n),2))
        for mask in range(1<<len(possible)):
            E=[e for j,e in enumerate(possible) if mask>>j&1];adj=[[] for _ in range(n)]
            for v,w in E:adj[v].append(w);adj[w].append(v)
            colors={};components=bipartite_components=0
            for v in range(n):
                if v in colors:continue
                components+=1;good=True;colors[v]=0;todo=[v]
                while todo:
                    a=todo.pop()
                    for b in adj[a]:
                        if b in colors:
                            if colors[b]==colors[a]:good=False
                        else:colors[b]=1-colors[a];todo.append(b)
                bipartite_components+=good
            A=[[int(v in e) for e in E] for v in range(n)]
            for p in (2,3,5,7):assert rank_mod(A,p)==n-(components if p==2 else bipartite_components)
            graphs+=1
    # Nonnegative right-hand side with only a signed integral solution on P4.
    x=(1,-1,1);y=(x[0],x[0]+x[1],x[1]+x[2],x[2]);assert y==(1,0,0,1)
    assert not any((a,a+b,b+c,c)==y for a,b,c in itertools.product(range(3),repeat=3))
    return graphs

def group_checks():
    P=[frozenset((frozenset((0,1)),frozenset((2,3)))),frozenset((frozenset((0,2)),frozenset((1,3)))),frozenset((frozenset((0,3)),frozenset((1,2))))]
    image=set();kernel=[]
    for perm in itertools.permutations(range(4)):
        action=tuple(P.index(frozenset(frozenset(perm[i] for i in pair) for pair in pairing)) for pairing in P)
        image.add(action)
        if action==(0,1,2):kernel.append(perm)
    assert len(image)==6 and len(kernel)==4
    assert set(kernel)=={(0,1,2,3),(1,0,3,2),(2,3,0,1),(3,2,1,0)}
    return dict(permutations=24,image_order=6,kernel_order=4)

def signature(word):
    x=y=z=0;H=V=0
    for a,b in word:z+=x*b;x+=a;y+=b;H+=abs(a);V+=abs(b)
    return x,y,z,H,V

def chronology_checks():
    steps=((1,0),(-1,0),(0,1),(0,-1));count=0
    for length in range(8):
        for word in itertools.product(steps,repeat=length):
            x,y,z,H,V=signature(word);xx,yy,zz,HH,VV=signature(tuple((-a,-b) for a,b in word[::-1]))
            assert (xx,yy,zz)==(-x,-y,x*y-z)
            assert H%2==x%2 and V%2==y%2 and (HH,VV)==(H,V)
            assert 2*zz-xx*yy==-(2*z-x*y)
            count+=1
    assert signature(((1,0),(0,1),(-1,0),(0,-1)))[:3]==(0,0,1)
    return count

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=Path('parity-transport-verification.json'));args=ap.parse_args()
    rng=random.Random(2026092704)
    report={'scope':'Finite exact regression checks; paper proofs carry universal claims. No Lean or full grid conjecture claim.','group':group_checks(),'incidence_graphs':arithmetic_checks(),'lattice_words':chronology_checks(),'grid_cases':[]}
    for m,n in ((2,2),(2,4),(2,6),(4,4)):
        count=0
        for T,A,M in feasible_pairs(m,n):grid_core(m,n,T,M,rng);count+=1
        report['grid_cases'].append(dict(m=m,n=n,pairs=count));print(m,n,count,flush=True)
    # Sharp abstract examples for every tested leaf-separation length.
    sharp=0
    for d in range(2,61):
        n=d+1;E=[(v,v+1) for v in range(d)];r=[0]+[1]*(d-1)+[0]
        z,sep=check_transport(n,E,r,[(v,0) for v in range(n)],2,rng)
        assert sep==d and z['q']==1 and z['a']==1 and z['b']==z['c']==0
        assert sum(r)+2==d+1;sharp+=1
    report['sharp_abstract_paths']=sharp
    # A real overloaded residual component, balanced by capacity outside it.
    T=sum(1<<v for v in (0,5,12,17,19,22));M=((1,2),(3,4),(7,13),(10,16),(8,9))
    witness=grid_core(4,6,T,M,rng)
    assert witness['r']==[0,1,0,0,2,0] and witness['edges']==[(0,1),(1,2)]
    assert witness['counts']==dict(a=1,b=2,c=0,o=0,q=-1,holes=4)
    report['overloaded_component_witness']=dict(m=4,n=6,T=list(bits(T)),M=M,core=witness)
    report['script_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest();report['result']='ALL_LISTED_CHECKS_PASSED'
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)
if __name__=='__main__':main()
