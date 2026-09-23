import importlib.util, os, itertools, sys
p=os.path.expanduser("~/omega-op/tuza-gen.py")
spec=importlib.util.spec_from_file_location("tg",p); tg=importlib.util.module_from_spec(spec); spec.loader.exec_module(tg)

def tris(n,adj):
    return [(a,b,c) for a in range(n) for b in range(a+1,n) for c in range(b+1,n)
            if adj[a]>>b&1 and adj[a]>>c&1 and adj[b]>>c&1]

def maxmatch(n,adj):
    E=[(a,b) for a in range(n) for b in range(a+1,n) if adj[a]>>b&1]
    best=0
    def go(i,used,c):
        nonlocal best
        if c+(len(E)-i)>best:
            if i==len(E): best=max(best,c); return
            a,b=E[i]
            if not(used>>a&1) and not(used>>b&1): go(i+1,used|1<<a|1<<b,c+1)
            go(i+1,used,c)
        else:
            best=max(best,c)
    go(0,0,0); return best

def maxind(n,adj):
    best=0
    for m in range(1<<n):
        ok=True
        for a in range(n):
            if (m>>a&1) and (adj[a]&m): ok=False; break
        if ok:
            k=bin(m).count("1")
            if k>best: best=k
    return best

def conn(n,adj):
    seen=1; st=[0]
    while st:
        v=st.pop(); nb=adj[v]&~seen
        while nb:
            b=nb&-nb; i=b.bit_length()-1; seen|=b; st.append(i); nb^=b
    return seen==(1<<n)-1

def reducible(n,adj):
    """Is there a triangle t and one edge e of t so that t meets every triangle of G-e in <=1 vertex?"""
    T=tris(n,adj)
    for t in T:
        for (x,y) in itertools.combinations(t,2):
            a2=list(adj); a2[x]&=~(1<<y); a2[y]&=~(1<<x)
            ok=True
            for s in tris(n,a2):
                if len(set(t)&set(s))>1: ok=False; break
            if ok: return True
    return False

N=8
def level_at(N):
    level={tg.canon(1,(0,)):(0,)}
    for n in range(2,N+1):
        nxt={}
        for g in level.values():
            for nbhd in range(1<<(n-1)):
                adj=list(g)+[nbhd]
                for u in range(n-1):
                    if nbhd>>u&1: adj[u]|=1<<(n-1)
                adj=tuple(adj)
                c=tg.canon(n,adj)
                if c not in nxt: nxt[c]=adj
        level=nxt
    return level

tot=out=red=0
for adj in level_at(N).values():
    if not conn(N,adj): continue
    tot+=1
    if maxmatch(N,adj)==N-maxind(N,adj): continue
    out+=1
    if reducible(N,adj): red+=1
print(f"connected={tot} outside_KE={out} reducible_by_one_edge={red} rate={red/out:.4f}")
