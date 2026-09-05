#!/usr/bin/env python3
"""Exact induced-graph audit, reusing the previously submitted interval kernel.

Eight certified roots generate 60 rays under S3 and the block antiunitary.
All 1770 pairs are checked. This is NOT a global root coverage certificate.
Only integer and fractions.Fraction arithmetic enters acceptance.
"""
from __future__ import annotations
import argparse, itertools, json
from pathlib import Path
from fractions import Fraction as F
import check_strict_x_counterexample as base
I,C,E=base.I,base.C,base.E
if not __debug__:
    raise RuntimeError('Assertions must be enabled')

def outer_round(x:I,bits:int=100)->I:
    d=1<<bits
    return I(F(x.lo.numerator*d//x.lo.denominator,d),
             F(-((-x.hi.numerator*d)//x.hi.denominator),d))

def cr(z:C)->C:return C(outer_round(z.re),outer_round(z.im))

def H_interval():
    H=base.hadamard(C.point(F(-3,5),F(4,5)),C(I.point(F(-2,5)),base.sqrtI(21)/5))
    return [H[i] for i in [2,0,1,4,5,3]]

def validate_root(spec,H):
    q=spec['chart_quarter_turns']; center=[F(v) for v in spec['center']];r=F(spec['radius'])
    assert len(q)==6 and q[0]==0 and all(type(v)is int and 0<=v<4 for v in q)
    assert len(center)==5 and r>0
    M=[[F(v) for v in row] for row in spec['preconditioner']]
    assert len(M)==5 and all(len(row)==5 for row in M) and base.determinant(M)!=0
    X=[I(t-r,t+r) for t in center]
    f0,_,_=base.equations_and_jacobian([I.point(t) for t in center],q,H)
    _,J,_=base.equations_and_jacobian(X,q,H)
    err=[[I.point(int(i==j))-sum((M[i][k]*J[k][j] for k in range(5)),I.point(0)) for j in range(5)] for i in range(5)]
    contraction=max(sum(v.abs_upper() for v in row) for row in err)
    assert contraction<F(1,1000)
    delta=[-sum((M[i][k]*f0[k] for k in range(5)),I.point(0))+
           sum((err[i][j]*I(-r,r) for j in range(5)),I.point(0)) for i in range(5)]
    assert all(v.abs_upper()<r/1000 for v in delta), ('displacement/r', float(max(v.abs_upper() for v in delta)/r), 'contraction',float(contraction))
    refined=[outer_round(t+v) for t,v in zip(center,delta)]
    assert all(X[j].lo<refined[j].lo<=refined[j].hi<X[j].hi for j in range(5))
    u=[cr(z) for z in base.phase_map(refined,q)]
    return {'u':u,'box':X,'chart':q,'contraction':contraction}

def transform(u,p,anti):
    z=[-x.conj() for x in u[3:]]+[x.conj() for x in u[:3]] if anti else u
    return [z[j] for j in list(p)+[i+3 for i in p]]

def fixed_by_shift(root):
    u=root['u'];w=transform(u,(1,2,0),False)
    if w[0].normsq().lo<=0:return False
    w=[cr(z/w[0]) for z in w]
    for j in range(1,6):
        z=w[j]*base.UNITS[(-root['chart'][j])%4]
        if (z+1).normsq().lo<=0:return False
        t=cr(C.point(0,-1)*(z-1)/(z+1))
        box=root['box'][j-1]
        if not(box.lo<t.re.lo and t.re.hi<box.hi):return False
    return True

def permutation_matrix(p):
    gp=list(p)+[j+3 for j in p]
    return [[F(int(j==gp[i])) for j in range(6)] for i in range(6)]

def connected_components(adj):
    remaining=set(range(len(adj)));out=[]
    while remaining:
        seed=min(remaining);seen={seed};todo=[seed]
        while todo:
            i=todo.pop()
            for j in adj[i]:
                if j not in seen:seen.add(j);todo.append(j)
        remaining-=seen;out.append(sorted(seen))
    return out

def bipartition(vertices,adj):
    color={}
    for seed in vertices:
        if seed in color:continue
        color[seed]=0;todo=[seed]
        while todo:
            i=todo.pop()
            for j in adj[i]:
                if j not in color:color[j]=1-color[i];todo.append(j)
                elif color[j]==color[i]:return None
    return [[i for i in vertices if color[i]==k] for k in (0,1)]

def check(path):
    data=json.loads(Path(path).read_text())
    assert data['schema']=='real-x-60-induced-graph-v1'
    assert data['parameters']=={'b':'(-3+4*i)/5','e':'(-2+i*sqrt(21))/5'}
    symbolic=base.symbolic_audit()
    ps=list(itertools.permutations(range(3)))
    assert data['group_permutations']==[list(p) for p in ps]
    H=H_interval();roots=[validate_root(spec,H) for spec in data['roots']]
    assert len(roots)==8
    eig=[fixed_by_shift(z) for z in roots]
    assert sum(eig)==2
    words=data['vertices']; assert len(words)==60
    G=[permutation_matrix(p) for p in ps]
    R=permutation_matrix((1,2,0));R2=base.mm(R,R)
    J0=[[F((-1 if i<3 else 1)*int(j==(i+3)%6)) for j in range(6)] for i in range(6)]
    # Normality of the three-cycle subgroup; Theta0 commutes with the real shift.
    assert base.mm(R,J0)==base.mm(J0,R)
    for M in G:assert base.mm(R,M) in [base.mm(M,R),base.mm(M,R2)]
    vecs=[]; is_eig=[]; eigenvalue=[]
    for w in words:
        k,p,a=w['root'],w['permutation'],w['antiunitary']
        assert type(k)is int and 0<=k<8 and type(p)is int and 0<=p<6 and type(a)is bool
        v=[cr(z) for z in transform(roots[k]['u'],ps[p],a)]
        vecs.append(v);is_eig.append(eig[k])
        eigenvalue.append(cr(v[1]/v[0]))
    adj=[set() for _ in words];edges=[];min_nonedge=F(1);max_distinct=F(0)
    n_skew=n_eigen=0
    for i,j in itertools.combinations(range(60),2):
        x,y=words[i],words[j]
        exact=False
        if x['root']==y['root'] and x['antiunitary']!=y['antiunitary']:
            K=base.mm(base.mm(base.mt(G[x['permutation']]),J0),G[y['permutation']])
            exact=base.mt(K)==[[-v for v in row] for row in K]
            if exact:n_skew+=1
        if not exact and is_eig[i] and is_eig[j]:
            if (eigenvalue[i]-eigenvalue[j]).normsq().lo>0:
                exact=True;n_eigen+=1
        g=sum((a.conj()*b for a,b in zip(vecs[i],vecs[j])),C.point())/6
        norm=g.normsq()
        assert norm.hi<1 # distinct rays, including across separate root orbits
        max_distinct=max(max_distinct,norm.hi)
        if exact:
            assert norm.lo<=F(0)<=norm.hi # interval consistency, NOT the proof of zero
            adj[i].add(j);adj[j].add(i);edges.append([i,j])
        else:
            assert norm.lo>0,('Unresolved pair',i,j)
            min_nonedge=min(min_nonedge,norm.lo)
    comps=connected_components(adj);summary=[];canonical=None
    for comp in comps:
        ne=sum(len(adj[i]) for i in comp)//2
        bp=bipartition(comp,adj)
        if bp is None:
            assert len(comp)==6 and ne==15 and all(is_eig[i] for i in comp)
            assert canonical is None;canonical=comp
        summary.append({'vertices':comp,'edge_count':ne,'bipartition':bp})
    assert canonical is not None
    signature=sorted((len(c['vertices']),c['edge_count']) for c in summary)
    assert signature==[(6,9),(6,9),(6,9),(6,15),(12,24),(12,24),(12,24)]
    assert len(edges)==114
    assert min_nonedge>F(1,100000000)
    return {'status':'PASS','arithmetic':'fractions.Fraction; outward dyadic enclosure only',
        'root_existence':'eight strict Krawczyk/contraction inclusions; all other rays are exact symmetry images',
        'unique_root_boxes':8,'distinct_rays':60,'unordered_pairs_checked':1770,
        'exact_edges':len(edges),'skew_symmetry_edges':n_skew,'distinct_eigenvalue_edges':n_eigen,
        'nonedges':1770-len(edges),'nonedge_normsq_strict_lower_bound':'1/100000000',
        'component_signature':signature,'components':summary,'canonical_six_clique':canonical,
        'unique_six_clique_in_induced_graph':True,'canonical_affinity_exact':'2',
        'noncanonical_induced_subgraph_bipartite':True,'exact_edge_list':edges,
        'scope':'Complete induced graph on the certified collection. No assertion that the collection exhausts all common-unbiased rays.',
        'lean_status':'The interval/graph checker is not a Lean kernel proof.',
        'symbolic_seed_checked':symbolic['both_Hadamard_Grams']}

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('certificate',type=Path);ap.add_argument('--report',type=Path)
    args=ap.parse_args(); result=check(args.certificate)
    text=json.dumps(result,indent=2)+'\n'
    if args.report:args.report.write_text(text)
    print(text)
