#!/usr/bin/env python3
"""Exact finite regression checks for SFT theory chapters 29--32.

Python 3, NumPy, and SymPy. No network, random acceptance, or floating point.
These examples test constructions; the universal statements require the paper proofs.
"""
from __future__ import annotations
import hashlib
import itertools as it
import json
from pathlib import Path
from typing import Callable
import numpy as np
import sympy as sp

HERE = Path(__file__).resolve().parent

class Group:
    def __init__(self, name: str, elements: list, product: Callable):
        self.name, self.elements = name, elements
        self.s = len(elements)
        index = {g: i for i, g in enumerate(elements)}
        self.mul = [[index[product(a,b)] for b in elements] for a in elements]
        assert self.mul[0] == list(range(self.s))
        assert [r[0] for r in self.mul] == list(range(self.s))
        self.inv = [next(j for j in range(self.s) if self.mul[i][j] == 0
                         and self.mul[j][i] == 0) for i in range(self.s)]
        for a,b,c in it.product(range(self.s), repeat=3):
            assert self.mul[self.mul[a][b]][c] == self.mul[a][self.mul[b][c]]

    def matmul(self, a: np.ndarray, b: np.ndarray) -> np.ndarray:
        assert a.shape[2] == b.shape[1] and a.shape[0] == b.shape[0] == self.s
        c = np.zeros((self.s, a.shape[1], b.shape[2]), dtype=object)
        for g in range(self.s):
            for h in range(self.s):
                c[self.mul[g][h]] += a[g] @ b[h]
        return c

    def identity(self, n: int) -> np.ndarray:
        a = np.zeros((self.s,n,n), dtype=object)
        a[0] = np.eye(n, dtype=object)
        return a

    def power(self, a: np.ndarray, j: int) -> np.ndarray:
        out = self.identity(a.shape[1])
        for _ in range(j):
            out = self.matmul(out,a)
        return out

    def augmentation_operator(self, a: np.ndarray) -> sp.Matrix:
        # Basis g-1 (g != 1) for each copy of the augmentation ideal.
        n = a.shape[1]
        out = np.zeros((n*(self.s-1),n*(self.s-1)), dtype=object)
        for i,j,h in it.product(range(n),range(n),range(1,self.s)):
            coeff = [0]*self.s
            for g in range(self.s):
                coeff[self.mul[g][h]] += a[g,i,j]
                coeff[g] -= a[g,i,j]
            assert sum(coeff) == 0
            for k in range(1,self.s):
                out[i*(self.s-1)+k-1,j*(self.s-1)+h-1] = coeff[k]
        return sp.Matrix(out.tolist())


def groups() -> list[Group]:
    ans = [Group(f'C{s}',list(range(s)),lambda a,b,s=s:(a+b)%s) for s in (2,3)]
    # (a,b) = r^a s^b; s r = r^{-1} s. D8 has order eight.
    ans.append(Group('D8',list(it.product(range(4),range(2))),
                     lambda x,y:((x[0]+(-1)**x[1]*y[0])%4,(x[1]+y[1])%2)))
    perm = list(it.permutations(range(3)))
    ans.append(Group('S3',perm,lambda p,q:tuple(p[q[i]] for i in range(3))))
    return ans


def prefix(a:int,d:int) -> np.ndarray:
    t = np.zeros((d,d),dtype=object)
    for i in range(a-1): t[i,i+1]=1
    return t


def projection(a:int,d:int) -> np.ndarray:
    return np.diag([1]*(a-1)+[0]*(d-a+1)).astype(object)


def block_diag(blocks:list[np.ndarray]) -> np.ndarray:
    sizes=[b.shape[0] for b in blocks]
    z=np.zeros((sum(sizes),sum(sizes)),dtype=object)
    start=0
    for b in blocks:
        end=start+b.shape[0];z[start:end,start:end]=b;start=end
    return z


def family(g:Group,t:tuple[int,...],d:int) -> np.ndarray:
    n=len(t)*d;s=g.s
    tmat=block_diag([prefix(a,d) for a in t])
    a=np.full((s,n,n),s**3*n,dtype=object)
    a[0]+=s*(s-1)*tmat
    for h in range(1,s):a[h]-=s*tmat
    return a


def factors(g:Group,t:tuple[int,...],v:tuple[int,...],d:int):
    xx=[];yy=[]
    for a,b in zip(t,v):
        assert abs(a-b)<=1
        if b==a-1: x,y=projection(a,d),prefix(a,d)
        elif b==a+1:x,y=prefix(a+1,d),projection(a+1,d)
        else:x,y=np.eye(d,dtype=object),prefix(a,d)
        xx.append(x);yy.append(y)
    ans=[]
    for mat in (block_diag(xx),block_diag(yy)):
        n=mat.shape[0];out=np.full((g.s,n,n),g.s,dtype=object)
        out[0]+=(g.s-1)*mat
        for h in range(1,g.s):out[h]-=mat
        assert min(out.flat)>0
        ans.append(out)
    return ans


def profile_from_powers(m:sp.Matrix) -> list[int]:
    p=sp.eye(m.rows);ranks=[m.rows]
    for j in range(1,m.rows+1):
        p=p*m;ranks.append(p.rank())
        if p.is_zero_matrix: break
    else:raise AssertionError('Expected nilpotent operator')
    widths=[ranks[j-1]-ranks[j] for j in range(1,len(ranks))]
    return [sum(w>i for w in widths) for i in range(widths[0])]


def expected_profile(t,d,s):
    base=list(t)+[1]*(len(t)*d-sum(t))
    return [a for a in base for _ in range(s-1)]


def delta(a,b):
    return max([abs(x-y) for x,y in it.zip_longest(a,b,fillvalue=0)]+[0])


def verify_families(gs):
    counts={'families':0,'matrices':0,'ordered_pairs':0,'elementary_steps':0,
            'rank_profiles':0,'mixed_direction_steps':0,'se_equalities':0}
    examples=[]
    for g in gs:
        # D=4 for small groups and D=3 for noncommutative groups keeps exact tests small.
        d=4 if g.s<=3 else 3;r=2;n=r*d
        tuples=list(reversed(list(it.combinations_with_replacement(range(1,d+1),r))))
        tuples=[tuple(reversed(t)) for t in tuples]
        mats={t:family(g,t,d) for t in tuples}
        counts['families']+=1
        for t,a in mats.items():
            counts['matrices']+=1
            assert min(a.flat)>0
            assert np.array_equal(sum(a),np.full((n,n),g.s**4*n,dtype=object))
            got=profile_from_powers(g.augmentation_operator(a))
            assert got==expected_profile(t,d,g.s),(g.name,t,got)
            counts['rank_profiles']+=1
        for t,v in it.product(tuples,repeat=2):
            counts['ordered_pairs']+=1
            ell=max(abs(a-b) for a,b in zip(t,v))
            assert delta(expected_profile(t,d,g.s),expected_profile(v,d,g.s))==ell
            path=[tuple(min(max(b,a-k),a+k) for a,b in zip(t,v)) for k in range(ell+1)]
            assert path[0]==t and path[-1]==v
            rr=g.identity(n);ss=g.identity(n)
            for a,b in zip(path,path[1:]):
                assert tuple(sorted(a,reverse=True))==a
                assert all(1<=x<=d for x in a)
                u,w=factors(g,a,b,d)
                assert np.array_equal(g.matmul(u,w),mats[a])
                assert np.array_equal(g.matmul(w,u),mats[b])
                rr=g.matmul(rr,u);ss=g.matmul(w,ss)
                counts['elementary_steps']+=1
                if any(x<y for x,y in zip(a,b)) and any(x>y for x,y in zip(a,b)):
                    counts['mixed_direction_steps']+=1
            if ell:
                at,av=mats[t],mats[v]
                for left,right in ((g.matmul(at,rr),g.matmul(rr,av)),
                                   (g.matmul(av,ss),g.matmul(ss,at)),
                                   (g.matmul(rr,ss),g.power(at,ell)),
                                   (g.matmul(ss,rr),g.power(av,ell))):
                    assert np.array_equal(left,right)
                    counts['se_equalities']+=1
        examples.append({'group':g.name,'dimension':n,'t':[d,d],'v':[d,1],
                         'same_depth':d,'exact_distance':d-1,
                         't_profile':expected_profile((d,d),d,g.s),
                         'v_profile':expected_profile((d,1),d,g.s)})
    return counts,examples


# Generic scalar edge products with all duplicate identities retained.
class Exchange:
    def __init__(self,g:Group,u:list[int],v:list[int]):
        self.g,self.u,self.v=g,u,v
        def enumerate_product(first,second):
            pairs=sorted(it.product(range(len(first)),range(len(second))),
                         key=lambda p:(g.mul[first[p[0]]][second[p[1]]],p))
            labels=[g.mul[first[i]][second[j]] for i,j in pairs]
            return pairs,{p:k for k,p in enumerate(pairs)},labels
        self.uv,self.uv_inv,self.a=enumerate_product(u,v)
        self.vu,self.vu_inv,self.b=enumerate_product(v,u)
    def forward(self,a0,a1):
        u0,v0=self.uv[a0];u1,_=self.uv[a1]
        return self.vu_inv[(v0,u1)],self.u[u0]
    def backward(self,b0,b1):
        _,u1=self.vu[b0];v1,_=self.vu[b1]
        return self.uv_inv[(u1,v1)],self.u[u1]


def verify_d8_overlap(g:Group):
    # q=(0,1), r=(1,0); U=u+(1-q)r, V=1+q.
    q=g.elements.index((0,1));r=g.elements.index((1,0))
    coeff=[1]*g.s;coeff[r]+=1;coeff[g.mul[q][r]]-=1
    u=[h for h,c in enumerate(coeff) for _ in range(c)]
    e=Exchange(g,u,[0,q])
    assert len(e.a)==len(e.b)==16
    assert [e.b.count(h) for h in range(g.s)]==[2]*g.s
    count=0
    for a0,a1,a2 in it.product(range(16),repeat=3):
        b0,alpha0=e.forward(a0,a1);b1,alpha1=e.forward(a1,a2)
        recovered,alpha=e.backward(b0,b1)
        assert recovered==a1 and alpha==alpha1
        assert g.mul[e.a[a0]][alpha1]==g.mul[alpha0][e.b[b0]]
        for h in range(g.s):
            h1=g.mul[h][e.a[a0]];k0=g.mul[h][alpha0];k1=g.mul[h1][alpha1]
            assert g.mul[k0][e.b[b0]]==k1
            assert g.mul[k1][g.inv[alpha1]]==h1
            for left in range(g.s):
                assert g.mul[g.mul[left][h]][alpha0]==g.mul[left][k0]
            count+=1
    reverse_count=0
    for b0,b1,b2 in it.product(range(16),repeat=3):
        a1,_=e.backward(b0,b1);a2,_=e.backward(b1,b2)
        assert e.forward(a1,a2)[0]==b1
        reverse_count+=1
    return {'forward_legal_three_edge_words':4096,'inverse_legal_three_edge_words':reverse_count,
            'group_coordinate_cases':count,'equivariance_cases':count*g.s}


def verify_grid():
    # Scalar examples: edges are tuples of binary half-edge identities.
    # Splitting is fixed by word lengths; this does not test varying vertex counts.
    # X_j is the cyclic rotation of L+1 distinct half-edge species, each with 2 edges.
    cases=0
    for L in (1,2,3):
        species=L+1
        # A_j edges are words over j,j+1,... cyclic species, each value 0/1.
        # U_j = first species; V_j = all remaining species.
        # A_j+1 = V_j U_j. Rotations have a concrete identity for each actual edge.
        def split_a(a):return a[:1],a[1:]
        def eta(v,u):return v+u
        def theta(u,v):return u+v
        def strip_top(top):
            left=[];right=[];row=top
            for _ in range(L):
                parts=[split_a(a) for a in row]
                left.append(parts[0][0]);right.append(parts[-1][1])
                row=[eta(parts[i][1],parts[i+1][0]) for i in range(len(parts)-1)]
            return tuple(left),tuple(reversed(right))
        def reverse_strip(bottom):
            left=[];right=[];row=bottom
            for _ in range(L):
                parts=[(a[:-1],a[-1:]) for a in row]
                left.append(parts[0][0]);right.append(parts[-1][1])
                row=[theta(parts[i][1],parts[i+1][0]) for i in range(len(parts)-1)]
            return tuple(left),tuple(reversed(right))
        # L=3 has 2^(L*(L+2))=32768 complete finite inputs.
        for bits in it.product((0,1),repeat=L*species+L):
            top=[tuple(bits[i*species:(i+1)*species]) for i in range(L)]
            rin=[(b,) for b in bits[L*species:]]
            row=top;left=[]
            for j in range(L):
                parts=[split_a(a) for a in row]
                uu=[p[0] for p in parts]+[rin[j]]
                left.append(uu[0]);row=[eta(parts[i][1],uu[i+1]) for i in range(L)]
            rout,smid=strip_top(top)
            got_s,got_r=reverse_strip(row)
            assert tuple(left)==rout and got_s==smid and got_r==tuple(rin)
            # Independent right-to-left column sweep.
            right=rin;bottom=[None]*L
            for i in reversed(range(L)):
                a=top[i];out=[]
                for j in range(L):
                    u,v=split_a(a);out.append(u);a=eta(v,right[j])
                right=out;bottom[i]=a
            assert right==left and bottom==row
            cases+=1
    return {'full_grid_inputs':cases,'chain_lengths':[1,2,3],
            'scope':'exhaustive binary half-edge scalar cases; not arbitrary matrices'}


def verify_involution_matrices(gs):
    checks=0;nonuniform=0
    for g in gs:
        qs=[q for q in range(1,g.s) if g.mul[q][q]==0]
        if not qs:continue
        q=qs[0]
        for n in (1,2,3):
            for seed in range(3):
                t=np.zeros((g.s,n,n),dtype=object)
                for h,i,j in it.product(range(g.s),range(n),range(n)):
                    t[h,i,j]=((h+1)*(i+2)+3*j+seed)%9-4
                v=g.identity(n)
                v[q]=np.eye(n,dtype=object)
                qm=g.identity(n)
                qm[q]=-np.eye(n,dtype=object)
                d=g.matmul(qm,t)
                k=np.max(np.abs(d),axis=0)+1
                u=np.array([k+d[h] for h in range(g.s)],dtype=object)
                a=g.matmul(u,v);b=g.matmul(v,u)
                assert min(u.flat)>0 and min(a.flat)>0 and min(b.flat)>0
                assert np.array_equal(b,np.array([2*k]*g.s,dtype=object))
                z=a-b
                assert not g.matmul(z,z).any()
                assert not g.matmul(b,z).any() and not g.matmul(z,b).any()
                assert np.array_equal(g.power(a,2),g.power(b,2))
                nonuniform+=int(bool(z.any()));checks+=1
    return {'integer_matrix_inputs':checks,'nonuniform_endpoints':nonuniform,
            'matrix_sizes':[1,2,3]}


def main():
    gs=groups()
    family_counts,examples=verify_families(gs)
    report={'method':'exact integer arithmetic and exact rational ranks; no floats',
            'family_checks':family_counts,'same_depth_examples':examples,
            'overlap_checks':verify_d8_overlap(next(g for g in gs if g.name=='D8')),
            'grid_checks':verify_grid(),
            'involution_matrix_checks':verify_involution_matrices(gs),
            'scope':'finite regression tests, not a universal proof or Lean certificate',
            'sentinel':'ALL_SFT_PROFILE_AND_PATH_CLOSURE_CHECKS_PASSED'}
    report['script_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    (HERE/'verification.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps(report,ensure_ascii=False,indent=2))

if __name__=='__main__':main()
