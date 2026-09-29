#!/usr/bin/env python3
"""Exact checks for the unchanged C2 endpoints in PR #8336, Proposition 22.4.
The universal one-step obstruction is proved in the accompanying paper appendix.
No Lean, external libraries, sampling, or remote writes are used here.
"""
from __future__ import annotations
import hashlib, itertools, json
from pathlib import Path
from verify_partition_closure import groups, gmultiply, peel_a, peel_b, fill_a, fill_b, slide


def edges(a):
    return tuple((i,j,h,c) for i,row in enumerate(a) for j,coeff in enumerate(row)
                 for h,k in enumerate(coeff) for c in range(k))


def paths(edge_sets):
    if not edge_sets:
        raise ValueError('This enumerator requires a positive path length.')
    words=[(a,) for a in edge_sets[0]]
    for alphabet in edge_sets[1:]:
        words=[w+(a,) for w in words for a in alphabet if w[-1][1]==a[0]]
    return words


class CountedStep:
    def __init__(self,u,v,g):
        self.u=edges(u); self.v=edges(v); self.g=g
        self.a=edges(gmultiply(u,v,g)); self.b=edges(gmultiply(v,u,g))
        self.tf,self.ti=self.factor(self.u,self.v)
        self.ef,self.ei=self.factor(self.v,self.u)
        assert set(self.ti)==set(self.a) and set(self.ei)==set(self.b)
    def factor(self,left,right):
        fibers={}
        for x,y in paths([left,right]):
            key=(x[0],y[1],self.g.mul[x[2]][y[2]])
            fibers.setdefault(key,[]).append((x,y))
        f={}; inv={}
        for key,pairs in sorted(fibers.items()):
            for count,pair in enumerate(sorted(pairs)):
                a=key+(count,); f[pair]=a; inv[a]=pair
        return f,inv


def coords(word,g,h):
    ans=[h]
    for a in word[:-1]: ans.append(g.mul[ans[-1]][a[2]])
    return tuple(ans)


def forward(steps,word,hs,g):
    word=list(word); hs=list(hs)
    for st in steps:
        fac=[st.ti[a] for a in word]
        hs=[g.mul[h][u[2]] for h,(u,v) in zip(hs,fac)][:-1]
        word=[st.ef[fac[i][1],fac[i+1][0]] for i in range(len(fac)-1)]
        assert all(word[i][1]==word[i+1][0] and hs[i+1]==g.mul[hs[i]][word[i][2]] for i in range(len(word)-1))
    return tuple(word),tuple(hs)


def backward(steps,word,hs,g):
    word=list(word); hs=list(hs)
    for st in reversed(steps):
        fac=[st.ei[a] for a in word]
        hs=[g.mul[hs[i]][g.inv[fac[i-1][1][2]]] for i in range(1,len(word))]
        word=[st.tf[fac[i-1][1],fac[i][0]] for i in range(1,len(fac))]
        assert all(word[i][1]==word[i+1][0] and hs[i+1]==g.mul[hs[i]][word[i][2]] for i in range(len(word)-1))
    return tuple(word),tuple(hs)


def run():
    g=groups()[0]; e=[1,0]; h=[0,1]; u=[1,1]; zero=[0,0]
    a=[[[2,2],[3,1]],[[2,2],[2,2]]]
    b=[[[2,2],[2,2]],[[2,2],[2,2]]]
    p=[[e,u,e],[u,u,zero]]
    pt=[[e,[0,2],e],[u,u,zero]]
    v=[[u,e],[zero,e],[u,e]]
    c=gmultiply(v,p,g)
    assert gmultiply(p,v,g)==a
    assert gmultiply(v,pt,g)==c
    assert gmultiply(pt,v,g)==b
    assert c==[[[2,2],[3,3],[1,1]],[[1,1],[1,1],[0,0]],[[2,2],[3,3],[1,1]]]
    assert gmultiply(a,a,g)==gmultiply(b,b,g)==gmultiply(a,b,g)==gmultiply(b,a,g)
    twice_e=[[[2,0],[0,0]],[[0,0],[1,1]]]
    twice_a=[[[2*k for k in coeff] for coeff in row] for row in a]
    twice_b=[[[2*k for k in coeff] for coeff in row] for row in b]
    assert gmultiply(twice_e,a,g)==twice_a
    assert gmultiply(a,twice_e,g)==twice_b
    steps=[CountedStep(p,v,g),CountedStep(v,pt,g)]
    assert steps[0].b==steps[1].a
    compat_a=compat_b=inv=0
    rpaths=paths([steps[0].u,steps[1].u]); spaths=paths([steps[1].v,steps[0].v])
    assert len(rpaths)==len(spaths)==16
    for word in paths([steps[0].a]*2):
        ro,sm=peel_a(steps,word)
        assert fill_a(steps,ro,sm)==word; inv+=1
        for ri in rpaths:
            if word[-1][1]!=ri[0][0]: continue
            assert slide(steps,word,ri,'r')==(ro,fill_b(steps,sm,ri)); compat_a+=1
    for word in paths([steps[-1].b]*2):
        so,rm=peel_b(steps,word)
        assert fill_b(steps,so,rm)==word; inv+=1
        for si in spaths:
            if word[-1][1]!=si[0][0]: continue
            assert slide(steps,word,si,'s')==(so,fill_a(steps,rm,si)); compat_b+=1
    for ri in rpaths:
        for si in spaths:
            if ri[-1][1]==si[0][0]:
                assert peel_a(steps,fill_a(steps,ri,si))==(ri,si); inv+=1
            if si[-1][1]==ri[0][0]:
                assert peel_b(steps,fill_b(steps,si,ri))==(si,ri); inv+=1
    recover_a=recover_b=0
    for word in paths([steps[0].a]*5):
        for h0 in range(g.q):
            hs=coords(word,g,h0)
            fw,fc=forward(steps,word,hs,g)
            bw,bc=backward(steps,fw,fc,g)
            assert (bw,bc)==((word[2],),(hs[2],)); recover_a+=1
    for word in paths([steps[-1].b]*5):
        for h0 in range(g.q):
            hs=coords(word,g,h0)
            bw,bc=backward(steps,word,hs,g)
            fw,fc=forward(steps,bw,bc,g)
            assert (fw,fc)==((word[2],),(hs[2],)); recover_b+=1
    augment_candidates=parity_cases=0
    for aa,bb,cc,dd in itertools.product(range(5),repeat=4):
        if aa*cc+bb*dd!=4 or aa*dd+bb*cc!=4: continue
        augment_candidates+=1
        # Necessary support form follows from XY=2E12 and YX=0,
        # then parity forces all four augmentation parameters even.
        if any(z%2 for z in (aa,bb,cc,dd)): continue
        for x1,x2,y1,y2 in itertools.product(range(-aa,aa+1,2),range(-bb,bb+1,2),range(-dd,dd+1,2),range(-cc,cc+1,2)):
            assert x1*y1+x2*y2!=2; parity_cases+=1
    return {'arithmetic':'exact integers', 'sampling':'none; listed finite sets exhausted',
            'group':'C2','matrix_sizes':[2,3,2], 'original_endpoints_unchanged':True,
            'factor_product_equalities':4,'lag_two_SE_product_checks':4,
            'cleared_denominator_rational_one_step_checks':2,
            'base_edge_counts':[len(st.a) for st in steps]+[len(steps[-1].b)],
            'compatibility_inputs_A':compat_a,'compatibility_inputs_B':compat_b,
            'triangle_inverse_identities':inv,
            'all_five_edge_words_and_starting_group_coordinates_recovery_A':recover_a,
            'all_five_edge_words_and_starting_group_coordinates_recovery_B':recover_b,
            'augmentation_parameter_candidates':augment_candidates,
            'necessary_parity_normal_form_cases':parity_cases,
            'scope':'finite instances; universal one-step exclusion is the separate paper divisibility proof, not this enumeration',
            'sentinel':'FIXED_C2_TWO_STEP_CLOSURE_CHECKS_PASSED'}


if __name__=='__main__':
    result=run()
    result['script_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    result['shared_script_sha256']=hashlib.sha256(Path(__file__).with_name('verify_partition_closure.py').read_bytes()).hexdigest()
    output=Path(__file__).with_name('fixed_c2_verification.json')
    output.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,ensure_ascii=False,indent=2))
