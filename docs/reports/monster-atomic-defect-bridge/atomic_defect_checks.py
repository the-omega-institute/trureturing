#!/usr/bin/env python3
"""Exact finite diagnostics for the atomic/defect bridge.

No VOA, Monster, OPE intertwiner, or analytic modular theorem is constructed.
The script checks finite sign, quadratic-space, and truncated character data.
"""
from __future__ import annotations
from collections import Counter
from fractions import Fraction as Q
from itertools import combinations, product, permutations
from math import comb
import json

COUNTS: Counter[str] = Counter()

def require(ok: bool, name: str, detail=None) -> None:
    if not ok:
        raise AssertionError((name, detail))
    COUNTS[name] += 1

def dot(a: int, b: int) -> int:
    return (a & b).bit_count() & 1

def cross(a: int, b: int) -> int:
    x = [(a >> i) & 1 for i in range(3)]
    y = [(b >> i) & 1 for i in range(3)]
    return ((x[1]*y[2] ^ x[2]*y[1]) |
            ((x[2]*y[0] ^ x[0]*y[2]) << 1) |
            ((x[0]*y[1] ^ x[1]*y[0]) << 2))

def qbit(a: int) -> int:
    return dot(a & 7, a >> 3)

def bbit(a: int, b: int) -> int:
    return qbit(a ^ b) ^ qbit(a) ^ qbit(b)

def xor_sum(items) -> int:
    out = 0
    for item in items:
        out ^= item
    return out

def sign_tables():
    base = [0, 1, 3, 6, 7, 4, 5, 2]
    for gauge in range(8):
        pairs = [(0,1), (0,2), (1,2)]
        cols = [0,0,0]
        for k,(i,j) in enumerate(pairs):
            if (gauge >> k) & 1:
                cols[i] ^= 1 << j
                cols[j] ^= 1 << i
        yield [base[g] ^ xor_sum(cols[i] for i in range(3) if (g>>i)&1)
               for g in range(8)]

def mul_vec(x, y, ell):
    out = [Q(0)] * 8
    for g, xv in enumerate(x):
        for h, yv in enumerate(y):
            out[g ^ h] += xv * yv * (-1)**dot(ell[g], h)
    return out

def unit_vec(i):
    return [Q(int(i == j)) for j in range(8)]

def norm2(x):
    return sum(t*t for t in x)

def matrix_entry_left(ell, g, row, col):
    return (-1)**dot(ell[g], col) if row == (g ^ col) else 0

def sign_equation_rank() -> int:
    # Unknown coefficients ell[g](e_i), g=1,...,7 and i=0,1,2.
    equations = []
    def term(g,h):
        return sum(1 << (3*(g-1)+i) for i in range(3) if (h>>i)&1)
    for g in range(1,8):
        equations.append((term(g,g),1))
    for g,h in combinations(range(1,8),2):
        equations.append((term(g,h)^term(h,g),1))
    pivots = {}
    for mask,rhs in equations:
        while mask:
            p = mask.bit_length()-1
            if p in pivots:
                m,r = pivots[p]
                mask ^= m
                rhs ^= r
            else:
                pivots[p] = (mask,rhs)
                break
        if not mask:
            require(rhs == 0, 'gaussian_consistency')
    return len(pivots)

def poly_mul(a,b,N):
    out=[0]*(N+1)
    for i,x in enumerate(a):
        if not x: continue
        for j,y in enumerate(b[:N+1-i]):
            if y: out[i+j]+=x*y
    return out

def euler_power(N,power,plus=False):
    """Product_(n>=1) (1 +/- q^n)^power through q^N, integer power."""
    a=[1]+[0]*N
    for n in range(1,N+1):
        factor=[0]*(N+1)
        for k in range(N//n+1):
            if power>=0:
                val=comb(power,k) if k<=power else 0
            else:
                val=(-1)**k * comb(-power+k-1,k)
            factor[k*n] = val if plus else val*(-1)**k
        a=poly_mul(a,factor,N)
    return a

def character_data(K=20):
    # One extra term accounts for the q^-1 prefactor.
    N=K+2
    t_numerator=euler_power(N,-24,True)
    p_numerator=euler_power(N,24,True)
    FA={k-1:Q(v) for k,v in enumerate(t_numerator)}
    FA[0]=FA.get(0,0)+24
    for k,v in enumerate(p_numerator): FA[k+1]=FA.get(k+1,0)+4096*v
    def sigma(n,p): return sum(d**p for d in range(1,n+1) if n%d==0)
    E4=[1]+[240*sigma(n,3) for n in range(1,N+1)]
    E6=[1]+[-504*sigma(n,5) for n in range(1,N+1)]
    jnum=poly_mul(poly_mul(poly_mul(E4,E4,N),E4,N),euler_power(N,-24),N)
    J={k-1:Q(v) for k,v in enumerate(jnum)}
    J[0]-=744
    cnum=poly_mul(E6,euler_power(N,-12),N)
    C={2*k-1:Q(v) for k,v in enumerate(cnum)}
    exps=range(-2,K+1)
    A={e:FA.get(e,Q(0)) for e in exps}
    AT={e:(-1 if e%2 else 1)*A[e] for e in exps}
    F2={e:FA.get(e//2,Q(0)) if e%2==0 else Q(0) for e in exps}
    J2={e:J.get(e//2,Q(0)) if e%2==0 else Q(0) for e in exps}
    for e in exps:
        require(A[e]+AT[e]==J2[e]-F2[e], 'cyclic_character_identity', e)
    classes={
        0:{e:(J2[e]+7*F2[e])/8 for e in exps},
        1:{e:(A[e]-AT[e]+6*C.get(e,0))/8 for e in exps},
        2:{e:(A[e]-AT[e]-2*C.get(e,0))/8 for e in exps},
        3:{e:(J2[e]-F2[e])/8 for e in exps},
    }
    for w,coeffs in classes.items():
        for e,v in coeffs.items():
            require(v.denominator==1 and v>=0, 'character_integrality_positive', (w,e))
    return exps,A,AT,C,F2,J2,classes

def all_lagrangians():
    out=set()
    singular=[a for a in range(1,64) if qbit(a)==0]
    require(len(singular)==35,'singular_count')
    for a,b,c in combinations(singular,3):
        if bbit(a,b) or bbit(a,c) or bbit(b,c): continue
        L=frozenset([0,a,b,c,a^b,a^c,b^c,a^b^c])
        if len(L)==8: out.add(L)
    require(len(out)==30,'lagrangian_count')
    return sorted(out,key=lambda L:tuple(sorted(L)))

def run():
    COUNTS.clear()
    require(sign_equation_rank()==18,'sign_rank')
    tables=list(sign_tables())
    require(len({tuple(x) for x in tables})==8,'eight_tables')
    Ls=all_lagrangians()
    exps,A,AT,C,F2,J2,classes=character_data()
    leading={}
    for w,coeffs in classes.items():
        e=min(e for e,v in coeffs.items() if v)
        leading[w]={'h':str(Q(e,2)+1),'dimension':int(coeffs[e])}
    sample={}
    for gauge,ell in enumerate(tables):
        for g,h,k in product(range(8),repeat=3):
            require(dot(ell[g],h^k)==(dot(ell[g],h)^dot(ell[g],k)), 'row_characters')
            delta=ell[g]^ell[h]^ell[g^h]
            require(delta==cross(g,h), 'missing_charge')
            f=lambda u,v:dot(ell[u],v)
            df=f(g,h)^f(g^h,k)^f(h,k)^f(g,h^k)
            require(df==dot(cross(g,h),k),'associator_determinant')
        for g in range(1,8):
            require(dot(ell[g],g)==1,'diagonal_sign')
            for j in range(8):
                Lg=lambda x:mul_vec(unit_vec(g),x,ell)
                require(Lg(Lg(unit_vec(j)))==[-v for v in unit_vec(j)],'left_square')
            for h in range(g+1,8):
                require(dot(ell[g],h)^dot(ell[h],g)==1,'reciprocal_sign')
                for j in range(8):
                    left=mul_vec(unit_vec(g),mul_vec(unit_vec(h),unit_vec(j),ell),ell)
                    right=mul_vec(unit_vec(h),mul_vec(unit_vec(g),unit_vec(j),ell),ell)
                    require(all(a+b==0 for a,b in zip(left,right)),'clifford_pairs')
        for t in range(20):
            x=[Q(((i+2)*(t+3)%11)-5,3) for i in range(8)]
            y=[Q(((i+4)*(t+1)%13)-6,5) for i in range(8)]
            require(norm2(mul_vec(x,y,ell))==norm2(x)*norm2(y),'norm_samples')
        atoms=[g|(ell[g]<<3) for g in range(1,8)]
        require(xor_sum(atoms)==0,'seven_relation')
        reps={}
        for w in range(4):
            for inds in combinations(range(7),w):
                a=xor_sum(atoms[i] for i in inds)
                require(a not in reps,'subset_uniqueness')
                reps[a]=inds
                require(qbit(a)==(w*(w+1)//2)%2,'subset_quadratic_form')
        require(len(reps)==64,'complete_64')
        for a in range(64):
            g,xi=a&7,a>>3
            for e in exps:
                if g==0:
                    z=(J2[e]+(7 if xi==0 else -1)*F2[e])/8
                else:
                    total=Q(0)
                    for h in range(8):
                        zh=A[e] if h==0 else AT[e] if h==g else (-1)**dot(ell[g],h)*C.get(e,0)
                        total+=(-1)**dot(xi,h)*zh
                    z=total/8
                require(z==classes[len(reps[a])][e],'all_module_fourier_coefficients',(a,e))
        for g,h in combinations(range(1,8),2):
            a=(g|(ell[g]<<3))^(h|(ell[h]<<3))
            k=g^h
            require(len(reps[a])==2 and (a>>3)!=ell[k],'pair_not_ground')
            require(leading[2]=={'h':'3/2','dimension':1216},'pair_target_lowest')
            require(cross(h,g^h)==cross(g,h),'fibonacci_missing_charge_invariant')
            # The homogeneous imaginary-unit Fibonacci orbit has exact period 3.
            seq=[(1,g),(1,h)]
            for _ in range(7):
                s,x=seq[-1];t,y=seq[-2]
                seq.append((s*t*(-1)**dot(ell[x],y),x^y))
            require(all(seq[i]==seq[i+3] for i in range(len(seq)-3)),'fibonacci_period_three')
        for L in Ls:
            require(all(len(reps[x])==3 for x in L if x),'lagrangian_triples')
            lines=[reps[x] for x in L if x]
            require(Counter(pair for line in lines for pair in combinations(line,2))==
                    Counter(combinations(range(7),2)),'fano_pair_cover')
            seen=set()
            for a in atoms:
                cos=frozenset(a^l for l in L)
                require(cos not in seen and sum(x in cos for x in atoms)==1,'one_atom_per_coset')
                seen.add(cos)
            for e in exps:
                require(sum(classes[len(reps[l])][e] for l in L)==J2[e],'extension_character_J')
            for a in range(1,64):
                if a in L:continue
                for e in exps:
                    tw=sum((-1)**bbit(a,l)*classes[len(reps[l])][e] for l in L)
                    require(tw==F2[e],'dual_twining_all_A')
        if gauge==0:
            # All permutations of the seven generators act on the quotient
            # F2^7/<all-ones>; the marked electric subspace is a Fano plane.
            electric=frozenset(a for a in range(64) if (a & 7)==0)
            base_lines=frozenset(frozenset(reps[a]) for a in electric if a)
            orbit=set(); stabilizer=0
            for perm in permutations(range(7)):
                new_lines=frozenset(frozenset(perm[i] for i in line) for line in base_lines)
                orbit.add(new_lines)
                stabilizer+=int(new_lines==base_lines)
            require(len(orbit)==30, 'S7_fano_orbit')
            require(stabilizer==168, 'marked_GL3_stabilizer')
            for i in range(6):
                perm=list(range(7)); perm[i],perm[i+1]=perm[i+1],perm[i]
                f=lambda a:xor_sum(atoms[perm[j]] for j in reps[a])
                for a in range(64):
                    require(qbit(f(a))==qbit(a), 'S7_quadratic_generators')
                    require(len(reps[f(a)])==len(reps[a]), 'S7_character_generators')
                    for b in range(64):
                        require(f(a^b)==(f(a)^f(b)), 'S7_fusion_generators')
            for charge in range(1,8):
                require(any(qbit(g)^qbit(g|(charge<<3)) for g in range(8)),
                        'discarded_charge_changes_spin')
            # Three independent ground labels: the cochain model is nonassociative.
            left=mul_vec(mul_vec(unit_vec(1),unit_vec(2),ell),unit_vec(4),ell)
            right=mul_vec(unit_vec(1),mul_vec(unit_vec(2),unit_vec(4),ell),ell)
            require(left!=right and left==[-v for v in right],'nonassociativity_control')
            sample={'ell':ell,'atoms_encoded_g_plus_8xi':atoms,
                    'charge_delta_1_2':ell[1]^ell[2]^ell[3],
                    'external_direction_4_sign':(-1)**dot(ell[1]^ell[2]^ell[3],4),
                    'associator_e1_e2_e4':{'left':list(map(str,left)),'right':list(map(str,right))},
                    'one_lagrangian':sorted(Ls[0])}
    return {'status':'passed','arithmetic':'exact integers/Fraction',
            'counts':dict(sorted(COUNTS.items())),
            'number_sign_tables':8,'sector_counts':[1,7,21,35],
            'leading_by_atomic_length':leading,'lagrangian_count':30,'character_preserving_label_group':'S7',
            'label_group_order':5040,'marked_stabilizer_order':168,
            'sample':sample,
            'scope':'Finite diagnostics only; no VOA, Monster, physical OPE, module realization, extension construction, or Lean verification.'}

if __name__=='__main__':
    print(json.dumps(run(),ensure_ascii=False,indent=2))
