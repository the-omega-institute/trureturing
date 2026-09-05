"""Exact source-bound check of shared zero responses and the 14-state profile.

Usage from a repository checkout:
    python Evidence/D5/Automata/GoldenBase4/check_zero_response.py .
Only the Python standard library is required. The original and new Lean tables
are read as data. This does not run Lean or establish a powers-only lower bound.
"""
from __future__ import annotations
import ast
from fractions import Fraction
from itertools import product
from pathlib import Path
import hashlib
import json
import re
import sys


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def vector(text: str, name: str):
    match = re.search(r'\bdef\s+' + re.escape(name) + r'\s*:[\s\S]*?:=\s*!\[', text)
    require(match is not None, 'missing vector ' + name)
    start = match.end() - 1
    depth = 0
    for end in range(start, len(text)):
        if text[end] == '[': depth += 1
        elif text[end] == ']':
            depth -= 1
            if depth == 0: break
    require(depth == 0, 'unclosed vector ' + name)
    body = text[start:end + 1].replace('![', '[')
    body = re.sub(r'\.inl\s+(\d+)', r'(0,\1)', body)
    body = re.sub(r'\.inr\s+(\d+)', r'(1,\1)', body)
    return ast.literal_eval(body)


def advance(a, q, k):
    for _ in range(k): q = a[q]
    return q


def multiply(a, b):
    require(a and b and len(a[0]) == len(b), 'matrix dimensions')
    return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]


def identity(n): return [[int(i==j) for j in range(n)] for i in range(n)]


def rank(a):
    a = [[Fraction(x) for x in row] for row in a]
    pivot = 0
    for column in range(len(a[0])):
        found = next((i for i in range(pivot,len(a)) if a[i][column]),None)
        if found is None: continue
        a[pivot],a[found]=a[found],a[pivot]
        scale=a[pivot][column]
        a[pivot]=[x/scale for x in a[pivot]]
        for i in range(len(a)):
            if i!=pivot:
                scale=a[i][column]
                a[i]=[x-scale*y for x,y in zip(a[i],a[pivot])]
        pivot+=1
        if pivot==len(a):break
    return pivot


def determinant(matrix):
    a=[row[:] for row in matrix];n=len(a);previous=1;sign=1
    for k in range(n-1):
        pivot=next((i for i in range(k,n) if a[i][k]),None)
        if pivot is None:return 0
        if pivot!=k:a[k],a[pivot]=a[pivot],a[k];sign=-sign
        for i in range(k+1,n):
            for j in range(k+1,n):
                numerator=a[i][j]*a[k][k]-a[i][k]*a[k][j]
                require(numerator%previous==0,'inexact determinant division')
                a[i][j]=numerator//previous
        for i in range(k+1,n):a[i][k]=0
        previous=a[k][k]
    return sign*a[-1][-1]


def verify_reference(original, concrete):
    a21,b21,out21 = (vector(original,n) for n in ['zeroTarget','oneTarget','output'])
    a,b,c,orig,rlag,clag,tests,inv = (vector(concrete,n) for n in
        ['zero','select','returnTo','origin','rowDelay','columnDelay','test','profileInverse'])
    require(len(a)==len(b)==14 and len(c)==7, 'carrier sizes')
    require(a21[:14]==a, 'zero rows disagree')
    require([14+x for x in b]==b21[:14], 'one rows disagree')
    require(c==a21[14:], 'transient returns disagree')
    f=out21[:14]
    require([advance(a,q,k) for q,k in zip(orig,rlag)]==list(range(14)), 'access coverage')
    def probe(q,t):return int((f if t[0]==0 else b)[q]==t[1])
    m=[[probe(advance(a,orig[i],rlag[i]+clag[j]),tests[j]) for j in range(14)] for i in range(14)]
    left=[[int(q==advance(a,orig[i],rlag[i])) for q in range(14)] for i in range(14)]
    right=[[probe(advance(a,q,clag[j]),tests[j]) for j in range(14)] for q in range(14)]
    require(multiply(left,right)==m, 'reference factorization')
    require(multiply(m,inv)==identity(14), 'right inverse fails')
    require(multiply(inv,m)==identity(14), 'left inverse fails')
    ranks=[]
    for horizon in range(1,5):
        full=[[probe(advance(a,q,k),t) for k in range(horizon)
                for t in [(0,d) for d in range(4)]+[(1,s) for s in range(7)]] for q in range(14)]
        ranks.append(rank(full))
    require(ranks==[9,12,13,14], 'unexpected horizon ranks')
    return m,inv,ranks


def check_small_models():
    counters=dict(models=0,factorization_entries=0,zero_prefix_evaluations=0,gap_evaluations=0,
                  models_with_self_loops=0,models_with_unused_slots=0,models_with_duplicate_pairs=0)
    tails=[w for n in range(3) for w in product((0,1),repeat=n)]
    for r,s in product((1,2),repeat=2):
        for a,b,c,f in product(product(range(r),repeat=r),product(range(s),repeat=r),
                                product(range(r),repeat=s),product(range(4),repeat=r)):
            counters['models']+=1
            # Transient labels do not enter the rank theorem; one fixed label map
            # is sufficient for this separately scoped run-equation regression.
            g=tuple(t%4 if f[0]%2 else 0 for t in range(s))
            counters['models_with_self_loops']+=any(a[q]==q for q in range(r))
            counters['models_with_unused_slots']+=len(set(b))<s
            counters['models_with_duplicate_pairs']+=len({(g[t],c[t]) for t in range(s)})<s
            def probe(q,t):return int((f if t[0]==0 else b)[q]==t[1])
            def evaluate(q,word,terminal):
                for block in word:q=a[q] if block==0 else c[b[q]]
                return g[b[q]] if terminal else f[q]
            rows=[(q,i) for q in range(r) for i in range(3)]
            cols=[(j,t) for j in range(3) for t in
                  [(0,d) for d in range(4)]+[(1,t) for t in range(s)]]
            lhs=[[probe(advance(a,q,i+j),t) for j,t in cols] for q,i in rows]
            l=[[int(x==advance(a,q,i)) for x in range(r)] for q,i in rows]
            rr=[[probe(advance(a,x,j),t) for j,t in cols] for x in range(r)]
            require(multiply(l,rr)==lhs, 'small factorization fails')
            counters['factorization_entries']+=len(rows)*len(cols)
            for q,k in product(range(r),range(4)):
                qk=advance(a,q,k)
                for tail,terminal in product(tails,(0,1)):
                    require(evaluate(q,(0,)*k+tail,terminal)==evaluate(qk,tail,terminal),'zero-prefix equation')
                    counters['zero_prefix_evaluations']+=1
                require(evaluate(q,(1,)+(0,)*k,1)==g[b[advance(a,c[b[q]],k)]],'shared gap equation')
                counters['gap_evaluations']+=1
    return counters


def main(repo: Path):
    base=repo/'D5/S1/Digit/GoldenBase4IntervalMachine.lean'
    specific=repo/'D5/S1/Digit/GoldenBase4ZeroResponse.lean'
    generic=repo/'D5/S0/Certificates/SkeletonSlotZeroResponse.lean'
    original,concrete=base.read_text(),specific.read_text()
    matrix,inverse,ranks=verify_reference(original,concrete)
    cert=json.loads((repo/'Evidence/D5/Automata/GoldenBase4/zero_response_minor14.json').read_text())
    require(matrix==cert['matrix'] and inverse==cert['inverse'], 'serialized certificate disagrees with source')
    require(determinant(matrix)==cert['determinant']==-1,'determinant certificate')
    returns,orig,rlag,clag,tests=(vector(concrete,n) for n in ['returnTo','origin','rowDelay','columnDelay','test'])
    require([[k,'output' if t[0]==0 else 'slot',t[1]] for k,t in zip(clag,tests)]==cert['columns'],'column metadata')
    for i,access in enumerate(cert['row_access']):
        expected=(0,0) if access is None else (returns[access[0]],access[1])
        require((orig[i],rlag[i])==expected,'row metadata')
    bad={
      'wrong_return':concrete.replace('![13,12,12,11,10,9,9]','![12,12,12,11,10,9,9]',1),
      'wrong_probe':concrete.replace('![.inl 0,.inl 1,.inl 3','![.inl 1,.inl 1,.inl 3',1),
      'wrong_origin':concrete.replace('![0,13,12,10,9,13,13,9,12,9,10,11,12,13]',
                                      '![1,13,12,10,9,13,13,9,12,9,10,11,12,13]',1),
      'wrong_inverse':concrete.replace('![0,1,-1,1,0,-1,1,0,0,0,0,0,0,0]',
                                       '![1,1,-1,1,0,-1,1,0,0,0,0,0,0,0]',1)}
    rejected=[]
    for name,text in bad.items():
        require(text!=concrete, 'mutation missing '+name)
        try:verify_reference(original,text)
        except ValueError:rejected.append(name)
        else:raise ValueError('mutation accepted '+name)
    result={'status':'PASS','reference_rank':14,'reference_determinant':-1,'joint_response_ranks_by_horizon':ranks,
            'inverse_products_checked':2,'reference_scalar_product_equalities':392,
            'small_models':check_small_models(),'rejected_mutations':rejected,
            'sources':{str(p.relative_to(repo)):hashlib.sha256(p.read_bytes()).hexdigest()
                       for p in [base,generic,specific]},
            'lean_executed':False,'new_powers_only_state_lower_bound':False,
            'scope':'Exact shared-zero constraints for every slot candidate; rank 14 only for the fixed labelled reference profile.'}
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    require(len(sys.argv)==2,'usage: check_zero_response.py repository_root')
    main(Path(sys.argv[1]))
