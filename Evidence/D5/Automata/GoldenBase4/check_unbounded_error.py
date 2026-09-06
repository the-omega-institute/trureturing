"""Source-bound finite certificate checks, not a Lean execution.

Usage: python check_unbounded_error.py reference.lean new_source.lean
The universal pumping and cardinality arguments are in the accompanying Lean
source. The power scan is bounded regression only. No power-only minimum is
asserted. Python standard library only, no numerical approximation.
"""
from __future__ import annotations
import ast
from bisect import bisect_right
from hashlib import sha256
from math import isqrt
from pathlib import Path
import json
import re
import sys


def require(h: bool, message: str) -> None:
    if not h:
        raise ValueError(message)


def literal(text: str, name: str):
    m = re.search(r'\bdef\s+' + name + r'\s*:[\s\S]*?:=\s*!?\[', text)
    require(m is not None, 'literal missing: ' + name)
    start = m.end()-1
    depth = 0
    for end in range(start, len(text)):
        if text[end] == '[': depth += 1
        elif text[end] == ']': depth -= 1
        if depth == 0: break
    require(depth == 0, 'unclosed literal')
    return ast.literal_eval(text[start:end+1].replace('![','['))


def verify(ref: str, src: str):
    A,B,O = (literal(ref,n) for n in ('zeroTarget','oneTarget','output'))
    tails,tests,cycle = (literal(src,n) for n in ('accessTail','suffix','cycleWord'))
    require(len(A)==len(B)==len(O)==21, 'reference dimensions')
    require(len(tails)==20 and len(tests)==13, 'certificate dimensions')
    require(A[0]==0 and O[0]==0, 'initial anchors')
    def run(q,word):
        for a in word:
            require(a in (0,1), 'nonbinary symbol')
            if q>=14 and a==1: return None
            q=(A if a==0 else B)[q]
        return q
    def value(word):
        q,v=0,0
        for a in word:q,v=v+a,q+v+2*a
        return q
    def digit(q):
        fl=lambda v:(v+isqrt(5*v*v))//2
        return fl(4*q)-4*fl(q)
    def same_type(q,t):return (q<14)==(t<14)
    def witness(q,t):
        for j,w in enumerate(tests):
            a,b=run(q,w),run(t,w)
            if a is not None and b is not None and O[a]!=O[b]:return j
        raise ValueError(f'unseparated pair {q},{t}')
    require(run(0,[1])==18, 'entry')
    require(run(18,cycle)==18 and cycle.count(1)==1, 'pumping cycle')
    require([run(18,w) for w in tails]==list(range(1,21)), 'access certificate')
    require(all(A[q]!=q for q in range(1,21)), 'core zero fixed point')
    pairs=[]
    for q in range(21):
        for t in range(q+1,21):
            if same_type(q,t):pairs.append([q,t,witness(q,t)])
    require(len(pairs)==112, 'pair coverage')
    checks=0
    for k in (0,1,6,14,64):
        pump=[1]+cycle*k
        require(pump.count(1)==k+1 and run(0,pump)==18, 'pumped prefix')
        words=[pump+w for w in tails]
        for q,w in enumerate(words,1):
            require(run(0,w)==q and w.count(1)>k, 'pumped access')
            require(w[0]==1 and all(a*b==0 for a,b in zip(w,w[1:])), 'canonical word')
            # All legal diagnostic continuations are checked with an arithmetic oracle.
            for suffix in tests:
                end=run(q,suffix)
                if end is not None:
                    require(digit(value(w+suffix))==O[end], 'oracle mismatch')
                    checks+=1
            if q<14:
                j=witness(q,A[q])
                x,y=w+tests[j],w+[0]+tests[j]
                require(x.count(1)>k and y.count(1)>k, 'fixed-point weight')
                require(digit(value(x))!=digit(value(y)), 'zero-fixed-point obstruction')
                checks+=2
    f=[0,1,1,2]
    while f[-1]<=4**999:f.append(f[-1]+f[-2])
    def indices(q):
        result=[]
        while q:
            j=bisect_right(f,q)-1;result.append(j);q-=f[j]
        return result
    endpoints={};six=[]
    for n in range(1000):
        inds=indices(4**n);occ=set(inds)
        word=[int(j in occ) for j in range(inds[0],1,-1)]
        q=run(0,word)
        require(q is not None and O[q]==digit(4**n), 'power scan')
        require(value(word)==4**n,'power word value')
        if q not in endpoints:
            endpoints[q]={'state':q,'power_index':n,'indices':inds,'digit':O[q]}
        if len(inds)==6:six.append(n)
    require(set(endpoints)==set(range(1,21)), 'power-terminal state coverage')
    require(max(v['power_index'] for v in endpoints.values())==62,'power-terminal cutoff')
    require(six==[6,7,14], 'weight-six finite scan')
    # Verify the three even-exponent rows from Table 4 of arXiv:2608.04445v1.
    rows={6:[2,4,12,14,16,18],7:[4,9,13,16,19,21],14:[2,8,12,20,29,42]}
    for n,inds in rows.items():
        require(sum(f[j] for j in inds)==4**n,'literature row value')
        require(all(b>=a+2 for a,b in zip(inds,inds[1:])),'literature row canonicality')
    return {'status':'PASS','separated_same_type_pairs':112,'core_access_states':20,
        'core_zero_nonfixed_states':20,'suffix_count':13,'maximum_suffix_length':max(map(len,tests)),
        'pumping_cycle':cycle,'pumping_weights_tested':[0,1,6,14,64],
        'pumped_arithmetic_checks':checks,'power_terminal_first_indices':[endpoints[i]['power_index'] for i in range(1,21)],
        'power_scan_extent':1000,'all_core_states_terminal_by_index':62,
        'weight_six_indices_in_scan':six,'literature_rows_recomputed':3,
        'external_diophantine_completeness_reproved':False,
        'universal_claim':'Fewer than 21 anchored typed states implies arithmetic errors of unbounded one-count on legal integer words.',
        'powers_only_minimum_proved':False,'lean_executed':False,
        'reference_sha256':sha256(ref.encode()).hexdigest(),'source_sha256':sha256(src.encode()).hexdigest()}


def main():
    require(len(sys.argv)==3,'usage: check_unbounded_error.py reference.lean new_source.lean')
    ref,src=(Path(p).read_text() for p in sys.argv[1:])
    result=verify(ref,src)
    mutations={
        'wrong_cycle':src.replace(':= [0,0,0,0,1]',':= [0,0,0,1]',1),
        'wrong_access':src.replace('![[0,1,0,1,0,0]','![[0,1,0,1,0]',1),
        'missing_final_separator':src.replace('[1,0,1,0,0,1]]','[0]]',1)}
    rejected=[]
    for name,mutant in mutations.items():
        require(mutant!=src,'mutation not applied: '+name)
        try:verify(ref,mutant)
        except ValueError:rejected.append(name)
        else:raise ValueError('mutation accepted: '+name)
    result['rejected_mutations']=rejected
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
