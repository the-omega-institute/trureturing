"""Bounded exact regression of M01 dense-input transport.

Uses the table parsed from GoldenBase4IntervalMachine.lean. Occupied Fibonacci
indices are obtained greedily; the dense word uses the unchanged M01 expression.
The universal arguments are in GoldenBase4DenseInput.lean. This executable is
not a Lean proof and does not certify a powers-only lower bound.
Usage: python check_dense_input.py path/to/GoldenBase4IntervalMachine.lean
"""
from __future__ import annotations
from bisect import bisect_right
import hashlib
import json
from math import isqrt
from pathlib import Path
import sys
from check_interval_source import table, require


def verify(source: Path, integers: int = 20000, powers: int = 1000) -> dict:
    text = source.read_text()
    A, B, O = (table(text, x) for x in ['zeroTarget', 'oneTarget', 'output'])
    fib = [0, 1, 1, 2]
    while fib[-1] <= max(integers, 4**powers):
        fib.append(fib[-1]+fib[-2])

    def occupied(n: int) -> list[int]:
        result=[]
        while n:
            i=bisect_right(fib,n)-1
            require(i>=2,'invalid occupied index')
            result.append(i)
            n-=fib[i]
        return result

    def check(n: int) -> None:
        indices=occupied(n)
        k=indices[0]-1 if indices else 1
        present=set(indices)
        bits=[int(i+2 in present) for i in reversed(range(k))]
        require(all(2<=i<k+2 for i in indices),'display bound')
        require(all(a>=b+2 for a,b in zip(indices,indices[1:])),'canonical separation')
        require(len(present)==len(indices),'duplicate index')
        require({i+2 for i in range(k) if i+2 in present}==present,'range bijection')
        require(sum(fib[j] for j in indices)==n,'upstream occupied sum')
        value=sum(bit*fib[len(bits)+1-j] for j,bit in enumerate(bits))
        require(value==n,'dense weighted value')
        state=0
        for bit in bits:
            require(state<14 or bit==0,'illegal base step')
            state=A[state] if bit==0 else B[state]
        floor_phi=lambda m:(m+isqrt(5*m*m))//2
        digit=floor_phi(4*n)-4*floor_phi(n)
        require(O[state]==digit,'oracle mismatch')

    for n in range(integers):check(n)
    for i in range(powers):check(4**i)
    return {'status':'PASS','interval_source_sha256':hashlib.sha256(text.encode()).hexdigest(),
            'consecutive_integers':integers,'power_inputs':powers,
            'first_power_index':0,'last_power_index':powers-1,
            'input_zero_word':[0],'range_bijection_checked':True,
            'canonical_separation_checked':True,'exact_oracle_checked':True,
            'floating_point_used':False,'lean_executed':False}

if __name__=='__main__':
    require(len(sys.argv)==2,'usage: check_dense_input.py Lean_table_file')
    print(json.dumps(verify(Path(sys.argv[1])),indent=2))
