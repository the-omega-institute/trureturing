"""Exhaustive finite audit of the channel retraction; no Lean execution.
Usage: python check_channel_retraction.py
The general theorem is in SkeletonChannelRetraction.lean. Unknown outputs and
undefined transitions are included. Every optional output-return signature is
enumerated for carriers of size one and two. This does not assert a new lower bound.
"""
from itertools import product
from pathlib import Path
import hashlib,json

def check():
    models=checks=strict=failures=0
    words=[w for k in range(4) for w in product(range(2),repeat=k)]
    f=lambda d:0 if d==2 else d
    g=lambda d:1 if d==0 else d
    def evaluate(A,P,F,q,w,t):
        for b in w:
            if b==0:q=A[q]
            else:q=None if P[q] is None else P[q][1]
            if q is None:return None
        return F[q] if t==0 else None if P[q] is None else P[q][0]
    for r in [1,2]:
        targets=[None]+list(range(r))
        signatures=[None]+list(product(range(4),targets))
        for A in product(targets,repeat=r):
            for P in product(signatures,repeat=r):
                Pnew=tuple(None if p is None else (g(p[0]),p[1]) for p in P)
                oldcost=r+len(set(P)-{None});newcost=r+len(set(Pnew)-{None})
                assert newcost<=oldcost
                for F in product(range(4),repeat=r):
                    models+=1;strict+=newcost<oldcost
                    Fnew=tuple(map(f,F))
                    assert 2 not in Fnew and all(p is None or p[0]!=0 for p in Pnew)
                    for q,w,t in product(range(r),words,range(2)):
                        old=evaluate(A,P,F,q,w,t);new=evaluate(A,Pnew,Fnew,q,w,t)
                        expected=None if old is None else (f if t==0 else g)(old)
                        assert new==expected
                        checks+=1;failures+=old is None
    # A mistaken return rewrite must be detected independently of output values.
    badA=(1,0);P=((2,1),(1,0));F=(0,3);Pbad=((2,0),(1,0))
    assert evaluate(badA,P,F,0,(1,),0)!=evaluate(badA,Pbad,F,0,(1,),0)
    return dict(status='PASS',models=models,evaluation_equalities=checks,
                undefined_evaluations_preserved=failures,strict_cost_reduction_models=strict,
                wrong_return_mutation_rejected=True,lean_executed=False,new_state_lower_bound=False)
if __name__=='__main__':
    report=check()
    here=Path(__file__).resolve()
    root=here.parents[4]
    names=['D5/S0/Certificates/SkeletonChannelRetraction.lean',
           'Blueprint/D5/S0/Certificates/SkeletonChannelRetraction.scribe.cs']
    report['sha256']={n:hashlib.sha256((root/n).read_bytes()).hexdigest() for n in names}
    print(json.dumps(report,indent=2))
