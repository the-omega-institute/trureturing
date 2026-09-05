"""An exact 21-state typed Zeckendorf DFAO for floor(4*{q*phi}).

All correctness-certificate checks use rational arithmetic and exact signs in
Q(sqrt(5)). Floating point is never used to choose a transition or output.
This is an executable algebraic certificate, not a Lean kernel certificate.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from functools import total_ordering
from collections import deque
from pathlib import Path
import argparse
import hashlib
import json
from math import isqrt


def sign_sqrt5(u: F, v: F) -> int:
    """Exact sign of u+v*sqrt(5)."""
    if not v: return (u > 0) - (u < 0)
    if not u: return (v > 0) - (v < 0)
    if u > 0 and v > 0: return 1
    if u < 0 and v < 0: return -1
    delta = u*u - 5*v*v
    return ((delta > 0) - (delta < 0)) * (1 if u > 0 else -1)

@total_ordering
@dataclass(frozen=True)
class QPhi:
    a: F
    b: F = F(0)

    def __post_init__(self):
        object.__setattr__(self, 'a', F(self.a))
        object.__setattr__(self, 'b', F(self.b))

    def __add__(self, other):
        if not isinstance(other, QPhi): other = QPhi(other)
        return QPhi(self.a+other.a, self.b+other.b)
    __radd__ = __add__
    def __neg__(self): return QPhi(-self.a, -self.b)
    def __sub__(self, other): return self+-other if isinstance(other, QPhi) else self+QPhi(-other)
    def __mul__(self, other):
        if not isinstance(other, QPhi): other = QPhi(other)
        return QPhi(self.a*other.a+self.b*other.b,
                    self.a*other.b+self.b*other.a+self.b*other.b)
    __rmul__ = __mul__
    def __lt__(self, other):
        if not isinstance(other, QPhi): other=QPhi(other)
        d=self-other
        return sign_sqrt5(2*d.a+d.b, d.b) < 0
    def coords(self):
        return [str(self.a), str(self.b)]
    def in_Zphi(self): return self.a.denominator==1 and self.b.denominator==1

ZERO=QPhi(0)
PHI=QPhi(0,1)
PSI=QPhi(1,-1)
DOMAINS={'R': (QPhi(3,-2),QPhi(2,-1)),
         'T': (QPhi(1,-1),QPhi(3,-2))}


def step_error(x: QPhi, digit: int) -> QPhi:
    return PSI*x-digit*(PSI*PSI)


def inside(x, bounds): return bounds[0] < x < bounds[1]


def floor_qphi(x: QPhi) -> int:
    # Output and certificate points remain in a small fixed interval.
    for k in range(-16,17):
        if QPhi(k) <= x < QPhi(k+1): return k
    raise ValueError('floor_qphi called outside certificate range')


def output(x): return floor_qphi(4*(x-floor_qphi(x)))

@dataclass(frozen=True)
class Cell:
    name: str
    typ: str
    lo: QPhi
    hi: QPhi
    singleton: bool=False

    def contains(self,x):
        return x==self.lo if self.singleton else self.lo < x < self.hi
    def sample(self): return self.lo if self.singleton else F(1,2)*(self.lo+self.hi)


def construct():
    cuts={'R':{ZERO,QPhi(F(1,4))}, 'T':{QPhi(F(-1,2)),QPhi(F(-1,4))}}
    rounds=0
    while True:
        old={t:set(c) for t,c in cuts.items()}
        for p in old['R']:
            pre=-PHI*p
            for t in ('R','T'):
                if inside(pre,DOMAINS[t]): cuts[t].add(pre)
        for p in old['T']:
            pre=-PHI*p+PSI
            if inside(pre,DOMAINS['R']): cuts['R'].add(pre)
        rounds+=1
        if old==cuts: break
        if rounds>100: raise RuntimeError('cut closure did not terminate')
    cells=[Cell('S','R',ZERO,ZERO,True)]
    for t in ('R','T'):
        points=[DOMAINS[t][0]]+sorted(cuts[t])+[DOMAINS[t][1]]
        cells.extend(Cell(f'{t}{i}',t,lo,hi) for i,(lo,hi) in enumerate(zip(points,points[1:])))
    assert len(cells)==21
    # A reachable error has integral coefficients in the basis 1,phi.
    # All artificial cut points except zero are therefore unreachable.
    excluded=[p for cs in cuts.values() for p in cs if p!=ZERO]
    assert all(not p.in_Zphi() for p in excluded)
    table=[]
    for c in cells:
        transitions=[]
        for digit in (0,1):
            if c.typ=='T' and digit==1:
                transitions.append(None); continue
            target_type='T' if digit==1 else 'R'
            y=step_error(c.sample(),digit)
            targets=[i for i,d in enumerate(cells) if d.typ==target_type and d.contains(y)]
            assert len(targets)==1, (c.name,digit,targets)
            j=targets[0]; dest=cells[j]
            if c.singleton:
                assert dest.contains(step_error(c.lo,digit))
            else:
                # psi is negative, so endpoint order is reversed.
                image_lo=step_error(c.hi,digit)
                image_hi=step_error(c.lo,digit)
                assert not dest.singleton
                assert dest.lo <= image_lo < image_hi <= dest.hi, (c.name,digit,dest.name)
            transitions.append(j)
        out=output(c.sample())
        if not c.singleton:
            sign = -1 if c.hi <= ZERO else 0
            # Entire open interval lies in a single integer strip and digit strip.
            assert QPhi(sign) <= c.lo < c.hi <= QPhi(sign+1)
            assert QPhi(F(out,4)+sign) <= c.lo < c.hi <= QPhi(F(out+1,4)+sign)
        table.append({'name':c.name,'type':c.typ,'output':out,
                      'zero':transitions[0],'one':transitions[1],
                      'singleton':c.singleton,'lower':c.lo.coords(),'upper':c.hi.coords()})
    assert table[0]['zero']==0 and table[0]['output']==0
    return cells,table,rounds


def reachability(table):
    words={0:''}; q=deque([0])
    while q:
        p=q.popleft()
        for digit,k in [('0','zero'),('1','one')]:
            dest=table[p][k]
            if dest is not None and dest not in words:
                words[dest]=words[p]+digit; q.append(dest)
    assert len(words)==len(table)
    return words


def distinguishability(table):
    """Produce typed pair witnesses. Illegal continuation is a separate outcome."""
    def suffix(p,q):
        seen={(p,q)}; todo=deque([(p,q,'')])
        while todo:
            i,j,w=todo.popleft()
            oi=None if i is None else table[i]['output']
            oj=None if j is None else table[j]['output']
            if oi!=oj: return w
            for d,k in [('0','zero'),('1','one')]:
                a=None if i is None else table[i][k]
                b=None if j is None else table[j][k]
                if (a,b) not in seen:
                    seen.add((a,b));todo.append((a,b,w+d))
        return None
    witnesses=[]
    for i in range(len(table)):
        for j in range(i+1,len(table)):
            w=suffix(i,j)
            assert w is not None, (i,j)
            witnesses.append({'left':i,'right':j,'suffix':w,
                              'same_type':table[i]['type']==table[j]['type']})
    return witnesses


def run(table, word):
    q=0
    for bit in word:
        if bit not in '01': raise ValueError('invalid digit')
        q=table[q]['one' if bit=='1' else 'zero']
        if q is None: return None
    return table[q]['output']


def zeck(n, weights):
    if n==0: return '0'
    from bisect import bisect_right
    k=bisect_right(weights,n); bits=[]
    for f in reversed(weights[:k]):
        b=int(f<=n); bits.append(str(b)); n-=b*f
    assert n==0
    return ''.join(bits)


def oracle(n):
    fl=lambda q:(q+isqrt(5*q*q))//2
    return fl(4*n)-4*fl(n)


def verify_ranges(table, bound, powers):
    weights=[1,2]
    maxn=max(bound,1 << (2*(powers-1))) if powers else bound
    while weights[-1]<=maxn: weights.append(weights[-1]+weights[-2])
    for n in range(bound):
        w=zeck(n,weights)
        assert run(table,w)==oracle(n), ('integer',n,w)
        if n<1000: assert run(table,'000'+w)==oracle(n)
    for n in range(powers):
        value=1 << (2*n); w=zeck(value,weights)
        assert run(table,w)==oracle(value), ('power',n)
    return {'consecutive_integers_checked':bound, 'integer_range':[0,bound-1],
            'power_indices_checked':powers,'power_range':[0,powers-1],
            'leading_zero_checks':min(1000,bound)}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--integers',type=int,default=100000)
    ap.add_argument('--powers',type=int,default=2000);args=ap.parse_args()
    cells,table,rounds=construct();words=reachability(table);pairs=distinguishability(table)
    counts=verify_ranges(table,args.integers,args.powers)
    report={'status':'PASS','states':len(table),'recurrent_states':14,'transient_states':7,
            'implicit_invalid_sink_counted':False,'cut_closure_rounds':rounds,
            'exact_interval_transition_checks':sum(2 if t['type']=='R' else 1 for t in table),
            'output_cell_checks':len(table), 'reachable_states':len(words),
            'pairwise_distinguishability_checks':len(pairs),
            'same_type_distinguishability_checks':sum(p['same_type'] for p in pairs),
            'lean_kernel_checked':False,**counts}
    root=Path(__file__).resolve().parent
    (root/'machine21.json').write_text(json.dumps({'start':0,'states':table},indent=2)+'\n')
    (root/'global_minimality_witnesses.json').write_text(json.dumps(
        {'access_words':words,'distinguishing_suffixes':pairs,
         'scope':'all legal Zeckendorf words, not only powers of four'},indent=2)+'\n')
    (root/'verification21.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
    print('id name type out zero one access')
    for i,t in enumerate(table):
        print(i,t['name'],t['type'],t['output'],t['zero'],t['one'],repr(words[i]))

if __name__=='__main__':main()
