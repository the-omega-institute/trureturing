#!/usr/bin/env python3
"""Exact source-query, positive-pair, and priced-loader certificates for section88.

Python >=3.10, standard library. Requires companion verify.py. The cylinder
checks do not enumerate all adaptive trees; their universal scope is proved in
the theory text. The loader assumes persistent coordinate access and dial reset.
"""
import argparse
from collections import Counter
from fractions import Fraction as Q
import importlib.util
from itertools import combinations, product
import json
from math import prod
from pathlib import Path

if not __debug__:
    raise RuntimeError('Exact verification requires assertions; remove -O/PYTHONOPTIMIZE.')
_spec = importlib.util.spec_from_file_location('two51_query_helpers', Path(__file__).with_name('verify.py'))
if _spec is None or _spec.loader is None:
    raise ImportError('Cannot load companion linear algebra helpers.')
_helpers = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_helpers)
rank = _helpers.rank
DIMS = (5, 3, 2, 2)
POINTS = list(product(*(range(n) for n in DIMS)))


def contrast(x):
    return (-1)**sum(x) if x[0] < 2 and x[1] < 2 else 0


def cylinders_and_pair():
    w = [contrast(x) for x in POINTS]
    plus = [Q(1,60)+Q(t,120) for t in w]
    minus = [Q(1,60)-Q(t,120) for t in w]
    assert sum(plus) == sum(minus) == 1 and min(plus+minus) == Q(1,120)
    rows, layers, cylinder_counts = [], [], []
    for r in range(5):
        before = len(rows)
        for indices in combinations(range(4), r):
            for values in product(*(range(DIMS[i]) for i in indices)):
                row = [int(tuple(x[i] for i in indices) == values) for x in POINTS]
                rows.append(row)
                if r < 4:
                    assert sum(a*b for a,b in zip(row,w)) == 0
                    assert sum(a*b for a,b in zip(row,plus)) == sum(a*b for a,b in zip(row,minus))
                # Every non-full cylinder contains >=2 different source configs.
                assert sum(row) == prod(DIMS[i] for i in range(4) if i not in indices)
        layers.append(rank(rows))
        cylinder_counts.append(len(rows)-before)
    assert layers == [1,9,30,52,60] and cylinder_counts == [1,12,51,92,60]
    digit = [((5*a+4*b+2*c+d)%25)//5 for a,b,c,d in POINTS]
    delta = [sum(t for t,h in zip(w,digit) if h == v) for v in range(5)]
    p = [sum(t for t,h in zip(plus,digit) if h == v) for v in range(5)]
    q = [sum(t for t,h in zip(minus,digit) if h == v) for v in range(5)]
    assert delta == [-1,2,-1,0,0]
    tv = lambda a,b: sum(abs(x-y) for x,y in zip(a,b))/2
    assert tv(p,q) == Q(1,30) and tv(plus,minus) == Q(2,15)
    # A genuinely branch-dependent three-coordinate protocol; tests its leaves,
    # not a claim to enumerate every policy.
    def transcript(x):
        first = 0
        second = 1 if x[first] % 2 == 0 else 2
        third = next(i for i in (3,2,1) if i not in (first,second))
        return tuple((i,x[i]) for i in (first,second,third))
    leaves = {transcript(x) for x in POINTS}
    for leaf in leaves:
        ids = [i for i,x in enumerate(POINTS) if transcript(x) == leaf]
        assert sum(plus[i] for i in ids) == sum(minus[i] for i in ids)
        assert ids == [i for i,x in enumerate(POINTS) if all(x[j] == v for j,v in leaf)]
    return {'query_span_dimensions':layers, 'cylinders_by_order':cylinder_counts,
            'proper_cylinders_checked':sum(cylinder_counts[:-1]),
            'positive_pair_minimum_mass':str(min(plus+minus)),
            'source_total_variation':str(tv(plus,minus)),
            'old_loader_first_digit_signed_contrast':delta,
            'old_loader_first_digit_plus':list(map(str,p)),
            'old_loader_first_digit_minus':list(map(str,q)),
            'first_digit_total_variation':str(tv(p,q)),
            'depth_three_source_recovery_error_lower_bound':str(tv(plus,minus)/2),
            'depth_three_first_digit_error_lower_bound':str(tv(p,q)/2),
            'adaptive_fixture_leaves':len(leaves)}


def original_step(q, digit):
    kind,b = q
    if kind == 'S': return 'WG2',digit
    if kind.startswith('W'): return {'WF':'F','WG1':'G','WG2':'WG1'}[kind],b
    if kind == 'H': return q
    d = (digit-b)%5
    if kind == 'G':
        return [('WF',b),('WG2',(b+2)%5),('H',5*((b+1)%5)+3),
                ('H',5*((b+1)%5)+4),('WG2',(b+2)%5)][d]
    return [('WF',(b-2)%5),('H',5*b+2),('H',5*((b+2)%5)),
            ('H',5*((b+2)%5)+1),('H',5*b)][d]


def run_original(x):
    q,pos,reads,waits,trace = ('S',0),x,0,0,[]
    for _ in range(30):
        trace.append(q)
        if q[0] == 'H':
            assert q[1] == x
            return trace,reads,waits
        if q[0].startswith('W'):
            pos=(pos+1)%25
            waits+=1
            q=original_step(q,0)
        else:
            reads+=1
            q=original_step(q,pos//5)
    raise AssertionError('Original controller failed to terminate.')


def reference_successor(digit):
    assert 0 <= digit < 5
    if digit >= 3:  # Complete the two physically unused dial-read slots.
        return 'Done', 0
    return ('Wrap',digit,25-5*digit) if digit else ('Qa',0)


def run_loader(source):
    # Actual finite-control simulation. W-state counts each forward unit wait;
    # no source-dependent write or free reverse step is used after the reset.
    a,b,c,d=source
    q,pos,queries,reads,waits,trace=('Qb',),0,0,0,0,[]
    for _ in range(70):
        trace.append((q,pos))
        stage=q[0]
        if stage=='Done': return pos,q[1],queries,reads,waits,trace
        if stage=='Qb':
            queries+=1; q=('Wb',4*b) if b else ('Qc',)
        elif stage=='Qc':
            queries+=1; q=('Wc',2*c) if c else ('Qd',)
        elif stage=='Qd':
            queries+=1; q=('Wd',1) if d else ('Ref',)
        elif stage=='Ref':
            reads+=1; r=pos//5
            assert r<3
            q=reference_successor(r)
        elif stage=='Qa':
            queries+=1; r=q[1]
            q=('Wa',r,5*a) if a else ('Done',r)
        else:
            pos=(pos+1)%25; waits+=1
            if stage in ('Wb','Wc','Wd'):
                q=(stage,q[1]-1) if q[1]>1 else ({'Wb':'Qc','Wc':'Qd','Wd':'Ref'}[stage],)
            elif stage=='Wrap': q=(stage,q[1],q[2]-1) if q[2]>1 else ('Qa',q[1])
            elif stage=='Wa': q=(stage,q[1],q[2]-1) if q[2]>1 else ('Done',q[1])
            else: raise AssertionError('Unknown loader state.')
    raise AssertionError('Loader failed to terminate.')


def priced_bridge():
    codes, loader_states, controller_pairs, costs=set(),set(),set(),[]
    assert reference_successor(3) == reference_successor(4) == ('Done',0)
    def decode(x,r):
        j=5*r+x%5
        return x//5, j if j<12 else 0
    runs=[run_original(x) for x in range(25)]
    def rotate(q):
        kind,b=q
        return q if kind=='S' else (kind,(b+(5 if kind=='H' else 1))%(25 if kind=='H' else 5))
    for source in POINTS:
        a,b,c,d=source; j=4*b+2*c+d
        x,r,nquery,nread,nwait,lt=run_loader(source)
        assert (x,r)==(5*a+j%5,j//5)
        assert nquery==4 and nread==1
        assert nwait==5*a+j%5+25*int(j>=5)
        trace,reads,waits=runs[x]
        assert decode(trace[-1][1],r)==(a,j)
        codes.add((x,r)); loader_states.update(q for q,_ in lt if q[0]!='Done')
        controller_pairs.update((q,r) for q in trace)
        assert runs[(x+5)%25][0]==[rotate(q) for q in trace]
        costs.append((nquery,nread,reads,nwait,waits,nwait+waits))
    assert len(codes)==60 and len(loader_states)==113
    for x,r in product(range(25),range(3)):
        a,j=decode(x,r)
        assert 0<=a<5 and 0<=j<12
        assert decode((x+5)%25,r)==((a+1)%5,j)
    # Terminal decoder extends to all75 labels. Fifteen invalid labels map to
    # (x//5,0); covariance holds even there.
    assert max(t[3] for t in costs)==49
    assert max(t[2] for t in costs)==4 and max(t[4] for t in costs)==6
    return {'source_configurations':60,'dial_inputs':25,'external_record_labels':3,
            'used_terminal_pairs':len(codes),'total_terminal_pairs':75,
            'controller_record_product_states':153,
            'physically_reachable_controller_record_pairs':len(controller_pairs),
            'reachable_preparation_control_states_excluding_handoff':len(loader_states),
            'combined_control_table_states':113+153,
            'physically_reachable_combined_control_states':113+len(controller_pairs),
            'loader_state_kinds':dict(sorted(Counter(q[0] for q in loader_states).items())),
            'physically_unused_preparation_read_slots_completed':2,
            'source_queries_on_every_path':4,'dial_reads_in_preparation':1,
            'maximum_dial_reads_after_preparation':4,'maximum_total_dial_reads':max(t[1]+t[2] for t in costs),
            'maximum_preparation_unit_waits':49,'maximum_controller_unit_waits':6,
            'maximum_total_unit_waits':max(t[5] for t in costs),
            'cost_vectors':sorted(set(costs)),
            'scope':'Requires one reset to dial0, persistent source coordinate queries, and additional finite control. Three record labels are optimal only when the final output is the old25 halt labels plus a fixed record. Loading paths are not asserted rotation-covariant.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result={'arithmetic':'exact integers and fractions','source_queries':cylinders_and_pair(),
            'priced_bridge':priced_bridge(),
            'scope':'No original-source query authorization, global controller optimum, or full operational equivalence is claimed.'}
    data=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output: args.output.write_text(data,encoding='utf-8')
    else: print(data,end='')


if __name__=='__main__': main()
