#!/usr/bin/env python3
"""Actual original-AP edge-separator countercontrol; standard library only.

Two K4 bags share primes 3,7. Equal projection sets and scalar summaries
do not determine the joint extension kernel or its subsequent gluing.
This is not a covering-system counterexample or a noncoverage novelty claim.
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from math import prod
from pathlib import Path
import json
import argparse

SOURCE = dict(zip((3,5,7,9,11,15,33,35,45,49,77,245),
                  (0,0,0,2,0,1,1,8,37,2,1,99)))
A = SOURCE | {21:0,55:0,1155:0}
A_SHIFT = A | {45:22}
B_ZERO = {13:0,17:0,39:0,51:0,91:0,119:0,221:0,4641:0}
B = B_ZERO | {97461:1}
BOUNDARY = (3,7)
SIZES = {3:9,5:5,7:49,11:11,13:13,17:17}
V3 = tuple(x for x in range(9) if x%3 and x!=2)
V7 = tuple(y for y in range(49) if y%7 and y!=2)


def factors(d):
    result=[]
    for p in SIZES:
        power=1
        while d%p==0:
            d//=p
            power*=p
        if power>1:
            result.append((p,power))
    assert d==1
    return tuple(result)


def local_kernel(family, private):
    """Enumerate actual prime-power coordinates; test original CRT cylinders."""
    forbidden=[tuple((p,power,a%power) for p,power in factors(d)) for d,a in family.items()]
    matrix=[[0]*49 for _ in range(9)]
    for x,y in product(range(9),range(49)):
        for values in product(*(range(SIZES[p]) for p in private)):
            word=dict(zip(private,values)) | {3:x,7:y}
            if not any(all(word[p]%power==residue for p,power,residue in condition)
                       for condition in forbidden):
                matrix[x][y]+=1
    return matrix


def direct_integer_kernel(family, period):
    """Independent univariate sieve over the complete original period."""
    surviving=bytearray(b'\x01')*period
    for d,a in family.items():
        assert d>1 and d%2 and 0<=a<d and period%d==0
        count=(period-1-a)//d+1
        surviving[a::d]=bytes(count)
    matrix=[[0]*49 for _ in range(9)]
    witness=None
    for n,good in enumerate(surviving):
        if good:
            matrix[n%9][n%49]+=1
            if witness is None:
                witness=n
    return matrix,witness


def summary(matrix):
    support=[(x,y) for x,y in product(range(9),range(49)) if matrix[x][y]>0]
    return dict(first_projection=sorted({x for x,y in support}),
                second_projection=sorted({y for x,y in support}),
                support_cardinality=len(support),
                total_extension_count=sum(map(sum,matrix)),
                complete_entry_histogram=dict(sorted(Counter(v for row in matrix for v in row).items())),
                weighted_first_marginal=list(map(sum,matrix)),
                weighted_second_marginal=[sum(matrix[x][y] for x in range(9)) for y in range(49)])


def encode(value):
    if isinstance(value,Fraction):
        return str(value)
    if isinstance(value,dict):
        return {str(k):encode(v) for k,v in value.items()}
    if isinstance(value,(list,tuple)):
        return [encode(v) for v in value]
    return value


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'),
                        help='JSON result path; defaults beside this program')
    args=parser.parse_args()
    if not __debug__:
        raise RuntimeError('Assertions must be enabled.')
    assert V3==(1,4,5,7,8) and len(V7)==41
    assert set(A).isdisjoint(B) and set(A_SHIFT)==set(A)
    assert prod(SIZES.values())==5360355
    kernels={name:local_kernel(family,private)
             for name,family,private in (('A',A,(5,11)),('A_shift',A_SHIFT,(5,11)),
                                         ('B_before',B_ZERO,(13,17)),('B_after',B,(13,17)))}
    for name,family in (('A',A),('A_shift',A_SHIFT)):
        exact,witness=direct_integer_kernel(family,9*49*5*11)
        assert exact==kernels[name]
    for x,y in product(range(9),range(49)):
        assert (kernels['A'][x][y]>0)==(x in V3 and y in V7 and (x,y)!=(1,1))
        assert (kernels['A_shift'][x][y]>0)==(x in V3 and y in V7 and (x,y)!=(4,1))
        shifted_x=4 if x==1 else 1 if x==4 else x
        assert kernels['A_shift'][x][y]==kernels['A'][shifted_x][y]
        assert kernels['B_before'][x][y]==192
        assert kernels['B_after'][x][y]==192-int((x,y)==(1,1))
    assert kernels['A'][1][1]==0 and kernels['A_shift'][1][1]==9
    sa,sb=summary(kernels['A']),summary(kernels['A_shift'])
    scalar_keys=('first_projection','second_projection','support_cardinality',
                 'total_extension_count','complete_entry_histogram')
    assert all(sa[key]==sb[key] for key in scalar_keys)
    assert sa['first_projection']==list(V3) and sa['second_projection']==list(V7)
    assert sa['support_cardinality']==204
    # Full projections are equal. Weighted marginals are not claimed equal.
    assert sa['weighted_first_marginal']!=sb['weighted_first_marginal']
    graph=set()
    for d in A|B:
        graph.update(combinations(sorted(p for p,power in factors(d)),2))
    expected_graph=set(combinations((3,5,7,11),2))|set(combinations((3,7,13,17),2))
    assert graph==expected_graph
    assert len(graph)==11 and len(A|B)==24
    assert all(len(factors(d))==4 for d in (1155,4641,97461))
    full_results=[]
    for name,family in (('A',A),('A_shift',A_SHIFT)):
        before=[[kernels[name][x][y]*kernels['B_before'][x][y] for y in range(49)] for x in range(9)]
        after=[[kernels[name][x][y]*kernels['B_after'][x][y] for y in range(49)] for x in range(9)]
        global_before,witness_before=direct_integer_kernel(family|B_ZERO,5360355)
        global_after,witness_after=direct_integer_kernel(family|B,5360355)
        assert global_before==before and global_after==after
        before_count=sum(map(sum,before));after_count=sum(map(sum,after))
        full_results.append(dict(left_family=name,
                                 original_moduli_count_after=len(family|B),
                                 original_period=5360355,
                                 survivors_before=before_count,survivors_after=after_count,
                                 loss_from_same_added_label=before_count-after_count,
                                 Haar_survival_after=Fraction(after_count,5360355),
                                 actual_uncovered_residue_after=witness_after,
                                 exact_glued_boundary_counts_before=before,
                                 exact_glued_boundary_counts_after=after,
                                 full_original_integer_enumeration_matches=True))
    assert full_results[0]['survivors_before']==full_results[1]['survivors_before']
    assert full_results[0]['loss_from_same_added_label']==0
    assert full_results[1]['loss_from_same_added_label']==9
    assert full_results[0]['survivors_after']-full_results[1]['survivors_after']==9
    data=dict(scope='Actual original AP control against replacing joint separator kernels by projection sets/scalar summaries. Not an AP cover counterexample.',
              original_source_family=SOURCE,
              first_K4_labels=A,first_K4_shifted_labels=A_SHIFT,
              second_K4_labels_before=B_ZERO,second_K4_labels_after=B,
              first_bag=(3,5,7,11),second_bag=(3,7,13,17),separator=(3,7),
              original_coordinate_sizes=SIZES,original_prime_graph_edges=sorted(graph),
              pure_boundary_domains=dict(V3=V3,V7=V7),local_extension_kernels=kernels,
              left_summaries=dict(A=sa,A_shift=sb),equal_summary_fields=scalar_keys,
              distinction='Projection sets, support cardinality, total count and entry histogram agree. Weighted first marginals differ and are explicitly retained, not claimed equal.',
              pointwise_gluing_rule='K_glued(x3,x7)=K_left(x3,x7)*K_right(x3,x7), summed once over the same complete separator coordinates.',
              glued_controls=full_results)
    args.output.write_text(json.dumps(encode(data),separators=(',',':'))+'\n',encoding='utf-8')
    print(json.dumps(encode(dict(left_summary={key:sa[key] for key in scalar_keys},
                                controls=[{k:v for k,v in r.items() if not k.startswith('exact_glued')}
                                          for r in full_results])),indent=2))


if __name__=='__main__':
    main()
