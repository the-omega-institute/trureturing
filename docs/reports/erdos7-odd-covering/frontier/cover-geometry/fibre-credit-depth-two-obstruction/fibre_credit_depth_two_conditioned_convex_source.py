#!/usr/bin/env python3
"""A common upper-tail ICX comparator for the existing shallow mu23 source.

The pinned old head geometry and actual retention theorem are inherited
premises. This exact consumer reconstructs their full comparator transport.
"""
import argparse
from collections import defaultdict
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import lcm,prod
from pathlib import Path
import json


def need(ok,message):
    if not ok:
        raise RuntimeError(message)


def pinned(path,expected):
    raw=path.read_bytes()
    need(sha256(raw).hexdigest()==expected,'pinned inherited source: '+str(path))
    return json.loads(raw)


def calculate(head_certificate=None,retention_certificate=None):
    directory=Path(__file__).resolve().parent
    report_root=directory.parents[2]
    if head_certificate is None:
        head_certificate=report_root/'certificates/marked_head_profile_certificate.parts/content/012-deletion_weighted_comparison.json'
    if retention_certificate is None:
        retention_certificate=directory/'fibre_credit_depth_two_uniform_shallow.json'
    head_sha='603a91b3d6f91d59b835deb9e0f0a8bd26148852f4e038dbacea6e5423634a5c'
    retention_sha='afc7b9a8167cf22e67885e427c865c5daa844eb3664b6ff7b684be56e3168591'
    head=pinned(head_certificate,head_sha)
    retention=pinned(retention_certificate,retention_sha)
    X={int(x):F(p) for x,p in head['auxiliary_atoms'].items()}
    need(tuple(sorted(X))==(1,2,3,4,5,6,8,12) and sum(X.values())==1 and min(X.values())>0,
         'the established eight-atom head comparison law')
    need(sum(x*p for x,p in X.items())==F(271,86),'head mean consistency')
    for knot,bound in head['hinge_knots'].items():
        need(sum((p*max(x-int(knot),0) for x,p in X.items()),F(0))==F(bound),
             'source law reproduces every inherited full-profile hinge knot')
    source_rows=retention['square_moment29_extension']['rows']
    shapes=('root1_same_other_column','root1_other_same_column','root1_other_other_column',
            'root2_same_other_column','root2_other_same_column','root2_other_other_column')
    need(tuple(row['shape'] for row in source_rows)==shapes,'all six inherited actual source shapes')
    deltas=tuple(F(row['mass23_lower']) for row in source_rows)
    need(deltas==(F(1243487,13077504),F(7609619,64627200),F(7609619,64627200),
                  F(39317,253440),F(123881,887040),F(123881,887040)),
         'same-source retained masses through23')
    delta=min(deltas)
    primes=(11,13,17,19,23)
    Z=defaultdict(F)
    raw_terms=0
    for outcomes in product((0,1),repeat=5):
        chance=prod((F(1,p-1) if doubled else F(p-2,p-1)
                     for p,doubled in zip(primes,outcomes)),start=F(1))
        multiplier=2**sum(outcomes)
        for x,probability in X.items():
            Z[x*multiplier]+=chance*probability
            raw_terms+=1
    need(raw_terms==256 and len(Z)==23 and sum(Z.values())==1,
         'one exact 23-atom product comparator from all256 source outcomes')
    threshold=8
    tail=sum((p for x,p in Z.items() if x>threshold),F(0))
    tail_closed=sum((p for x,p in Z.items() if x>=threshold),F(0))
    need(tail<=delta<=tail_closed,'threshold8 splits one atom at the retained upper-tail mass')
    Y={x:p/delta for x,p in Z.items() if x>threshold}
    Y[threshold]=1-tail/delta
    need(len(Y)==17 and min(Y.values())>0 and sum(Y.values())==1,'one common normalized 17-atom upper-tail law')
    common_den=lcm(*(p.denominator for p in Y.values()))
    need(common_den==242237485035,'compact exact denominator of the final common law')
    numerators={x:int(p*common_den) for x,p in Y.items()}
    need(sum(numerators.values())==common_den,'all displayed comparison probabilities sum to one')

    moments=[]
    for k in range(1,5):
        direct=sum((p*x**k for x,p in Y.items()),F(0))
        clipped=F(threshold**k)+sum((p*max(x**k-threshold**k,0) for x,p in Z.items()),F(0))/delta
        need(direct==clipped,'moments of the single law equal the clipped-source formula')
        moments.append(direct)
    expected=(F(354870451028,26915276115),F(1940069387744,8971758705),
              F(31390970044192,6211217565),F(1089423903671104,5383055223))
    need(tuple(moments)==expected,'four fixed independently checked exact moments')
    old=(F(19),F(2607189975,7283281),F(906617738995,159166336))
    need(all(new<previous for new,previous in zip(moments[:3],old)),
         'all first-three moments strictly improve the same-source prior bounds')
    shape_fourth=F(4005807477705,19895792)
    need(shape_fourth<moments[3],'the separate same-source shape-specific D2 fourth bound remains stronger')
    hinges=[]
    for t in range(max(Y)+1):
        h=lambda x:max(x-t,0)
        at_cut=h(threshold)
        direct=sum((p*h(x) for x,p in Y.items()),F(0))
        clipped=F(at_cut)+sum((p*max(h(x)-at_cut,0) for x,p in Z.items()),F(0))/delta
        need(direct==clipped,'every integer hinge agrees with the one common upper-tail law')
        hinges.append(direct)
    # A constant selected load17 met the old first-four scalar ceilings, but
    # its first two moments exceed the new caps. No arithmetic realization.
    negative_control=(F(17),F(289),F(4913),F(83521))
    need(all(a<b for a,b in zip(negative_control,old+(shape_fourth,))),
         'finite scalar control passed the preceding moment-only interface')
    need(negative_control[0]>moments[0] and negative_control[1]>moments[1],
         'the same finite scalar control is rejected by the new mean and square')

    out=dict(scope='A single common increasing-convex comparator on the existing actual shallow mu23 source. '
                   'The head geometry, full ICX theorem and actual retention theorem are inherited; '
                   'no new Lean verification or five-direction positivity conclusion.',
             head_source_sha256=head_sha,retention_source_sha256=retention_sha,
             source_geometry_reexecuted=False,complete_ICX_source_theorem_reproved=False,
             actual_source_changed=False,primes=primes,shape_retention_lower_bounds=list(map(str,deltas)),
             common_retention_lower=str(delta),source_outcomes_checked=raw_terms,
             X=[dict(value=x,probability=str(X[x])) for x in sorted(X)],
             Z=[dict(value=x,probability=str(Z[x])) for x in sorted(Z)],
             threshold=threshold,tail_mass_strictly_above=str(tail),tail_mass_at_least=str(tail_closed),
             Y_probability_denominator=common_den,
             Y=[dict(value=x,probability_numerator=numerators[x],probability=str(Y[x])) for x in sorted(Y)],
             common_Y_moments_one_through_four=list(map(str,moments)),
             common_Y_moments_decimal=list(map(float,moments)),
             stronger_same_source_D2_fourth=str(shape_fourth),
             combined_first_four_caps=list(map(str,tuple(moments[:3])+(shape_fourth,))),
             hinge_thresholds_checked=len(hinges),
             scalar_negative_control=dict(load='17',moments=list(map(str,negative_control)),
                                          rejected_by=['mean','square'],
                                          scope='Selected scalar model only, no congruence realization.'),
             exact_checks_passed=True)
    return out


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--head-certificate',type=Path)
    parser.add_argument('--retention-certificate',type=Path)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result=json.loads(json.dumps(calculate(args.head_certificate,args.retention_certificate)))
    rendered=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output is None:
        need(json.loads(Path(__file__).resolve().with_suffix('.json').read_text())==result,
             'retained result agrees with complete conditioned-convex source arithmetic')
        print(rendered,end='')
    else:
        args.output.write_text(rendered)


if __name__=='__main__':
    main()
