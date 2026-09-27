#!/usr/bin/env python3
"""Exact AP fixtures; no listed family is asserted to be a whole cover.

Checks the ordered-rescue arithmetic and actual relative-private points,
including a full-prefix failure case. Each active parent's needed exponent
inequality is checked explicitly; arbitrary synchronized tuples are not
asserted to have greedy chronology. No list is asserted to give complete
tail coverage or an extremal odd cover.
"""
from math import gcd,lcm
import json


def check(ok,message):
    if not ok:
        raise ArithmeticError(message)


def member(y,ap):return (y-ap[0])%ap[1]==0


def fixture(name,p,source,children,parent_index,base_x,tail,private_witness,expected_active):
    check(len({d for a,d in source})==len(source),'repeated source modulus')
    check(all(d>1 and d%2 for a,d in source),'invalid odd nonunit AP')
    parents=[];contractions=[];metadata=[]
    for child in children:
        a,d=child
        check(child in source,'child is not an original listed AP')
        q=d//p
        parent=next(ap for ap in source if ap[1]==q)
        parents.append(parent);contractions.append((a%q,q))
        e=0;m=d
        while m%p==0:e+=1;m//=p
        root=a%p
        check(a%p**e==(root+p*tail)%p**e and a%m==base_x%m,
              'selected child misses the common base')
        metadata.append((e,m,root))
    check(len({m for e,m,r in metadata})==p-1,'cofactor colors are not distinct')
    check({r for e,m,r in metadata}==set(range(1,p)),'missing nonzero root')
    check(len(set([q for a,q in parents]+[d for a,d in children]))==2*(p-1),
          'parent-child modulus pairs collide')
    for parent,child,B in zip(parents,children,contractions):
        check((parent[0]-B[0])%parent[1]!=0,'parent not disjoint from its contraction')
        check(child[1]%B[1]==0 and member(child[0],B),'contraction does not contain child')
    chronology_checks=[]
    for i,(candidate,(ei,mi,ri)) in enumerate(zip(parents,metadata)):
        hi=ei-1
        if hi==0:
            continue
        si=candidate[0]%p
        candidate_active=candidate[0]%mi==base_x%mi and \
                         candidate[0]%p**hi==(si+p*tail)%p**hi
        if not candidate_active:
            continue
        check(si!=0 and si!=ri,'active parent does not have a different nonzero root')
        j=next(j for j,(ej,mj,rj) in enumerate(metadata) if rj==si)
        hj=metadata[j][0]-1
        check(hj<=hi-1,'active-parent exponent premise PR2 failed')
        chronology_checks.append(dict(parent_index=i,parent_root=si,
            selected_index_on_parent_root=j,child_depth=hi,earlier_selected_depth=hj,
            verified_exponent_inequality='h_j <= h_i - 1'))
    parent=parents[parent_index];e,m,root=metadata[parent_index]
    f=e-1
    parent_root=parent[0]%p if f else None
    active=f>=1 and parent[0]%m==base_x%m and \
           parent[0]%p**f==(parent_root+p*tail)%p**f
    check(active==expected_active,'incorrect full-prefix activity')
    period=lcm(*(d for a,d in source))
    old_parent_points=range(parent[0]%parent[1],period,parent[1])
    private=[];intersection_counts=[0]*len(children);private_rescues=[0]*len(children)
    containment_counts=[0]*len(children)
    for y in old_parent_points:
        own_private=not any(ap!=parent and member(y,ap) for ap in source)
        if own_private:private.append(y)
        for j,(child,B) in enumerate(zip(children,contractions)):
            if member(y,B):
                intersection_counts[j]+=1
                if own_private:private_rescues[j]+=1
                if member(y,child):containment_counts[j]+=1
    check(private_witness%period in private,'stated private witness is not private in listed family')
    if active:
        for j,(ej,mj,rj) in enumerate(metadata):
            expected=ej==1 or rj==parent_root
            check(bool(intersection_counts[j])==expected,'active-parent AP intersection iff failed')
            if ej>=2 or rj==parent_root:
                check(containment_counts[j]==intersection_counts[j],
                      'purported deep rescue is not already original-child coverage')
                check(private_rescues[j]==0,'active parent has a forbidden private rescuer')
    return dict(name=name,p=p,full_period=period,whole_cover_claim=False,
                complete_tail_cover_claim=False,extremality_claim=False,
                greedy_origin_claim=False,active_parent_exponent_checks=chronology_checks,
                parent=list(parent),parent_active_at_common_base=active,
                listed_family_private_count=len(private),private_witness=private_witness,
                full_parent_points_checked=period//parent[1],
                AP_intersection_counts=intersection_counts,
                original_child_containment_counts=containment_counts,
                actual_relative_private_rescue_counts=private_rescues,
                witness_rescuers=[j for j,B in enumerate(contractions) if member(private_witness,B)])


def result():
    source3=[(0,3),(11,15),(58,63),(22,45),(86,189)]
    children3=[(22,45),(86,189)]
    a=fixture('active parent, no shallow selected child',3,source3,children3,1,2,1,58,True)
    check(a['witness_rescuers']==[],'active-parent blocker was rescued')
    source3bad=[(0,3),(11,15),(16,63),(22,45),(86,189)]
    b=fixture('same first root, different higher prefix',3,source3bad,children3,1,2,1,142,False)
    check(b['witness_rescuers']==[0],'full-prefix countercheck did not expose a deep rescue')
    source5=[(0,5),(0,7),(0,11),(2,15),(22,35),(23,55),(31,75),(131,325),(1509,1625)]
    children5=[(31,75),(22,35),(23,55),(1509,1625)]
    c=fixture('active parent rescued only by other-root shallow contractions',5,source5,children5,3,1,1,5006,True)
    check(c['witness_rescuers']==[1,2],'allowed shallow private rescue changed')
    return dict(success=True,fixtures=[a,b,c],
                scope='Exact AP intersections, explicit active-parent exponent inequalities, and private points relative to finite AP lists. No list is asserted to cover all tails or all integers, to arise from the greedy construction, or to satisfy global extremality. These fixtures check arithmetic, not existence or nonexistence of odd covers.')


if __name__=='__main__':print(json.dumps(result(),sort_keys=True,indent=2))
