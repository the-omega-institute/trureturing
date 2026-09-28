#!/usr/bin/env python3
"""Four public-plus-private singleton fibres with an arbitrary full fifth.

Self-contained actual-source construction. Reads no files, writes --output.
No source deletion, minimum-cut or exhaustive-source claim.
"""
import argparse
from collections import Counter, defaultdict
from fractions import Fraction as Q
from itertools import combinations, product
from pathlib import Path
import json

N=(4,5,5,5)
SEL=(2,3,3,3)
D=(1,5,7,25,35,49,175,245,1225)
W=Q(495,647)
P5=tuple(map(Q,('1','1/3','3/5','1/5','1/5','1/5','3/25','1/15','1/25')))


def check(value,message):
    if not value: raise RuntimeError(message)


def tree(labels,b,l):
    return sum(n>=l for n in Counter(g for g,h in labels).values())>=b


def crt(p):
    r,c,g,h=p
    a,b=r+5*c,g+7*h
    out=(a+25*((2*(b-a))%49))%1225
    check(out%25==a and out%49==b,'original CRT')
    return out


def mix(terms):
    out=defaultdict(Q)
    for w,law in terms:
        for p,m in law.items():out[p]+=w*m
    return dict(out)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    y=(0,0)
    z=((0,1),(1,0),(1,1),(0,2))
    source={(1,c):frozenset((y,z[c])) for c in range(4)}
    source[1,4]=frozenset(product(range(7),repeat=2))
    outer={0:(2,3),2:(2,4),3:(3,4)}
    for i,(r,cols) in enumerate(outer.items()):
        f=frozenset({(g,h) for g in cols for h in range(5)}|
                    {(0,1),(1,0),(0,3+i),(1,3+i)})
        check(len(f)==14,'complete other-root fibre')
        for c in range(N[r]):source[r,c]=f
    check(len(source)==19 and len(source[1,4])==49 and sum(map(len,source.values()))==253,
          'unchanged19owner253point source and arbitrary fifth')
    choices={r:list(combinations(range(N[r]),SEL[r])) for r in range(4)}
    projections={r:[frozenset().union(*(source[r,c] for c in cs)) for cs in choices[r]] for r in range(4)}
    pairs=0
    for r,s in combinations(range(4),2):
        for a,b in product(projections[r],projections[s]):
            check(tree(a|b,3,3),'original complete legal pair premise');pairs+=1
    check(pairs==480 and tree(frozenset().union(*source.values()),5,5),'all pairs and standalone')
    check(all(not all(tree(f,3,3) for f in projections[r]) for r in range(4)),'no individually robust root')
    anchor=(1,2,3)
    F=frozenset().union(*(source[1,c] for c in anchor))
    check(F==frozenset((y,z[1],z[2],z[3])) and len(F)==4,'complete legal four-label anchor')
    eta={(1,0,*y):Q(1,4),**{(1,c,*z[c]):Q(1,4) for c in anchor}}
    check(len(eta)==4 and len({c for r,c,g,h in eta})==4,'sameF four distinct actual owners')
    psi=defaultdict(Q);trees=0
    for i,(r,cols) in enumerate(outer.items()):
        for j,cs in enumerate(choices[r]):
            actual=F|frozenset().union(*(source[r,c] for c in cs))
            branches=(0,1,cols[j%2]);t=set()
            for g in branches:
                required={a for a in F if a[0]==g}
                other=sorted(a for a in actual-required if a[0]==g)
                part=required|set(other[:3-len(required)])
                check(len(part)==3 and required<=part<=actual,'wholeF normalized actual branch')
                t.update(part)
            survivors=t-F
            check(tree(t,3,3) and len(survivors)==5,'actual five-survivor puncture')
            owner=cs[j%len(cs)]
            check(survivors<=source[r,owner],'actual original owner lift')
            for g,h in survivors:psi[r,owner,g,h]+=Q(1,3*len(choices[r])*5)
            trees+=1
    psi=dict(psi)
    laws={'psi':psi,'eta':eta,'lambda':mix([(W,psi)]),'pi':mix([(1-W,eta)])}
    laws['nu']=mix([(Q(1),laws['lambda']),(Q(1),laws['pi'])])
    check(trees==26 and sum(psi.values())==1,'all26 original other restrictions')
    check(all((g,h) not in F and r!=1 for r,c,g,h in psi),'global completeF fine exclusion')
    caps={};cylinders=0
    for name,law in laws.items():
        check(all(m>0 and (g,h) in source[r,c] for (r,c,g,h),m in law.items()),'unchanged actual source support')
        target=W if name=='lambda' else 1-W if name=='pi' else Q(1)
        check(sum(law.values())==target,'one fixed law mass')
        cs=[]
        for d in D:
            values=[Q(0)]*d
            for p,m in law.items():values[crt(p)%d]+=m
            cs.append(max(values));cylinders+=d
        caps[name]=cs
    check(all(a<=b for a,b in zip(caps['psi'],P5)),'complete puncture cap table')
    check(all(a<=W*b for a,b in zip(caps['lambda'],P5)),'scaled same-law puncture caps')
    pi_caps=(1-W,1-W,3*(1-W)/4,(1-W)/4,3*(1-W)/4,(1-W)/4,(1-W)/4,(1-W)/4,(1-W)/4)
    check(all(a<=b for a,b in zip(caps['pi'],pi_caps)),'actual four-owner eta caps')
    check(caps['nu'][2]<=3*W/5 and caps['nu'][5]<=W/5,'same-law pure7/49 caps')
    for g in range(7):
        check(sum(m for (r,c,gg,h),m in psi.items() if gg==g)<=Q(3-sum(gg==g for gg,h in F),5),
              'normalized original column deletion cap')
    check(cylinders==8835,'five law slots times1767 numerical cylinders')
    result=dict(status='PASS',actual_points=253,original_owners=19,original_pair_checks=pairs,
                paired_tree_constructions=trees,numerical_law_slot_cylinders=cylinders,
                arbitrary_fifth_fibre_size=49,anchor=anchor,four_owner_representatives=list(eta),
                no_individually_robust_root=True,standalone=True,
                query_bound_from_existing_F12222_2_certificate='5795/647',
                caps={name:list(map(str,c)) for name,c in caps.items()},
                source=[dict(root=r,child=c,whole_fibre=sorted(f)) for (r,c),f in sorted(source.items())],
                laws={name:[dict(point=p,mass=str(m)) for p,m in sorted(law.items())] for name,law in laws.items()},
                scope='Actual control of four complete public-plus-private fibres and arbitrary fifth. No minimum-cut or Lean claim.')
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('status','actual_points','original_pair_checks','paired_tree_constructions','numerical_law_slot_cylinders','arbitrary_fifth_fibre_size')}))


if __name__=='__main__':main()
