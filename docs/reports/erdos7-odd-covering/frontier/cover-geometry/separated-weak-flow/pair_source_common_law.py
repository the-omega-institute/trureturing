#!/usr/bin/env python3
"""Construct a common original-label law for four roots, three pair-children each.
Standard library only. All checks remain active under python -O.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from math import lcm
import json

LABELS=(1,5,25,7,35,175)

def require(ok,message):
    if not ok:raise ValueError(message)

def construct_common_law(rows,root_digits=(1,2,3,4),child_digits=None):
    require(len(rows)==4,'four source roots')
    require(len(root_digits)==4 and len(set(root_digits))==4 and all(type(r)is int and 0<=r<5 for r in root_digits),'four distinct actual root digits')
    if child_digits is None:child_digits=((0,1,2),)*4
    require(len(child_digits)==4,'one actual child record per root')
    normalized=[]
    for row,digits in zip(rows,child_digits):
        require(len(row)==3,'three active children per root')
        require(len(digits)==3 and len(set(digits))==3 and all(type(a)is int and 0<=a<5 for a in digits),'three distinct actual child digits')
        pairs=[]
        for pair in row:
            require(len(pair)==2 and len(set(pair))==2 and all(type(y)is int and 0<=y<7 for y in pair),'two distinct actual seven columns per child')
            pairs.append(tuple(sorted(pair)))
        normalized.append(tuple(pairs))
    rows=tuple(normalized)
    require(all(set(rows[r]).isdisjoint(rows[s]) for r,s in combinations(range(4),2)),'distinct unordered pair sets must be disjoint across roots')
    degree=Counter(y for row in rows for pair in row for y in pair)
    delta=max(degree.values());center=max(degree,key=lambda y:(degree[y],-y))
    weights={}
    if delta<=8:
        mode='uniform';q=2;k=h=1;exception=1
    else:
        k,h,exception=(4,6,5) if delta>=10 else (9,11,10)
        q=k+h;mode='heavy' if delta>=10 else 'degree_nine'
        exception_count=2 if delta>=10 else 3
        center_degree_cap=12 if delta>=10 else 9
        require(q==2*exception and 0<k<=h,'positive balanced leaf mass')
        require(sum(center not in pair for row in rows for pair in row)<=exception_count,'at most three exception children')
        require(sum(d>=9 for d in degree.values())==1,'the heavy column is unique')
        for y in degree:
            if y!=center:
                require(sum((min(center,y),max(center,y)) in row for row in rows)<=1,'each spoke endpoint belongs to at most one root')
    for r,row,digits in zip(root_digits,rows,child_digits):
        for a,pair in zip(digits,row):
            for y in pair:
                weights[r,a,y]=1 if mode=='uniform' else k if y==center else h if center in pair else exception
    denominator=12*q
    require(len(weights)==24 and all(w>0 for w in weights.values()),'one positive supported mass at each of 24 original points')
    require(sum(weights.values())==denominator,'total mass')
    roots=Counter();leaves=Counter();columns=Counter();root_columns=Counter()
    for (r,a,y),w in weights.items():
        roots[r]+=w;leaves[r,a]+=w;columns[y]+=w;root_columns[r,y]+=w
    require(set(roots.values())=={3*q} and set(leaves.values())=={q},'simultaneous exact root and leaf masses')
    if mode=='uniform':
        require(max(columns.values())<=8 and max(root_columns.values())<=3 and max(weights.values())==1,'uniform simultaneous cell caps')
        coefficients=Counter(lcm(m,n) for m,n in product(LABELS,repeat=2))
        require(coefficients=={1:1,5:3,25:5,7:3,35:9,175:15},'all 36 ordered original-label intersections')
        bound=F(24+3*6+5*2+3*8+9*3+15,24)
        cases=None
    else:
        for y in range(7):
            center_col=y==center
            require(columns[y]<=(center_degree_cap*k if center_col else 3*h+exception_count*exception),'common seven-column mass cap')
            for r in root_digits:
                require(root_columns[r,y]<=(3*k if center_col else 3*h),'root-column mass cap')
            require(all(w<=(k if center_col else h) for (r,a,z),w in weights.items() if z==y),'point mass cap in a fixed column')
        # The global phase b is shared across all roots; d is the independent 35-column phase.
        # If b != d, their two indicators cannot both be one, so the final point increment is at most 9h.
        cases=({
            'b=d=center':37*q+56*k,
            'b=center,d=private':52*q+18*k,
            'b=private,d=center':55*q-9*k,
            'b=d=private':80*q-51*k,
            'b,d=distinct_private':72*q-43*k,
        } if delta>=10 else {
            'b=d=center':37*q+47*k,
            'b=center,d=private':52*q+9*k,
            'b=private,d=center':113*q//2-9*k,
            'b=d=private':163*q//2-51*k,
            'b,d=distinct_private':147*q//2-43*k,
        })
        for (bc,dc,equal),expected in zip(((True,True,True),(True,False,False),(False,True,False),(False,False,True),(False,False,False)),cases.values()):
            Cb=center_degree_cap*k if bc else 3*h+exception_count*exception
            Db=3*k if bc else 3*h;Dd=3*k if dc else 3*h
            Mb=k if bc else h;Md=k if dc else h
            expanded=26*q+3*Cb+5*Dd+2*Db+2*Mb+2*Md+2*equal*Dd+(11 if equal else 9)*h
            require(expanded==expected,'five-case expansion including the last original point label')
        bound=F(max(cases.values()),denominator)
    expected={'uniform':F(59,12),'degree_nine':F(1171,240),'heavy':F(149,30)}[mode]
    require(bound==expected<F(46,9),'general full-phase bound for the selected law')
    return dict(rows=rows,root_digits=root_digits,child_digits=child_digits,weights=weights,denominator=denominator,mode=mode,heavy_column=center if mode!='uniform' else None,max_degree=delta,bound=bound,cases=cases)

def crt(x,m,y):
    out=x+m*(((y-x)*pow(m,-1,7))%7)
    require(out%m==x and out%7==y,'literal CRT map')
    return out

def exact_gamma(law):
    """Independent finite phase audit for fixtures; not the proof of the general bound."""
    points_by_root={r:tuple((a,y,w) for (u,a,y),w in law['weights'].items() if u==r) for r in law['root_digits']}
    local={};local_checks=0
    for r,points in points_by_root.items():
        leaves=sorted({a for a,y,w in points});cols=sorted({y for a,y,w in points});atoms=[(a,y) for a,y,w in points]
        for b in range(7):
            for mask in range(16):
                p,m,e,f=(bool(mask&(1<<j)) for j in range(4))
                best=(-1,None)
                for d,a,(v,z) in product(cols if m else (None,),leaves if e else (None,),atoms if f else ((None,None),)):
                    cost=sum(w*(1+p+(y==b)+(m and y==d)+(e and child==a)+(f and (child,y)==(v,z)))**2 for child,y,w in points)
                    if cost>best[0]:best=(cost,(d,a,v,z))
                    local_checks+=1
                local[r,b,mask]=best
    best=(-1,None);outer_checks=0
    for alloc in product(law['root_digits'],repeat=4):
        masks={r:sum(1<<j for j in range(4) if alloc[j]==r) for r in law['root_digits']}
        for b in range(7):
            cost=sum(local[r,b,masks[r]][0] for r in law['root_digits'])
            if cost>best[0]:best=(cost,(alloc,b,masks))
            outer_checks+=1
    alloc,b,masks=best[1]
    d=local[alloc[1],b,masks[alloc[1]]][1][0]
    a=local[alloc[2],b,masks[alloc[2]]][1][1]
    v,z=local[alloc[3],b,masks[alloc[3]]][1][2:]
    phases=(0,alloc[0],alloc[2]+5*a,b,crt(alloc[1],5,d),crt(alloc[3]+5*v,25,z))
    literal=sum(w*sum(crt(r+5*a,25,y)%m==phase for m,phase in zip(LABELS,phases))**2 for (r,a,y),w in law['weights'].items())
    require(literal==best[0],'attaining separated layout equals all six literal original phases')
    value=F(best[0],law['denominator'])
    require(value<=law['bound'],'independent complete phase maximum respects the general theorem')
    return dict(exact_gamma=str(value),attaining_phases=phases,local_phase_checks=local_checks,common_phase_root_assignments=outer_checks)

FIXTURES={
 'low_degree_attains_uniform_bound':(((0,1),)*3,((0,2),)*3,((0,3),(0,3),(1,4)),((1,5),(2,4),(3,5))),
 'degree_nine_attains_bound':(((0,1),)*3,((0,2),)*3,((0,3),(0,3),(1,4)),((0,4),(1,5),(1,5))),
 'twelve_center_children':(((0,1),)*3,((0,2),)*3,((0,3),)*3,((0,4),)*3),
 'one_exception':(((0,1),(0,1),(2,3)),((0,2),)*3,((0,3),)*3,((0,4),)*3),
 'proper_cut_source':(((0,1),)*3,((0,2),(0,3),(0,2)),((0,4),(0,4),(1,4)),((0,5),(0,5),(1,5))),
 'heavy_private_attains_bound':(((0,1),)*3,((0,2),)*3,((0,3),(0,3),(1,4)),((0,4),(0,4),(1,5))),
}

def main():
    results=[]
    for name,rows in FIXTURES.items():
        law=construct_common_law(rows)
        checked=exact_gamma(law)
        if 'attains' in name:require(F(checked['exact_gamma'])==law['bound'],'attaining control is sharp for its prescribed law')
        results.append(dict(name=name,rows=rows,mode=law['mode'],max_degree=law['max_degree'],denominator=law['denominator'],general_bound=str(law['bound']),cases=law['cases'],**checked))
    # Reject a genuinely disallowed cross-root reuse of a pair.
    bad=(((0,1),)*3,((0,1),)*3,((0,3),)*3,((0,4),)*3)
    rejected=False
    try:construct_common_law(bad)
    except ValueError:rejected=True
    require(rejected,'cross-root repeated pair is rejected')
    C=F(149,30);B5=1+2*F(1,4)/3+F(3,8)/9;lam=(C-1)/32
    require(B5==F(29,24) and lam==F(119,960),'Chapter09 parameters for initial five height two')
    lift=(C*B5-lam)/(1-lam)
    require(lift==F(16927,2523)<9,'conditional correctly aligned five-height arithmetic')
    print(json.dumps(dict(conditional_height_scope='Requires the actual distinct-label residual and provenance hypotheses of Chapter09 at Q0=175; five extension only',conditional_five_height_bound=str(lift),universal_bound='149/30',target='46/9',heavy_rule='center 4, private endpoint 6, exception endpoints 5 each; total 120',heavy_bound='149/30',degree_nine_rule='center 9, private endpoint 11, exception endpoints 10 each; total 240',degree_nine_bound='1171/240',low_degree_bound='59/12',fixtures=results,invalid_cross_root_pair_rejected=rejected),indent=2))
if __name__=='__main__':main()
