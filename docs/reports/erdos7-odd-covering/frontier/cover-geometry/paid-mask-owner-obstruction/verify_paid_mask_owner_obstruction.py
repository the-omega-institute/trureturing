#!/usr/bin/env python3
"""Construct and check Report860's local AP paid-mask obstruction.

Only the explicit CRT family and finite projection grids are evaluated.
The family is a noncover; no divisor-closed or EB1-minimal realization is
asserted. JSON on stdout contains the reconstructible source and results.
"""

import json
from itertools import combinations, product
from math import gcd, prod, lcm
from fractions import Fraction as F
q=113
internal=(13,17,29)
A=(5,11,19); B=(7,23)
external=tuple(sorted(A+B))
primes=tuple(sorted(internal+external))
m=prod(internal); W=prod(primes); Q=9*q*W

def crt(items):
    r=0; n=1
    for p,a in items:
        if p==1: continue
        r += n*(((a-r)*pow(n,-1,p))%p)
        n*=p; r%=n
    return r

orig=[]
def add(name,terms,private):
    n=prod(p for p,a in terms)
    r=crt(terms)
    orig.append({'name':name,'n':n,'r':r,'private':private})

def point(old=2,digit=50,vals=None):
    d={p:1 for p in primes}
    if vals: d.update(vals)
    return crt([(9,old),(q,digit)]+list(d.items()))

add('guard3',[(3,0)],point(old=0))
add('guard9',[(9,1)],point(old=1))
for p in internal:
    add('guard'+str(p),[(p,0)],point(vals={p:0}))

internal_divs=[prod(ps) for k in range(4) for ps in combinations(internal,k)]
tags=sorted((3**a*d,a,d) for a in range(3) for d in internal_divs)
assert len(tags)==24
for p in external:
    for residue,(tag,a,d) in zip([0]+list(range(3,p)),tags):
        terms=[(3**a,2),(p,residue)]+[(r,1) for r in internal if d%r==0]
        add('forbid_'+str(p)+'_'+str(residue),terms,point(vals={p:residue}))

links=((5,11),(11,19),(7,23))
for p,r in links:
    for a,(u,v) in enumerate(((1,2),(2,1))):
        vals={z:1 for z in external}
        if (p,r)==(5,11): vals.update({5:u,11:v,19:v})
        elif (p,r)==(11,19): vals.update({5:u,11:u,19:v})
        else: vals.update({7:u,23:v})
        add('link_'+str(p)+'_'+str(r)+'_'+str(u)+str(v),[(3**a,2),(p,u),(r,v)],point(vals=vals))

# One fixed code, with all effective owners beneath the target parent2.
safe={2,4,5,7,8}; short={2,4,5,7,8,11}
leaves={(3,13),(4,16)}|{(4,x) for x in short}
for x in range(243):
    if x%9 in safe and x%27!=13 and x%81!=16 and x%81 not in short:
        leaves.add((5,x))
code={0:(3,13),111:(4,16),112:(5,98),1:(4,2),2:(4,4),3:(4,5),4:(4,7),5:(4,8),6:(4,11),
      10:(5,29),11:(5,110),12:(5,191),14:(5,56),20:(5,17),21:(5,44)}
assert set(code.values())<=leaves and len(code)==len(set(code.values()))
for digit,leaf in zip(sorted(set(range(q))-set(code)),sorted(leaves-set(code.values()))):code[digit]=leaf
assert len(code)==113
for (a,x),(b,y) in combinations(leaves,2): assert (x-y)%3**min(a,b)!=0

add('unitq',[(q,0)],point(digit=0))
add('unit3q',[(3,1),(q,111)],point(old=7,digit=111))
add('unit9q',[(9,8),(q,112)],point(old=8,digit=112))
for a,digit in enumerate((3,4,1)):
    old=code[digit][1]%9
    add('target_'+str(a),[(3**a,old),(q,digit),(m,1)],point(old=old,digit=digit))

owners={5:((10,1),(11,2),(20,1)),7:((12,1),(14,2),(21,1))}
for s,options in owners.items():
    for a,(digit,residue) in enumerate(options):
        old=code[digit][1]%9
        vals={p:residue if p in (A if s==5 else B) else 1 for p in external}
        add('owner_'+str(s)+'_'+str(a),[(3**a,old),(q,digit),(s,residue)],point(old=old,digit=digit,vals=vals))

assert len({o['n'] for o in orig})==len(orig)
assert all(o['n'] > 1 and o['n'] % 2 == 1 and Q % o['n'] == 0
           and 0 <= o['r'] < o['n'] for o in orig)
private_checks=0
for o in orig:
    hit=[u['name'] for u in orig if (o['private']-u['r'])%u['n']==0]
    assert hit==[o['name']],(o['name'],hit)
    private_checks+=len(orig)
comparable=0
for x,y in combinations(orig,2):
    if x['n']%y['n']==0 or y['n']%x['n']==0:
        comparable+=1
        assert (x['r']-y['r'])%gcd(x['n'],y['n'])!=0

K={(x,y):crt([(m,1)]+[(p,1+x) for p in A]+[(p,1+y) for p in B]) for x,y in product((0,1),repeat=2)}
gamma=W
for w in K.values():gamma=gcd(gamma,w-K[(0,0)])
assert gamma==m
qfree=[o for o in orig if o['n']%q!=0]
# Exact mask proof reduces to the binary 2^5 grid after all other roots are deleted.
# Check only this surviving grid; no W or Q enumeration is used.
live=[]
for bits in product((1,2),repeat=len(external)):
    vals=dict(zip(external,bits))
    x=point(vals=vals)
    if not any((x-o['r'])%o['n']==0 for o in qfree): live.append(x%W)
assert set(live)==set(K.values())
for w in K.values():
    hits=[]
    for s,options in owners.items():
        hits.append([i for i,(digit,r) in enumerate(options) if code[digit][1]%27==2 and w%s==r])
    assert len(hits[0])==len(hits[1])==1
for i,j in product(range(3),repeat=2):
    covered={w for w in K.values() if any(code[owners[s][a][0]][1]%27==2 and w%s==owners[s][a][1] for s,a in [(5,i),(7,j)])}
    assert covered != set(K.values())

# Query projections: none, X, Y, XY; minimal maxima are1,1/2,1/2,1/4.
counts=[0]*4
for k in range(len(primes)+1):
    for supp in combinations(primes,k):
        counts[any(p in A for p in supp)+2*any(p in B for p in supp)]+=1
assert counts==[8,56,24,168]
assert counts[0]+F(counts[1],2)+F(counts[2],2)+F(counts[3],4)==90

# Inspect top-row GLC for every nonternary prime anchor dividing Q.
# No global EB1 property is assumed.
glc_fail=[]
for anchor in primes+(q,):
    groups={}
    for o in orig:
        if o['n']%9==0 and o['n']%anchor==0:
            groups.setdefault((o['r']%9,o['r']%anchor),[]).append(o)
    for key,group in groups.items():
        edges=[]
        for x,y in combinations(group,2):
            for p in primes+(q,):
                if p!=anchor and x['n']%p==y['n']%p==0 and (x['r']-y['r'])%p==0:
                    edges.append((x['name'],y['name'],p));break
        for e,f in combinations(edges,2):
            if len({e[0],e[1],f[0],f[1]})==4:
                glc_fail.append((anchor,key,e,f));break
        if glc_fail and glc_fail[-1][0]==anchor: break
assert not glc_fail, glc_fail
hole=point(old=2,digit=50)
assert hole==1076125640591
assert not any((hole-o['r'])%o['n']==0 for o in orig)
assert 1469 not in {o['n'] for o in orig} and (9*q*m)%1469==0
assert all(sum(code[d][1]%27==2 and w%s==r
               for s in owners for d,r in owners[s])==2 for w in K.values())

def alternative_code_descent():
    originals=orig
    code={0:(3,13),111:(4,16),112:(5,98)}
    for d,ell in zip(range(30,36),(2,4,5,7,8,11)):code[d]=(4,ell)
    code.update({3:(5,14),4:(5,25),1:(5,29),10:(5,110),11:(5,191),20:(5,17),12:(5,56),14:(5,137),21:(5,44)})
    assert len(code)==len(set(code.values())) and set(code.values())<=leaves
    for d,L in zip(sorted(set(range(q))-set(code)),sorted(leaves-set(code.values()))):code[d]=L
    assert len(code)==113
    for (a,x),(b,y) in combinations(code.values(),2):assert (x-y)%3**min(a,b)!=0
    safe={2,4,5,7,8}
    decoder={}
    for t in range(243):
        hits=[d for d,(a,ell) in code.items() if (t-ell)%3**a==0]
        assert len(hits)==(1 if t%9 in safe else 0)
        if hits:decoder[t]=hits[0]
    assert len(decoder)==135

    def crt(items):
        r=0; n=1
        for p,a in items:
            if p==1:continue
            r+=n*(((a-r)*pow(n,-1,p))%p);n*=p;r%=n
        return r

    oldq=[o for o in originals if o['n']%q==0]
    retained=[o for o in originals if o['n']%q]
    assert all(9*W%o['n']==0 for o in retained)
    assert all(o['n']%2 and o['n']>1 for o in originals)
    assert any(o['n']==3 and o['r']==0 for o in originals)
    assert any(o['n']==9 and o['r']==1 for o in originals)
    new=[]
    inverse_enclosure_checks=0
    for o in oldq:
        n=o['n']; a=0
        while n%3==0:n//=3;a+=1
        s=n//q; d=o['r']%q; depth,ell=code[d]
        assert 0<=a<=2 and depth>=a+3
        assert ell%3**a==o['r']%3**a
        new_n=3**(a+3)*s
        new_r=crt([(3**(a+3),ell),(s,o['r']%s)])
        assert new_r%3**(a+3)==ell%3**(a+3)
        assert new_r%s==o['r']%s
        assert new_n*q==27*o['n']
        for t,digit in decoder.items():
            if digit==d and t%3**a==o['r']%3**a:
                assert (t-new_r)%3**(a+3)==0
            inverse_enclosure_checks+=1
        new.append({'old_name':o['name'],'old_modulus':o['n'],'old_residue':o['r'],'a':a,'cofactor':s,'q_digit':d,'inverse_depth':depth,'inverse_leaf':ell,'modulus':new_n,'residue':new_r})
    assert len(new)==12 and len(retained)==66
    assert len({o['modulus'] for o in new})==12
    assert not ({o['modulus'] for o in new}&{o['n'] for o in originals})
    assert all(o['modulus']%27==0 for o in new)
    assert all(o['modulus']%2 and o['modulus']>1 for o in new)
    assert inverse_enclosure_checks==1620
    assert {o['cofactor'] for o in new}=={1,5,7,6409}
    assert {o['q_digit'] for o in new}.isdisjoint(range(30,36))
    oldsum=sum(o['n'] for o in oldq);newsum=sum(o['modulus'] for o in new)
    assert (oldsum,newsum)==(9433918,2254122)
    assert oldsum-newsum==7179796
    new_period=lcm(*(o['n'] for o in retained),*(o['modulus'] for o in new))
    assert new_period==243*W
    # A direct old-covered / new-uncovered point confirms that this is a pullback
    # whole-cover argument, not pointwise containment of the numerical AP unions.
    w11=K[(1,1)]
    lost=crt([(243,2),(W,w11),(q,3)])
    assert any((lost-o['r'])%o['n']==0 for o in originals)
    assert all((lost-o['r'])%o['n']!=0 for o in retained)
    assert all((lost-o['residue'])%o['modulus']!=0 for o in new)
    result={'selected_short_digits':list(range(30,36)),'old_q_bearing_count':12,'new_count':12,'retained_count':66,'old_q_bearing_sum':oldsum,'new_sum':newsum,'saving':oldsum-newsum,'new_period':new_period,'corridor_residue_checks':243,'inverse_enclosure_checks':inverse_enclosure_checks,'new_APs':new,'alternative_code':[{'q_digit':d,'depth':L[0],'leaf':L[1]} for d,L in sorted(code.items())],'old_covered_new_uncovered_point':lost,'scope':'Common-source pullback descent conditional on original whole coverage; not containment of the old numerical AP union.'}
    return result

print(json.dumps({
    'scope': 'Local actual paid-mask countermodel; noncover, not divisor-closed, no EB1 claim',
    'q':q, 'm':m, 'W':W, 'Q':Q,
    'internal_primes':internal, 'X_primes':A, 'Y_primes':B,
    'original_count':len(orig), 'qfree_count':len(qfree),
    'private_membership_checks':private_checks,
    'comparable_pairs_disjoint':comparable,
    'nonternary_anchor_GLC_failures':glc_fail,
    'residual': [{'X':x,'Y':y,'residue':w} for (x,y),w in K.items()],
    'Gamma':gamma, 'query_projection_counts':counts,
    'minimum_query_norm':90, 'all_9_owner_plans_fail':True,
    'actual_six_sibling_load':2, 'uncovered_integer':hole,
    'missing_divisor_label':1469,
    'originals':orig,
    'code': [{'digit':d,'depth':a,'residue':r} for d,(a,r) in sorted(code.items())],
    'owners': {str(s):list(options) for s,options in owners.items()},
    'alternative_code_descent': alternative_code_descent(),
}, indent=2, sort_keys=True))
