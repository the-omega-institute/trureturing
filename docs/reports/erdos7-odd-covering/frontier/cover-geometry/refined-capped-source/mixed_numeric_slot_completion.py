#!/usr/bin/env python3
"""Exact finite certificate consumer for a common numerical-slot cap completion.

The finite checks do not replace the accompanying infinite ray/greedy proof and
make no assertion of actual deletion saturation or an odd distinct covering.
Only explicit input paths are opened; standard library only; no assertions.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
from math import prod
from pathlib import Path
import argparse
import heapq
import importlib.util
import json

P=(5,7,11,13,17,19,23)
SUPPORTS=tuple(s for s in range(1<<len(P)) if s.bit_count()>=2)
DEN=prod(q-2 for q in P)
CHECKS=0

def require(test,label):
    global CHECKS
    CHECKS+=1
    if not test:
        raise ValueError(label)

def finite_denominators(ps,limit):
    out=[]
    def visit(i,d):
        if i==len(ps):
            out.append(d)
            return
        d*=ps[i]
        while d<=limit:
            visit(i+1,d)
            d*=ps[i]
    visit(0,1)
    return sorted(out)

def ordered_denominators(ps):
    base=prod(ps)
    todo=[base]
    seen={base}
    while todo:
        d=heapq.heappop(todo)
        yield d
        for p in ps:
            v=d*p
            if v not in seen:
                seen.add(v)
                heapq.heappush(todo,v)

def interval_union(intervals):
    out=[]
    for a,b in sorted(intervals):
        if out and a<=out[-1][1]:
            out[-1]=(out[-1][0],max(b,out[-1][1]))
        else:
            out.append((a,b))
    return out

def role_vector(parts):
    out=[F(0)]*10
    for j,w in parts:
        require(type(j) is int and 0<=j<10,'role index')
        w=F(w)
        require(w>=0,'negative role mass')
        out[j]+=w
    require(sum(out)==1,'role masses do not sum to one')
    return out

def star_vector(parts):
    for w,(r,t) in parts:
        require(type(r) is int and r in (0,1),'star root index')
        require(type(t) is int and 0<=t<5,'star leaf index')
    return role_vector([(5*r+t,w) for w,(r,t) in parts])

def common_polynomial(candidate):
    stars=[star_vector(s) for s in candidate['stars']]
    require(len(stars)==7,'seven stars required')
    require(len(candidate['support_colors'])==len(SUPPORTS),'120 colors required')
    colors={}
    for s,spec in zip(SUPPORTS,candidate['support_colors']):
        colors[s]=role_vector([(spec,'1')] if type(spec) is int else spec)
    ans=[]
    explicit=[]
    pairs=[(s,t) for s,t in combinations(SUPPORTS,2) if not s&t]
    triples=[(s,t,u) for s,t,u in combinations(SUPPORTS,3) if not(s&t or s&u or t&u)]
    require((len(pairs),len(triples))==(546,210),'matching combinatorics')
    for leaf in range(5):
        def incidence(v):
            return sum(w*(int(j//5==int(leaf>=2))+int(j%5==leaf)) for j,w in enumerate(v))
        z=[F(p-2)-incidence(v) for p,v in zip(P,stars)]
        c={s:1+incidence(v) for s,v in colors.items()}
        @lru_cache(None)
        def matching(mask):
            if mask==0:
                return F(1)
            bit=mask&-mask
            i=bit.bit_length()-1
            return z[i]*matching(mask^bit)-sum(c[s]*matching(mask^s) for s in SUPPORTS if s&bit and s&mask==s)
        ans.append(matching(127)/DEN)
        def untouched(mask):
            return prod(z[i] for i in range(7) if not mask>>i&1)
        v=untouched(0)-sum(c[s]*untouched(s) for s in SUPPORTS)
        v+=sum(c[s]*c[t]*untouched(s|t) for s,t in pairs)
        v-=sum(c[s]*c[t]*c[u]*untouched(s|t|u) for s,t,u in triples)
        explicit.append(v/DEN)
    require(ans==explicit,'matching recursion differs from 120/546/210 polynomial')
    require(ans==list(map(F,candidate['expected_leaf_responses'])),'leaf response mismatch')
    require(all(x>=0 for x in ans),'negative leaf response')
    require(sum(x==0 for x in ans)==3,'expected exactly three zero leaf responses')
    return stars,colors,ans

def verify_star_slots(stars,certs):
    require(len(certs)==7,'missing star slot completion')
    for q,want,c in zip(P,stars,certs):
        require(c['prime']==q,'star prime order')
        prefix=c['prefix_roles']
        tail=c['constant_tail_role']
        parts=[(j,F(q-1,q**n)) for n,j in enumerate(prefix,1)]
        parts.append((tail,F(1,q**len(prefix))))
        require(role_vector(parts)==want,'star numerical slots mismatch')

def verify_mixed(mask,spec,cert,greedy_steps):
    ps=tuple(P[i] for i in range(7) if mask>>i&1)
    require(cert['support_mask']==mask,'support mask mismatch')
    require(tuple(cert['primes'])==ps,'support primes mismatch')
    require(len(spec)==2,'two-color certificate required')
    (role_a,t),(role_b,tb)=spec
    t,tb=F(t),F(tb)
    require(t+tb==1 and 0<t<1,'two-color mass')
    require(cert['first_role']==role_a and cert['second_role']==role_b,'completion roles mismatch')
    require(F(cert['target'])==t,'completion target mismatch')
    p,q=ps[:2]
    r=prod(ps[2:])
    threshold=r*p*q**(p-1)
    C=prod(v-1 for v in ps)
    require(cert['threshold']==threshold,'ray threshold mismatch')
    head=finite_denominators(ps,threshold)
    tail=1-sum((F(C,d) for d in head),F(0))
    require(tail>0 and F(cert['tail_mass'])==tail,'tail mass mismatch')
    chosen=cert['selected_head_denominators']
    require(len(chosen)==len(set(chosen)),'repeated numerical slot')
    require(all(d in head for d in chosen),'selected slot outside finite head')
    subtotal=sum((F(C,d) for d in chosen),F(0))
    residual=t-subtotal
    require(F(cert['residual'])==residual,'residual mismatch')
    require(0<=residual<=tail,'head selection leaves infeasible tail residual')
    intervals=[(F(0),tail)]
    counts=[1]
    for d in reversed(head):
        a=F(C,d)
        intervals=interval_union(intervals+[(x+a,y+a) for x,y in intervals])
        counts.append(len(intervals))
    require(any(a<=t<=b for a,b in intervals),'target outside exact subsum union')
    require(counts[-1]==cert['final_interval_count'],'interval count mismatch')
    require(len(head)==cert['head_count'],'head count mismatch')
    # Finite independent sanity audit of the all-height ray and greedy rules.
    rho=residual
    remaining=tail
    tail_choices=[]
    steps=0
    for d in ordered_denominators(ps):
        if d<=threshold:
            continue
        a=F(C,d)
        ray_sum=F(0)
        ray_starts=[]
        for b in range(1,p):
            base=r*q**b
            require(base<=F(d,p),'ray base exceeds d/p')
            m=base*p
            while m<=d:
                m*=p
            require(d<m<=p*d,'ray first denominator bounds')
            ray_starts.append(m)
            ray_sum+=F(C*p,m*(p-1))
        require(len(set(ray_starts))==p-1,'ray starts are not distinct')
        require(ray_sum>=a,'ray bound smaller than current atom')
        require(remaining-a>=ray_sum,'explicit ray tail exceeds exact remaining mass')
        use=rho>=a
        if use:
            rho-=a
            tail_choices.append(d)
        remaining-=a
        require(0<=rho<=remaining,'greedy residual left tail interval')
        steps+=1
        if steps==greedy_steps:
            break
    return dict(support_mask=mask,primes=list(ps),normalizer=C,threshold=threshold,
                head_count=len(head),final_interval_count=len(intervals),
                target=str(t),tail_mass=str(tail),selected_head_denominators=chosen,
                head_subtotal=str(subtotal),residual=str(residual),
                greedy_audit_steps=steps,greedy_selected_count=len(tail_choices),
                greedy_remaining_mass=str(remaining),greedy_residual=str(rho),
                interval_union=[[str(a),str(b)] for a,b in intervals])

def fixed_weight_hinge(response,library_path):
    require(library_path.is_file(),'existing product hinge library required')
    spec=importlib.util.spec_from_file_location('e7_existing_product_hinge',library_path)
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    require(tuple(module.P)==P,'hinge prime window mismatch')
    weights=(F(1,3),F(1,3),F(1,9),F(1,9),F(1,9))
    r=max(sum(weights[:2]),sum(weights[2:]))
    v=max(weights)
    mass=sum(w*max(x,F(0)) for w,x in zip(weights,response))
    ratios=[(c+dr*r+dv*v,h) for h,(c,dr,dv) in enumerate(module.hinge_coefficients(),1)]
    require(len(ratios)==27,'all 27 positive product-hinge breakpoints required')
    full_nonternary_mean=prod(F(p-1,p-2) for p in P)
    ratios.insert(0,(full_nonternary_mean*(1+r+F(3,2)*v)/28,0))
    require(len(ratios)==28,'all 28 nonnegative product-hinge breakpoints required')
    threshold,h=min(ratios)
    require(mass==F(80083719696451,4070321102680875),'specified fixed-weight response')
    require(h==16,'specified minimizing hinge')
    for ratio,j in ratios:
        require(ratio-mass>F(7,500),'strict fixed-weight hinge obstruction gap')
    return dict(weights=list(map(str,weights)),root_cap=str(r),leaf_cap=str(v),
                clipped_mass=str(mass),clipped_mass_decimal=float(mass),
                minimum_hinge_ratio=str(threshold),minimum_hinge_ratio_decimal=float(threshold),
                minimizing_h=h,gap=str(threshold-mass),gap_decimal=float(threshold-mass),
                strict_gap_lower_bound='7/500',
                all_hinge_ratios=[dict(h=j,ratio=str(ratio)) for ratio,j in ratios])

def run(data,greedy_steps,hinge_library):
    require(data['schema']=='e7-mixed-numerical-cap-completion-v1','certificate schema')
    candidate=data['candidate']
    stars,colors,response=common_polynomial(candidate)
    verify_star_slots(stars,data['star_completions'])
    fractions={s:spec for s,spec in zip(SUPPORTS,candidate['support_colors']) if type(spec) is not int}
    certs=data['mixed_completions']
    require(len(certs)==len(fractions),'missing or extra mixed completion')
    require({c['support_mask'] for c in certs}==set(fractions),'mixed completion masks mismatch')
    results=[verify_mixed(c['support_mask'],fractions[c['support_mask']],c,greedy_steps) for c in certs]
    hinge=fixed_weight_hinge(response,hinge_library)
    return dict(status='PASS: exact finite cap-completion certificate',scope='Infinite numerical slot existence uses the supplied ray/greedy derivation. The stated clipped-polynomial/product-hinge comparison fails at the specified fixed weights in the numerical cap-completion domain. No Lean compilation, actual deletion saturation, covering realization, all-fixed-weight obstruction, or obstruction to the Report792 weights is claimed.',checks=CHECKS,stars=7,constant_mixed_supports=len(SUPPORTS)-len(fractions),fractional_mixed_supports=len(fractions),leaf_responses=list(map(str,response)),mixed_completions=results,fixed_weight_obstruction=hinge)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--certificate',type=Path,default=Path(__file__).with_name(Path(__file__).stem+'_certificate.json'))
    ap.add_argument('--write-result',type=Path)
    ap.add_argument('--hinge-library',type=Path,default=Path(__file__).with_name('clipped_common_source_obstruction.py'))
    ap.add_argument('--greedy-steps',type=int,default=128)
    args=ap.parse_args()
    require(args.greedy_steps>0,'positive greedy audit count required')
    result=run(json.loads(args.certificate.read_text()),args.greedy_steps,args.hinge_library)
    if args.write_result:
        args.write_result.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('mixed_completions','fixed_weight_obstruction')},indent=2))

if __name__=='__main__':
    main()
