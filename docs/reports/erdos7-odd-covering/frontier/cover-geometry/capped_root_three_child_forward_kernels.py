#!/usr/bin/env python3
"""A capped root and three fixed two-head/one-outside children in the global network.

Exact rational certificate; the report supplies the normalized common-law proof.
"""
import argparse,json
from fractions import Fraction as F
from hashlib import sha256
from heapq import heappop,heappush
from itertools import product
from math import prod
from pathlib import Path

def encode(x):
    if isinstance(x,F): return str(x)
    if isinstance(x,dict): return {str(k):encode(v) for k,v in x.items()}
    if isinstance(x,(tuple,list)): return [encode(v) for v in x]
    return x

def prefix(ps,count):
    z=(0,)*len(ps); pending=[(1,z)]; seen={z}; out=[]
    while len(out)<count:
        d,e=heappop(pending); out.append((d,e))
        for i,p in enumerate(ps):
            ee=tuple(a+(i==j) for j,a in enumerate(e))
            if ee not in seen:
                seen.add(ee); heappush(pending,(d*p,ee))
    return out

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source-dir',type=Path,default=Path(__file__).parent)
    ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=ap.parse_args(); checks={}; sources={}
    def require(name,value):
        if not value: raise ArithmeticError(name)
        checks[name]=True
    def load(name):
        path=args.source_dir/name; raw=path.read_bytes(); d=json.loads(raw)
        require(name+'_checks',bool(d['checks']) and all(v is True for v in d['checks'].values()))
        fingerprint=sha256(path.with_suffix('.py').read_bytes()).hexdigest()
        require(name+'_producer',d['producer_sha256']==fingerprint)
        sources[name]=dict(sha256=sha256(raw).hexdigest(),producer_sha256=fingerprint)
        return d
    staged=load('staged_two_parent_attachment.json')
    pairs=load('shared_head_pair_forward_kernels.json')
    require('shared_staged_input',pairs['sources']['staged_two_parent_attachment.json']==sources['staged_two_parent_attachment.json'])
    gate=F(staged['constants']['inherited_gate']); alpha=F(staged['constants']['alpha'])
    require('head_constants',gate==F(26345885990886052732242307711,9055182074115772514304000000000)
            and alpha==F(2673,138320))
    def moment(ps,caps,N,tag):
        labels=prefix(ps,N+1); top=labels[-1][0]; ranges=[]
        for p in ps:
            z=1; n=0
            while z<=top: z*=p; n+=1
            ranges.append(range(n))
        grid=sorted((prod(p**e for p,e in zip(ps,es)),es) for es in product(*ranges)
                    if prod(p**e for p,e in zip(ps,es))<=top)
        require(tag+'_literal_prefix',grid==labels)
        def kernel(e,f):
            return prod((c if max(i,j) else F(1))/p**max(i,j) for p,c,i,j in zip(ps,caps,e,f))
        def row(e):
            return prod((1+c/F(p-1)) if i==0 else c*F(i+1+F(1,p-1),p**i)
                        for p,c,i in zip(ps,caps,e))
        total=prod(1+c*(F(3,p-1)+F(2,(p-1)**2)) for p,c in zip(ps,caps))
        tails=[]; current=total
        for n,(_,e) in enumerate(labels):
            current-=2*(row(e)-sum((kernel(e,f) for _,f in labels[:n]),F()))-kernel(e,e)
            literal=total-2*sum((row(f) for _,f in labels[:n+1]),F())
            literal+=sum((kernel(f,g) for _,f in labels[:n+1] for _,g in labels[:n+1]),F())
            require(f'{tag}_complement_{n}',current==literal and current>0)
            tails.append(current)
        return dict(primes=ps,caps=caps,selected_nonunit_count=N,literal_prefix=labels,
                    complete_moment=total,unselected_moment=current,tails=tails)
    rm=moment((3,5),(F(2),F(5,3)),15,'root')
    rootD=19; rootdelta=F(1,5); rootcap=F(36,rootD)/(1-rootdelta)
    rootfee=rm['unselected_moment']/(4*rootdelta*(1-rootdelta)*rootD**2)
    require('root_moment_and_fee',rm['unselected_moment']==F(1043,9720)
            and rootcap==F(45,19) and rootfee==F(5215,11228544))
    require('root_preserves_old_prefix_interface',rootcap<F(37,4) and rootcap/F(37)<F(1,3))
    # For q>=37, (q-1)/(q-18) decreases; its cross-multiplied difference
    # from 36/19 is 17(q-37)/(19(q-18)), nonnegative.
    require('root_monotone_cap_identity',36-19==17 and 36*18-19==17*37)
    cm=moment((3,5,37),(F(2),F(5,3),rootcap),20,'children')
    require('child_moment',cm['unselected_moment']==F(1248323,4432320))
    childrows=[]
    for v in (41,43,47):
        D=v-23; delta=F(1,2); cap=F(2*(v-1),D)
        fee=cm['unselected_moment']/D**2
        require(f'child_{v}_normalized_cap',cap<=6 and cap<=F(v,4))
        childrows.append(dict(reference_owner=v,selected_nonunit_count=20,D=D,
                              threshold=delta,conditional_Haar_cap=cap,violation_fee=fee))
    require('later_children_cap_monotone',2*(41-1)<=6*(41-23) and 23>1)
    early=F(staged['fee_tables']['3_5']['total_fee'])
    late=F(staged['fee_tables']['3_23']['total_fee'])
    two=F(pairs['consequence']['total_nonroot_fee'])
    ordinary=F(staged['consequence']['ordinary_attachment_fee'])
    require('whole_prime_budgets',early<F(1,2600) and late<F(1,125000) and two<F(1,250000))
    require('single_head_ordinary_fee',ordinary==F(1,131072))
    reclaimed=[]
    for v in (37,41,43,47):
        terms={}
        for tag,factor in (('3_5',F(10,3)),('3_23',F(4))):
            row=next(r for r in staged['fee_tables'][tag]['finite_rows'] if r['entry_prime']==v)
            terms[tag]=factor*F(row['blocker_fee_upper'])
        if v>37:
            row=next(r for r in pairs['finite_rows'] if r['node_prime']==v)
            terms['two_parent']=2*F(row['node_violation_fee'])
        reclaimed.append(dict(reference_prime=v,terms=terms,total=sum(terms.values(),F())))
    reclaim=sum((r['total'] for r in reclaimed),F())
    star=rootfee+sum((r['violation_fee'] for r in childrows),F())
    base=gate-F(10,3)*early-4*late-2*ordinary-2*two
    raw=base+reclaim-star
    simple_raw=gate-F(1,780)-F(4,125000)-F(1,65536)-F(2,250000)+reclaim-star
    simple=alpha*simple_raw
    require('reclaimed_rows',reclaim==F(166863257555290507129,139748489904627489600000))
    require('one_joint_star_fee',star==F(27577492013,10914144768000))
    require('strict_positive_raw_reserve',raw>simple_raw>0)
    require('head_projection',simple==F(5260468727593499468839527169104406487,1136921153757303339735127550853120000000000)
            and simple>F(1,220000))
    result=dict(schema='capped-root-three-child-forward-kernels-v1',sources=sources,
        scope=dict(head='Report598 restriction',special_owners='First four network entries q0<q1<q2<q3, bounded below by37,41,43,47',
           root='q0 fixed parents first two head coordinates; N15,delta1/5 capped selected-complement row',
           children='q1,q2,q3 fixed triple of those same two head parents and q0; N20,delta1/2',
           other_owners='All Report614 fixed two-parent owners and global crossings, numerically after q3',
           ordinary='All existing private ordinary domains, Type I head branches and separate components',
           source='One normalized-row construction over the same actual head submeasure',
           heights='Arbitrary finite',phases='Arbitrary globally fixed per distinct numerical original modulus',
           excluded='Other three-parent inventories, unrestricted head labels, undeclared ordinary-interior crossings',lean_verified=False),
        constants=dict(head_gate=gate,alpha=alpha,single_head_cap=2,head_pair_cap=4,root_cap=rootcap),
        root_moment=rm,root=dict(reference_owner=37,selected_nonunit_count=15,D=rootD,threshold=rootdelta,
                               conditional_Haar_cap=rootcap,violation_fee=rootfee),
        child_moment=cm,children=childrows,reclaimed=reclaimed,
        budget=dict(early_roots=early,late_roots=late,two_parent=two,ordinary_base=ordinary,
                    old_raw=base,reclaimed=reclaim,new_star=star,raw=raw,simple_raw=simple_raw),
        consequence=dict(exact_extendible_head_lower=alpha*raw,simple_extendible_head_lower=simple,
                         strictly_greater_than='1/220000',full_density_lower='1/(220000 Q_off)'),
        checks=checks,producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    args.output.write_text(json.dumps(encode(result),indent=2)+'\n')
    print(json.dumps(encode(dict(checks=len(checks),root_fee=rootfee,star_fee=star,reclaimed=reclaim,
                               simple_head_lower=simple,strictly_greater_than='1/220000'))))
if __name__=='__main__':main()
