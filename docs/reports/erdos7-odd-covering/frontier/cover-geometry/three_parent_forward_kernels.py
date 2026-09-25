#!/usr/bin/env python3
"""Exact same-law reserve for two- and three-parent outside owners.

Three-parent owners have at least two outside parents. Finite selected
cofactor staircases and a complete cubical tail keep conditional density six.
The accompanying proof supplies the joint conditional-law statements.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from heapq import heappop, heappush
import importlib.util
import json
from math import prod
from pathlib import Path


def encode(value):
    if isinstance(value,F): return str(value)
    if isinstance(value,dict): return {str(k):encode(v) for k,v in value.items()}
    if isinstance(value,(list,tuple)): return [encode(v) for v in value]
    return value


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-dir',type=Path,default=Path(__file__).parent)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args()
    checks,sources={},{}
    def require(name,truth):
        if not truth: raise ArithmeticError(name)
        checks[name]=True
    def load(name):
        path=args.source_dir/name
        raw=path.read_bytes(); data=json.loads(raw)
        require(name+'_checks',bool(data['checks']) and all(x is True for x in data['checks'].values()))
        fingerprint=sha256(path.with_suffix('.py').read_bytes()).hexdigest()
        require(name+'_producer',fingerprint==data['producer_sha256'])
        sources[name]={'sha256':sha256(raw).hexdigest(),'producer_sha256':fingerprint}
        return data
    staged=load('staged_two_parent_attachment.json')
    network=load('shared_head_pair_forward_kernels.json')
    load('recursive_pair_forward_kernels.json')
    for parent in (staged,network):
        for name,pin in parent.get('sources',{}).items():
            if name in sources:
                require(name+'_shared_input',pin==sources[name])
    helper=args.source_dir/'recursive_pair_forward_kernels.py'
    spec=importlib.util.spec_from_file_location('existing_recursive_pair',helper)
    method=importlib.util.module_from_spec(spec); spec.loader.exec_module(method)

    alpha=F(staged['constants']['alpha']); gate=F(staged['constants']['inherited_gate'])
    early=F(staged['fee_tables']['3_5']['total_fee'])
    late=F(staged['fee_tables']['3_23']['total_fee'])
    ordinary=F(staged['consequence']['ordinary_attachment_fee'])
    pair_fee=F(network['consequence']['total_nonroot_fee'])
    controls=(F(2,5),F(9,20),F(1,2))
    head_caps=tuple(1/(1-d) for d in controls)
    require('head_original_Haar_caps',head_caps==(F(5,3),F(20,11),F(2)))
    require('all_single_head_caps_at_most_two',max(head_caps+(F(2),F(5,3)))==2)
    require('all_head_pair_caps_at_most_four',F(10,3)<4 and
            all(2*x<=4 for x in head_caps) and
            all(head_caps[i]*head_caps[j]<=4 for i in range(3) for j in range(i+1,3)))
    require('full_head_projection_density',alpha==F(2673,138320) and
            1/alpha==F(staged['constants']['density_D'])*prod(head_caps))
    require('unchanged_root_budgets',early<F(1,2600) and late<F(1,125000))
    require('ordinary_single_head_budget',ordinary==F(1,131072))
    require('unchanged_two_parent_budget',pair_fee<F(1,250000))
    require('root_complements_and_generated_caps',network['constants']['root_minimum_D']==4
            and network['constants']['nonroot_conditional_haar_density']==6)

    ps=(3,37,41); caps=(F(1),F(37,4),F(41,4)); boundary=971
    heap=[(1,(0,0,0))]; seen={(0,0,0)}; labels=[]
    while len(labels)<boundary:
        d,es=heappop(heap); labels.append((d,es))
        for k,p in enumerate(ps):
            ee=tuple(e+(j==k) for j,e in enumerate(es))
            if ee not in seen:
                seen.add(ee); heappush(heap,(d*p,ee))
    # An independent rectangular enumeration certifies every selected cofactor.
    grid=[]; top=labels[-1][0]
    powers=[]
    for p in ps:
        values=[]; x=1
        while x<=top: values.append(x); x*=p
        powers.append(values)
    for i,x in enumerate(powers[0]):
        for j,y in enumerate(powers[1]):
            if x*y>top: break
            for k,z in enumerate(powers[2]):
                if x*y*z>top: break
                grid.append((x*y*z,(i,j,k)))
    require('complete_distinct_three_parent_prefix',sorted(grid)==labels)
    def kernel(e,f):
        return prod((c if max(i,j) else F(1))/p**max(i,j)
                    for p,c,i,j in zip(ps,caps,e,f))
    def row(e):
        return prod((1+c/F(p-1)) if i==0 else c*F(i+1+F(1,p-1),p**i)
                    for p,c,i in zip(ps,caps,e))
    factors=tuple(1+c*(F(3,p-1)+F(2,(p-1)**2)) for p,c in zip(ps,caps))
    total=prod(factors); m=total; sum_rows=F(); square=F(); moments=[]
    for n,(_,e) in enumerate(labels):
        cross=sum((kernel(e,f) for _,f in labels[:n]),F())
        diagonal=kernel(e,e)
        m-=2*(row(e)-cross)-diagonal
        sum_rows+=row(e); square+=2*cross+diagonal
        require(f'complete_cofactor_tail_{n}',m==total-2*sum_rows+square
                and m>0 and (not moments or m<=moments[-1]))
        moments.append(m)
    sieve=bytearray(b'\1')*boundary; sieve[:2]=b'\0\0'
    for p in range(2,boundary):
        if sieve[p]:
            for q in range(p*p,boundary,p): sieve[q]=0
    primes=[q for q in range(43,boundary) if sieve[q]]
    require('complete_three_parent_prime_window',len(primes)==150 and
            primes==[r['node_prime'] for r in network['finite_rows'] if r['node_prime']>=43])
    rows=[]
    for v in primes:
        fee,n,delta=method.optimum(v,moments)
        D=v-3-n; cap=F(v-1,D)/(1-delta)
        require(f'node_{v}_legal_selected_complement',0<=n<v-3 and D>0)
        require(f'node_{v}_normalized_row_cap',0<delta<=F(1,2) and cap<=6)
        require(f'node_{v}_whole_height_fee',fee==moments[n]/(4*delta*(1-delta)*D*D))
        rows.append(dict(node_prime=v,selected_label_count=n,complement_D=D,
                         threshold=delta,conditional_Haar_cap=cap,
                         complete_cofactor_moment=moments[n],node_violation_fee=fee))
    finite=sum((r['node_violation_fee'] for r in rows),F())
    require('finite_three_parent_fee',finite<F(3,5000))

    n0=7
    both=tuple(c*F(p*(p+1),(p-1)**2)*F(1,p**n0) for p,c in zip(ps,caps))
    single=tuple(c*F(p,p-1)*F(1,p**n0)*(n0+1+F(2,p-1)) for p,c in zip(ps,caps))
    rectangle=sum(both[i]*prod(factors[j] for j in range(3) if j!=i) for i in range(3))
    rectangle+=2*sum(single[i]*single[j]*factors[3-i-j] for i in range(3) for j in range(i+1,3))
    require('cube_start_covers_entire_tail',2*n0**3+3<=boundary<=2*(n0+1)**3+1)
    require('cube_moment_at_start',rectangle*3**n0==F(211923214881494131358891,22212202531721076633600)<10)
    require('scaled_diagonal_terms_nonincreasing',all(F(3,p)<=1 for p in ps))
    require('scaled_cross_terms_strictly_decreasing',
            all(F(3,ps[i]*ps[j])*F(n0+2,n0+1)**2<1
                for i in range(3) for j in range(i+1,3)))
    require('cube_density_cap_at_first_node',F(2*(2*n0**3+2),n0**3+1)==4<=6)
    tail=F(60)*F(n0+1,n0)**2*F(1,n0**4)*F(3,2)*F(1,3**n0)
    require('all_interval_geometric_tail',tail==F(640,28588707)<F(1,40000))
    triple_fee=finite+tail
    require('complete_three_parent_fee',triple_fee<F(1,1600))

    raw=gate-F(10,3)*early-4*late-2*ordinary-2*(pair_fee+triple_fee)
    simple_raw=gate-F(1,780)-F(4,125000)-F(1,65536)-2*(F(1,250000)+F(1,1600))
    simple=alpha*simple_raw
    require('positive_same_law_raw_mass',raw>simple_raw>0)
    require('complete_head_reserve',simple==F(37925188791845275633871920243,6091532434864204079431680000000000)
            and simple>F(1,170000))
    result=dict(schema='three-parent-forward-kernels-v1',sources=sources,
      scope=dict(head='Report598 restriction',two_parent='Every Report614 owner retained',
        three_parent='Three fixed distinct smaller parents, at least two outside; arbitrary nonunit parent exponent triples and all positive owner heights',
        source='Same global unnormalized law; early roots preloaded, head-only normalized kernels, remaining owners in increasing order',
        ordinary='Existing disjoint private domains, single-head Type I branches and separate ordinary components',
        excluded='Three head-parent roots, two head plus one outside in a triple, more than three parents, undeclared private-interior crossings, unrestricted head labels',lean_verified=False),
      constants=dict(alpha=alpha,head_gate=gate,single_head_cap=2,head_pair_cap=4,
                     head_continuation_caps=head_caps,reference_parents=ps,reference_caps=caps,
                     generated_conditional_Haar_cap=6),
      moment_table=dict(all_label_factors=factors,all_label_moment=total,
                        literal_prefix=labels,complete_tail_moments=moments),
      finite_rows=rows,finite_three_parent_fee=finite,
      analytic_tail=dict(first_outside_prime=boundary,cube_start=n0,selected_count='n^3-1',
        threshold='1/2',conditional_Haar_cap=4,cube_scaled_moment_at_start=rectangle*3**n0,
        moment_bound='10*3^(-n)',integer_interval_count_bound='6*(n+1)^2',whole_tail_fee=tail),
      fees=dict(early_roots=early,late_roots=late,ordinary_single_head=ordinary,
                two_parent=pair_fee,three_parent=triple_fee),
      consequence=dict(raw_good_mass_lower=raw,exact_extendible_head_lower=alpha*raw,
                       simple_extendible_head_lower=simple,strictly_greater_than=F(1,170000),
                       full_density_lower='1/(170000 Q_off)'),
      checks=checks,producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    args.output.write_text(json.dumps(encode(result),indent=2)+'\n')
    print(json.dumps(encode(dict(checks=len(checks),rows=len(rows),finite_fee=finite,
                                tail_fee=tail,total_three_parent_fee=triple_fee,
                                simple_final=simple,strictly_greater_than=F(1,170000)))))


if __name__=='__main__': main()
