#!/usr/bin/env python3
"""One common law for arbitrary fixed three-parent inventories under the root-one head.

Exact finite staircase costs and a complete cubical tail. Every outside row
is normalized, including dead fibres. The proof supplies the same-source
conditional integration; this program certifies its arithmetic.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from heapq import heappop, heappush
import json
from math import prod
from pathlib import Path


def encode(x):
    if isinstance(x,F): return str(x)
    if isinstance(x,dict): return {str(k):encode(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)): return [encode(y) for y in x]
    return x


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source',type=Path,default=Path(__file__).with_name('root_one_all_stars_certificate.json'))
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args()
    checks={}
    def require(name,truth):
        if not truth: raise ArithmeticError(name)
        checks[name]=True
    raw=args.source.read_bytes(); source=json.loads(raw)
    require('published_root_one_source_pin',sha256(raw).hexdigest()=='b932b6ef8731d8047d052891e1e477e73a5d88bd07b956b02cfe6f6bb873a8d0')
    for extension,field in [('py','producer_sha256'),('cpp','kernel_sha256')]:
        require('source_'+extension+'_pin',sha256(args.source.with_suffix('.'+extension).read_bytes()).hexdigest()==source[field])
    gate=F(source['gate_lower']);alpha=F(2673,138320)
    require('root_one_complete_gate',gate>F(7,250) and source['certificate']['passed'] is True)
    require('source_density',F(source['metadata']['source_density_D'])==F(3458,405))
    require('head_transport_density',F(source['metadata']['Haar_factor'])==alpha)
    require('source_not_Lean',source['new_lean_verification'] is False)
    ps=(3,5,7);caps=(F(2),)*3;boundary=971
    heap=[(1,(0,0,0))];seen={(0,0,0)};labels=[]
    while len(labels)<boundary:
        d,es=heappop(heap);labels.append((d,es))
        for j,p in enumerate(ps):
            ee=tuple(e+(i==j) for i,e in enumerate(es))
            if ee not in seen:seen.add(ee);heappush(heap,(d*p,ee))
    powers=[];top=labels[-1][0]
    for p in ps:
        row=[];x=1
        while x<=top:row.append(x);x*=p
        powers.append(row)
    grid=[]
    for i,a in enumerate(powers[0]):
        for j,b in enumerate(powers[1]):
            if a*b>top:break
            for k,c in enumerate(powers[2]):
                if a*b*c>top:break
                grid.append((a*b*c,(i,j,k)))
    require('numeric_cofactor_prefix_complete',sorted(grid)==labels)
    def kernel(e,f):
        return prod(F(2,p**max(i,j)) if max(i,j) else F(1) for p,i,j in zip(ps,e,f))
    def row(e):
        return prod((1+F(2,p-1)) if i==0 else F(2,p**i)*(i+1+F(1,p-1)) for p,i in zip(ps,e))
    factors=tuple(1+2*(F(3,p-1)+F(2,(p-1)**2)) for p in ps)
    total=prod(factors);moment=total;row_sum=F();square=F();moments=[]
    for n,(_,e) in enumerate(labels):
        cross=sum((kernel(e,f) for _,f in labels[:n]),F());diagonal=kernel(e,e)
        row_sum+=row(e);square+=2*cross+diagonal
        moment-=2*(row(e)-cross)-diagonal
        require(f'moment_{n}',moment==total-2*row_sum+square and moment>0 and (not moments or moment<=moments[-1]))
        moments.append(moment)
    sieve=bytearray(b'\1')*boundary;sieve[:2]=b'\0\0'
    for p in range(2,boundary):
        if sieve[p]:
            for v in range(p*p,boundary,p):sieve[v]=0
    primes=[v for v in range(37,boundary) if sieve[v]]
    rows=[]
    for v in primes:
        fee,n=min((moments[n]/(v-3-n)**2,n) for n in range(v-10))
        D=v-3-n;density=F(2*(v-1),D)
        require(f'owner_{v}_domain',D>=8 and n>=0)
        require(f'owner_{v}_conditional_cap',density<=F(v,4))
        require(f'owner_{v}_all_height_fee',fee==moments[n]/D**2)
        rows.append(dict(owner_prime=v,selected_nonunit_patterns=n,complement_D=D,
                         threshold=F(1,2),conditional_Haar_cap=density,
                         cofactor_moment=moments[n],violation_fee=fee))
    finite=sum((r['violation_fee'] for r in rows),F())
    require('complete_finite_prime_window',len(rows)==152 and rows[0]['owner_prime']==37 and rows[-1]['owner_prime']==967)
    require('finite_fee',finite<F(53,2000))
    # Bound the complete moment outside [0,n)^3, including both off-cube indices.
    n0=7
    AA=tuple(F(2*p*(p+1),(p-1)**2*p**n0) for p in ps)
    BB=tuple(F(2*p,(p-1)*p**n0)*(n0+1+F(2,p-1)) for p in ps)
    cube=sum(AA[i]*prod(factors[j] for j in range(3) if j!=i) for i in range(3))
    cube+=2*sum(BB[i]*BB[j]*factors[3-i-j] for i in range(3) for j in range(i+1,3))
    require('cube_scaled_start',cube*3**n0==F(796108766521,22059187500)<37)
    require('all_later_scaled_diagonals',all(F(3,p)<=1 for p in ps))
    require('all_later_scaled_crosses',all(F(3,ps[i]*ps[j])*F(n0+2,n0+1)**2<1 for i in range(3) for j in range(i+1,3)))
    require('tail_interval_contains_boundary',2*n0**3+3<=boundary<=2*(n0+1)**3+1)
    require('tail_conditional_density',F(2*(2*n0**3+2),n0**3+1)==4<=F(boundary,4))
    tail=F(6*37)*F(n0+1,n0)**2/F(n0**4)*F(3,2)/3**n0
    require('complete_tail',tail==F(2368,28588707)<F(1,12000))
    fee=finite+tail
    require('all_outside_owners',fee<F(27,1000))
    require('outside_to_reference_prefix',max(F(p,4) for p in ps)<=2 and all(p<=37 for p in ps))
    ordinary=F(1,65536)
    raw_good=gate-fee-ordinary
    simple_raw=F(7,250)-F(27,1000)-ordinary
    head=alpha*simple_raw
    require('positive_actual_joint_mass',raw_good>simple_raw==F(8067,8192000)>0)
    require('uniform_extendible_head',head>F(1,53000))
    result=dict(schema='unrestricted-triple-parent-forward-kernels-v1',
        source=dict(name=args.source.name,sha256=sha256(raw).hexdigest(),producer_sha256=source['producer_sha256'],kernel_sha256=source['kernel_sha256']),
        scope=dict(head='Report617 fixed ten-prime root-one outside layout and central pure source; all retained central star and pair phases arbitrary',
          outside='Every owner >=37 has one fixed tuple of at most three distinct smaller parents, including any count of head parents; arbitrary finite size, crossings, heights and globally fixed phases',
          law='Complete head first; normalized capped rows in increasing outside prime order; no survival conditioning',
          ordinary='Inherited private extension domains and Type I branches; no undeclared interior crossings',
          excluded='Unrestricted head phases and labels, several independent parent tuples for one owner, more than three parents, undeclared private crossings'),
        constants=dict(head_gate=gate,alpha=alpha,reference_parents=ps,reference_caps=caps,threshold=F(1,2),conditional_density_rule='v/4',minimum_complement_D=8),
        moment_table=dict(all_factors=factors,all_moment=total,prefix=labels,complete_tail_moments=moments),
        finite_rows=rows,finite_fee=finite,
        tail=dict(boundary=boundary,cube_start=n0,selected_count='n^3-1',D='v-n^3-2',
                  scaled_start=cube*3**n0,moment_upper='37*3^(-n)',interval_count='6*(n+1)^2',fee=tail),
        consequence=dict(total_owner_fee=fee,total_owner_fee_strict=F(27,1000),ordinary_single_head_fee=ordinary,
          raw_good_lower=raw_good,simple_raw_lower=simple_raw,head_lower=alpha*raw_good,
          simple_head_lower=head,head_strict=F(1,53000),full_density_lower='1/(53000 Q_off)'),
        checks=checks,producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),new_lean_verification=False)
    args.output.write_text(json.dumps(encode(result),indent=2)+'\n')
    print(json.dumps(encode(dict(checks=len(checks),rows=len(rows),finite_fee=finite,tail_fee=tail,total_fee=fee,simple_head_lower=head))))

if __name__=='__main__':main()
