#!/usr/bin/env python3
"""Exact actual-prefix orbit source/query certificate, including every height.

No optimizer is used. The optional generation path writes the freshly checked
result; the default replays and compares adjacent retained data.
"""
from argparse import ArgumentParser
from collections import defaultdict
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import json
from math import isqrt
from pathlib import Path

CHECKS=0

def require(condition,message):
    global CHECKS
    CHECKS+=1
    if not condition:
        raise ValueError(message)

def integer(value):
    require(type(value) in (str,int),"integer input type")
    result=int(value)
    require(str(result)==str(value),"canonical integer input")
    return result

def is_prime(p):
    return p>=2 and all(p%d for d in range(2,isqrt(p)+1))

def factor_over(m,primes):
    result={}
    for p in primes:
        while m%p==0:
            result[p]=result.get(p,0)+1
            m//=p
    require(m==1,"original label supported on declared primes")
    return result

def coordinate_buckets(p,prefixes):
    children=defaultdict(set)
    nodes={(0,0)}
    for residue,depth in prefixes:
        for j in range(depth):
            key=(residue%(p**j),j)
            children[key].add((residue//(p**j))%p)
            nodes.add((residue%(p**(j+1)),j+1))
    buckets=[]
    def visit(residue,depth):
        used=children.get((residue,depth),set())
        if not used:
            buckets.append((depth,(residue,)))
            return
        free=tuple(residue+a*p**depth for a in range(p) if a not in used)
        if free:
            buckets.append((depth+1,free))
        for a in sorted(used):
            visit(residue+a*p**depth,depth+1)
    visit(0,0)
    require(sum((F(len(rs),p**e) for e,rs in buckets),F(0))==1,
            "coordinate orbit partition mass")
    require(len(buckets)<=len(nodes),"orbit count bounded by actual trie nodes")
    return buckets,len(nodes)

def coefficient(p,bucket,phase,depth):
    terminal,branches=bucket
    if depth<=terminal:
        return F(sum(r%(p**depth)==phase for r in branches),len(branches))
    return F(int(phase%(p**terminal) in branches),len(branches)*p**(depth-terminal))

def phase_rows(p,buckets,depth):
    representatives={r%(p**depth) for _,branches in buckets for r in branches}
    return tuple(sorted({tuple(coefficient(p,b,phase,depth) for b in buckets)
                         for phase in representatives}))

def build(family,primes):
    factorizations=[factor_over(m,primes) for m,_ in family]
    all_buckets=[]
    node_counts=[]
    exponents=[]
    for p in primes:
        prefixes={(a%(p**fs[p]),fs[p]) for (_,a),fs in zip(family,factorizations) if p in fs}
        bs,count=coordinate_buckets(p,prefixes)
        all_buckets.append(bs)
        node_counts.append(count)
        exponents.append(max((e for _,e in prefixes),default=0))
    live=[]
    haar=[]
    for indices in product(*(range(len(bs)) for bs in all_buckets)):
        survives=True
        for (_,a),fs in zip(family,factorizations):
            values=[coefficient(p,all_buckets[k][indices[k]],a%(p**fs[p]),fs[p])
                    for k,p in enumerate(primes) if p in fs]
            require(all(x in (0,1) for x in values),"each actual original constant on orbit")
            if all(values):
                survives=False
                break
        if survives:
            mass=F(1)
            for k,p in enumerate(primes):
                depth,branches=all_buckets[k][indices[k]]
                mass*=F(len(branches),p**depth)
            live.append(indices)
            haar.append(mass)
    return all_buckets,node_counts,exponents,live,haar

def all_height_queries(buckets,primes,exponents,live,masses):
    menus=[[phase_rows(p,bs,e) for e in range(exponents[k]+1)]
           for k,(p,bs) in enumerate(zip(primes,buckets))]
    total=F(0)
    maxima={}
    row_count=0
    for levels in product(*(range(e+1) for e in exponents)):
        maximum=F(0)
        for rows in product(*(menus[k][e] for k,e in enumerate(levels))):
            value=F(0)
            for indices,mass in zip(live,masses):
                term=mass
                for k,index in enumerate(indices):
                    term*=rows[k][index]
                value+=term
            maximum=max(maximum,value)
            row_count+=1
        fee=F(1)
        for k,p in enumerate(primes):
            if levels[k]==exponents[k]:
                fee*=F(p,p-1)
        maxima[levels]=maximum
        total+=fee*maximum
    return total,maxima,row_count

def two_chain(n):
    family=[]
    for j in range(1,n+1):
        power=3**j
        pure=1 if j==1 else 2+3**(j-1)
        mixed=2 if j==1 else 3**(j-1)
        phase=next(mixed+k*power for k in range(5) if (mixed+k*power)%5==0)
        family.extend(((power,pure),(5*power,phase)))
    return family

def dense_controls():
    results=[]
    for n in range(1,6):
        family=two_chain(n)
        primes=(3,5)
        bs,_,ee,live,haar=build(family,primes)
        period=5*3**n
        survivors=[x for x in range(period) if all(x%m!=a for m,a in family)]
        require(sum(haar,F(0))==F(len(survivors),period),"literal survivor mass")
        raw={x:F(1+(17*x*x+31*x+7)%101) for x in survivors}
        normal=sum(raw.values(),F(0))
        raw={x:v/normal for x,v in raw.items()}
        orbit_masses=[F(0) for _ in live]
        membership={}
        for x,weight in raw.items():
            match=[]
            for k,p in enumerate(primes):
                found=[i for i,b in enumerate(bs[k]) if x%(p**b[0]) in b[1]]
                require(len(found)==1,"literal point has one local orbit")
                match.append(found[0])
            orbit_index=live.index(tuple(match))
            membership[x]=orbit_index
            orbit_masses[orbit_index]+=weight
        after,maxima,rows=all_height_queries(bs,primes,ee,live,orbit_masses)
        before=F(0)
        for levels in product(*(range(e+1) for e in ee)):
            modulus=3**levels[0]*5**levels[1]
            old=defaultdict(F)
            averaged=defaultdict(F)
            for x,weight in raw.items():
                old[x%modulus]+=weight
                index=membership[x]
                averaged[x%modulus]+=orbit_masses[index]/(period*haar[index])
            old_max=max(old.values())
            require(maxima[levels]<=old_max,"every fixed numerical maximum contracts")
            require(max(averaged.values())==maxima[levels],"menu equals every literal phase maximum")
            fee=F(1)
            for k,p in enumerate(primes):
                if levels[k]==ee[k]:
                    fee*=F(p,p-1)
            before+=fee*old_max
        require(after<=before,"complete Euler-weighted response contracts")
        results.append(dict(n=n,period=period,survivors=len(survivors),
                            joint_orbits=len(live),phase_rows=rows,
                            B_before=str(before),B_after=str(after)))
    return results

def run(input_path):
    global CHECKS
    CHECKS=0
    raw=input_path.read_bytes()
    data=json.loads(raw)
    require(data['schema']=='actual-prefix-orbit-certificate-v1',"certificate schema")
    primes=tuple(integer(p) for p in data['primes'])
    require(tuple(sorted(set(primes)))==primes,"distinct increasing prime list")
    require(all(is_prime(p) and p>2 for p in primes),"odd prime list")
    family=[(integer(m),integer(a)) for m,a in data['originals']]
    require(len({m for m,_ in family})==len(family),"distinct original numerical labels")
    require(all(m>1 and m%2 and 0<=a<m for m,a in family),"literal original ranges")
    n=integer(data['example']['depth'])
    require(data['example']['name']=='report535-two-chain',"declared example")
    require(family==two_chain(n),"complete original family reconstructed from stated construction")
    active=tuple(p for p in primes if any(m%p==0 for m,_ in family))
    free=tuple(p for p in primes if p not in active)
    buckets,nodes,levels,live,haar=build(family,active)
    actual_buckets=[{'prime':p,'buckets':[{'depth':e,'prefixes':[str(r) for r in rs]} for e,rs in bs]} for p,bs in zip(active,buckets)]
    require(actual_buckets==data['coordinate_buckets'],"literal coordinate orbit descriptors")
    require(live==[tuple(map(integer,x)) for x in data['joint_orbit_indices']],"canonical actual orbit order")
    denominator=integer(data['mass_denominator'])
    require(denominator>0,"positive mass denominator")
    nums=[integer(x) for x in data['mass_numerators']]
    require(len(nums)==len(live) and all(x>=0 for x in nums),"source mass vector")
    require(sum(nums)==denominator,"exact unit mass")
    masses=[F(x,denominator) for x in nums]
    cap=F(data['haar_density_cap'])
    require(cap>0 and all(m<=cap*h for m,h in zip(masses,haar)),"one exact Haar density cap")
    density=sum(haar,F(0))
    require(density==F(13,30)+F(1,2*3**n),"complete two-chain survivor density")
    unit_B,maxima,rows=all_height_queries(buckets,active,levels,live,masses)
    uniform_B,_,uniform_rows=all_height_queries(buckets,active,levels,live,[h/density for h in haar])
    euler=F(1)
    for p in free:
        euler*=F(p,p-1)
    B=unit_B*euler
    uniform_B*=euler
    require(B<uniform_B,"exact common-source improvement over full survivor Haar")
    require(B<28,"B including numerical label1 below28 in this example")
    period=1
    for p,e in zip(active,levels):period*=p**e
    controls=dense_controls()
    result=dict(schema='actual-prefix-orbit-query-v1',status='PASS',
                source_sha256=sha256(raw).hexdigest(),
                scope='Exact fixed-family source representation and witness; no uniform B<28 theorem or unrestricted covering result; no Lean verification',
                primes=list(primes),active_primes=list(active),free_primes=list(free),
                original_count=len(family),maximal_original_exponents=levels,
                complete_period=str(period),actual_survivor_residues=str(density*period),
                local_trie_nodes=nodes,local_orbit_counts=list(map(len,buckets)),
                joint_source_orbits=len(live),positive_source_orbits=sum(x>0 for x in nums),
                numerical_query_slots=len(maxima),literal_coefficient_rows=rows,
                haar_survivor_density=str(density),source_haar_density_cap=str(cap),
                uniform_source_B=str(uniform_B),certificate_B=str(B),certificate_R=str(B-1),
                strict_improvement=str(uniform_B-B),
                complete_tail='q_d=(gcd(d,L)/d)q_gcd(d,L); sum_g w_g q_g, including g=1',
                scipy_used=False,lp_optimality_claimed=False,full_deep_carrier_enumerated=False,
                dense_controls=controls,checks=CHECKS)
    require(rows==uniform_rows,"one shared complete query menu")
    result['checks']=CHECKS
    return result

def main():
    here=Path(__file__).resolve().parent
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--input',type=Path,default=here/'actual_prefix_orbit_query_certificate.json')
    parser.add_argument('--expected',type=Path,default=here/'actual_prefix_orbit_query.json')
    parser.add_argument('--write-result',type=Path)
    args=parser.parse_args()
    result=run(args.input)
    if args.write_result:
        args.write_result.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    else:
        require(json.loads(args.expected.read_text())==result,"retained result equals full exact replay")
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__':main()
