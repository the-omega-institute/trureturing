#!/usr/bin/env python3
"""Exact independent audit of the80 support-aware matching pair contexts."""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
from collections import Counter
import json
import argparse
import hashlib

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument("--directory",type=Path,default=Path(__file__).resolve().parent)
parser.add_argument("--output",type=Path,default=Path(__file__).with_suffix(".json"))
args=parser.parse_args()
candidate_path=args.directory/"support_aware_pair_exchange_certificate.json"
candidate=json.loads(candidate_path.read_text())

Q=(7,11,13,17,19)
D={q:F(5,6) if q==7 else 1-F(1,q-1)-F(2,q*(q-2)) for q in Q}
a={q:F(1,q-1) for q in Q}
b={(q,r):F(1,q*(q-2)*(r-1))+F(1,(q-1)*r*(r-2)) for q,r in combinations(Q,2)}
checks=Counter()
def ck(name,condition):
    checks[name]+=1
    if not condition:raise AssertionError(name)
def H(vs):
    total=F(0)
    for count in range(len(vs)//2+1):
        for es in combinations(tuple(combinations(vs,2)),count):
            used=[p for e in es for p in e]
            if len(set(used))<2*count:continue
            term=F((-1)**count)
            for e in es:term*=b[e]
            for p in vs:
                if p not in used:term*=D[p]
            total+=term
    return total
R={frozenset(T):H(tuple(q for q in Q if q not in T)) for k in range(6) for T in combinations(Q,k)}
def tau(P,K):
    q,r=P;K=frozenset(K)
    r0,rq,rr,rqr=(R[K|frozenset(S)] for S in ((),(q,),(r,),(q,r)))
    return rqr,rq-a[r]*rqr,rr-a[q]*rqr,r0-a[q]*rq-a[r]*rr+a[q]*a[r]*rqr
contexts={}
for P in combinations(Q,2):
    rest=tuple(p for p in Q if p not in P)
    for k in range(4):
        for K in combinations(rest,k):
            contexts[P,K]=tau(P,K)
            for x in contexts[P,K]:ck('positive block',x>0)
mins=[min((t[i],key) for key,t in contexts.items()) for i in range(4)]
expected=(F(77690927,118918800),F(17004889549,29631167280),F(175232434423,363891528000),F(84106036967663,211566534379200))
ck('reported coefficient minima',tuple(x[0] for x in mins)==expected)
ratios={}
max_ratios={}
ratio_count=0
for p in Q:
    candidates=[]
    for (P,K),blocks in contexts.items():
        if p not in K:continue
        shrunk=contexts[P,tuple(q for q in K if q!=p)]
        for i in range(4):
            ratio=shrunk[i]/blocks[i]
            ck('lower unquery contraction',ratio>=F(4,5) if p==7 else ratio>=F(5,6))
            ck('upper unquery contraction',ratio<=D[p])
            ratio_count+=1
            candidates.append((ratio,P,K,i))
    ratios[p]=min(candidates)
    max_ratios[p]=max(candidates)
ck('reported delta7',ratios[7][0]==F(1915424773533541,2340864476042190))
ck('reported delta11 minimum',min(ratios[p][0] for p in Q if p!=7)==F(574546060482833,661191624184410))
single={p:R[frozenset()]-a[p]*R[frozenset((p,))] for p in Q}
for x in single.values():ck('positive single-coordinate zero atom',x>0)

# The only infinite part of these comparisons propagates by the prime ratio.
for p in Q:
    ck('3 weighted mean',F(4,5)*2>=F(p-1,p-2))
    ck('3 weighted first depth',F(4,5)*F(2,3)>=a[p])
    ck('3 weighted second depth',F(4,5)*F(2,9)>=F(1,(p-2)*p))
    if p>=11:
        ck('5 weighted mean',F(5,6)*F(4,3)>=F(p-1,p-2))
        ck('5 weighted first depth',F(5,6)*F(4,15)>=a[p])
        ck('5 weighted second depth',F(5,6)*F(4,75)>=F(1,(p-2)*p))

r0,r7,r11,r711=(R[frozenset(S)] for S in ((),(7,),(11,),(7,11)))
canonical_product=F(8,3)*(r0+r7/5+r11/9+r711/45)
scalar_product=R[frozenset((7,13))]*F(8,3)*F(6,5)*F(12,11)
wrong_atomwise_delta=tau((7,11),())[3]-r0*F(9,10)**2
ck('atomwise later-replacement counterexample',wrong_atomwise_delta<0)
ck('arbitrary Q tail replacement counterexample',F(1,10)>a[13])
def product_mean(P,K,central_factor):
    q,r=P;t11,t10,t01,t00=tau(P,K)
    mq=F(q-1,q-2);mr=F(r-1,r-2)
    pq=mq-(1-a[q]);pr=mr-(1-a[r])
    ans=central_factor*(t00+t10*pq+t01*pr+t11*pq*pr)
    for p in K:ans*=F(p-1,p-2)
    return ans
wrong_five=product_mean((11,13),(7,),F(8,3))
canonical_five=product_mean((7,11),(13,),F(8,3))
wrong_five_gap=wrong_five-canonical_five
wrong_count_gap=wrong_five-R[frozenset((7,))]-canonical_five+R[frozenset((13,))]
ck('wrong five partition product counterexample',wrong_five_gap==F(372464259439,2260326222000)>0)
ck('wrong five partition count counterexample',wrong_count_gap==F(150250149338951,1410443562528000)>0)

ck('candidate schema',candidate['schema']=='support-aware-pair-exchange-certificate-v1' and not candidate['new_lean_verification'])
ck('fixed Q',candidate['Q']==list(Q))
ck('unary masses',candidate['unary_masses']=={str(q):str(D[q]) for q in Q})
ck('first caps',candidate['pair_first_caps']=={str(q):str(a[q]) for q in Q})
responses=[{'queried':list(T),'response':str(R[frozenset(T)])} for k in range(6) for T in combinations(Q,k)]
ck('all32 independent responses',responses==candidate['responses'])
for T,value in R.items():
    ck('positive source response',value>0)
    for p in Q:
        if p not in T:ck('query monotonicity',R[T|{p}]>value)
context_rows=[{'pair':list(P),'retained':list(K),'coefficients_pp_p0_0p_00':list(map(str,t))} for (P,K),t in contexts.items()]
ck('all80 independent contexts',context_rows==candidate['contexts'])
context_hash=hashlib.sha256(json.dumps(context_rows,sort_keys=True,separators=(',',':')).encode()).hexdigest()
ck('context fingerprint',context_hash==candidate['contexts_sha256'])
ck('480 ratio count',ratio_count==480==candidate['contraction_ratio_count'])
labels=('++','+0','0+','00')
minimum_records={}
for i,label in enumerate(labels):
    val,(P,K)=mins[i]
    minimum_records[label]={'value':str(val),'pair':list(P),'retained':list(K)}
ck('all block minimum records',minimum_records==candidate['block_minima'])
def ratio_record(data):
    value,P,K,i=data
    return {'value':str(value),'pair':list(P),'retained':list(K),'block':labels[i]}
min_records={str(p):ratio_record(ratios[p]) for p in Q}
max_records={str(p):ratio_record(max_ratios[p]) for p in Q}
ck('all contraction minima',min_records==candidate['contraction_minima'])
ck('all contraction maxima',max_records==candidate['contraction_maxima'])
for (P,K),(pp,p0,op,oo) in contexts.items():
    q,r=P;K=frozenset(K)
    ck('pair total identity',oo+a[q]*p0+a[r]*op+a[q]*a[r]*pp==R[K])
    ck('pair first tail identity',p0+a[r]*pp==R[K|{q}])
    ck('pair second tail identity',op+a[q]*pp==R[K|{r}])
# Fixed actual references remain unchanged in the source counterexample.
source_gap=r0-R[frozenset((13,))]/12
smaller_pair_atom_drop=tau((7,13),())[3]-tau((7,11),())[3]
ck('same-reference13 cylinder counterexample',source_gap==F(270508276995713,528916335948000)>0)
ck('canonical four counterexample source bounds',all(r0<=R[frozenset(T)] for T in ((),(7,),(11,),(7,11))))
ck('smaller pair atom counterexample',smaller_pair_atom_drop==F(343119356159,34969675104000)>0)
reported_facts={
 'wrong_pair_product_first_moment':wrong_five,
 'canonical_product_first_moment':canonical_five,
 'wrong_pair_product_gap':wrong_five_gap,
 'wrong_pair_owner_count_hinge_gap':wrong_count_gap,
 'smaller_pair_zero_zero_atom_decrease':smaller_pair_atom_drop,
 'four_response_source_retained13_event_mass_cap':F(1,12),
 'four_response_source_retained13_event_excess_at_cap':source_gap,
 'outside37_first_tail':F(1,10),
 'X13_first_tail':F(1,12),
}
ck('all candidate counterexample facts',{k:str(v) for k,v in reported_facts.items()}==candidate['counterexamples'])
ck('unquery constants not ordered',R[frozenset((13,))]>R[frozenset()])
ck('adaptive branch maximum counterexample',F(3,4)>F(1,2))

def enc(v):
    if isinstance(v,F):return str(v)
    if isinstance(v,dict):return {str(k):enc(x) for k,x in v.items()}
    if isinstance(v,(list,tuple)):return [enc(x) for x in v]
    return v
result={
 'status':'PASS','new_lean_verification':False,
 'scope':'Independent explicit matching enumeration validates all32 responses,80 positive contexts,480 lower and upper contractions, activation identities and fixed-reference counterexamples. Candidate producer was not opened or imported; its hash below is a claim from the pinned candidate JSON. The ordinary same-source theorem is separate from these finite checks.',
 'candidate_sha256':hashlib.sha256(candidate_path.read_bytes()).hexdigest(),
 'candidate_program_sha256_claim':candidate['program_sha256'],
 'program_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'responses':responses,'contexts':context_rows,'contexts_sha256':context_hash,
 'block_minima':minimum_records,'contraction_minima':min_records,'contraction_maxima':max_records,
 'counterexamples':reported_facts,'additional_counterexamples':{
    'new_pair_zero_atom_minus_double_outside_zero_atom':wrong_atomwise_delta,
    'old_scalar_minus_canonical_product_mean':scalar_product-canonical_product,
    'old_scalar_minus_canonical_count_mean':scalar_product-R[frozenset((7,13))]-canonical_product+r0},
 'checks':dict(checks),'check_count':sum(checks.values())}
args.output.write_text(json.dumps(enc(result),indent=2)+'\n')
print(json.dumps({'status':result['status'],'check_count':result['check_count'],'contexts_sha256':context_hash,'output':str(args.output)},sort_keys=True))
