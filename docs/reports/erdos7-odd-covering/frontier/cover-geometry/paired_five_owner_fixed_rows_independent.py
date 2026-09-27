#!/usr/bin/env python3
"""Independent exact audit: no candidate code imports or execution.

Direct divisor convolution constructs the actual four-block pair product law.
Old noncanonical coverage uses the five-candidate analytic exchange reduction
from the fixed-witness exchanges of Report655, not candidate branch fee implementations.
"""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
from functools import lru_cache
from collections import Counter
import hashlib
import json
import math
import sys
import argparse

sys.set_int_max_str_digits(0)
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent,
                    help='Directory containing the fixed named producer/result and pinned inputs.')
parser.add_argument('--output',type=Path,
                    help='Optional result JSON path; default is the independent result in --directory.')
args=parser.parse_args()
BASE=args.directory.resolve()
CANDIDATE=BASE/'paired_five_owner_fixed_rows_certificate.json'
PRODUCER=BASE/'paired_five_owner_fixed_rows_certificate.py'
OUT=args.output if args.output is not None else BASE/'paired_five_owner_fixed_rows_independent.json'
checks=Counter()
def ck(name, condition):
    checks[name]+=1
    if not condition: raise AssertionError(name)
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def load(name): return json.loads((BASE/name).read_text())
def compact(obj): return json.dumps(obj,sort_keys=True,separators=(',',':')).encode()
def enc(x):
    if isinstance(x,F): return str(x)
    if isinstance(x,dict): return {str(k):enc(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)): return [enc(v) for v in x]
    return x
def progress(s): print(s,flush=True)

c=json.loads(CANDIDATE.read_text())
fixed=load('four_parent_tail_fixed_schedule.json')
domain=load('ordinary_domain_five_parent_certificate.json')
four=load('paired_owner_fixed_rows_certificate.json')
for name,digest in c['input_sha256'].items(): ck('input fingerprint',sha(BASE/name)==digest)
ck('producer fingerprint bytes only',sha(PRODUCER)==c['program_sha256'])
ck('candidate scope',c['schema']=='paired-five-owner-fixed-row-certificate-v1' and not c['new_lean_verification'])
rows=c['rows']; n=len(rows)
primes=[v for v in range(37,1253) if all(v%p for p in range(2,math.isqrt(v)+1))]
ck('193 complete owner rows',n==193 and [r['owner'] for r in rows]==primes)
for r,f,d,old4 in zip(rows,fixed['rows'],domain['finite_rows'],four['rows']):
    v,h=r['owner'],r['h']
    ck('unchanged row',v==f['owner']==d['owner']==old4['owner'] and h==f['h']==d['h']==old4['h'])
    ck('actual cap',F(r['cap'])==F(v-1,h)==F(f['cap'])==F(d['cap'])==F(old4['cap']) and F(v-1,h*v)<F(1,10))
    ck('actual threshold',F(r['threshold'])==F(v-2)-F(1,65536)-h==F(f['threshold'])==F(d['t']))
    ck('hinge shift',F(r['s'])==F(r['threshold'])+1)
N=max(math.ceil(F(r['s'])) for r in rows)
ck('finite negative support envelope',N==c['finite_negative_part_endpoint']==1080)

Q=(7,11,13,17,19)
D={q:F(5,6) if q==7 else 1-F(1,q-1)-F(2,q*(q-2)) for q in Q}
edge={(p,q):F(1,p*(p-2)*(q-1))+F(1,(p-1)*q*(q-2)) for p,q in combinations(Q,2)}
# Enumerate all matchings explicitly, independently of the producer recurrence.
def polynomial(vertices):
    es=list(combinations(vertices,2)); total=F(0)
    for k in range(len(vertices)//2+1):
        for picked in combinations(es,k):
            used=[v for e in picked for v in e]
            if len(set(used))!=2*k: continue
            term=F((-1)**k)
            for e in picked: term*=edge[e]
            for v in vertices:
                if v not in used: term*=D[v]
            total+=term
    return total
R=[polynomial(tuple(q for q in Q if q not in S)) for S in ({13},{7,13},{11,13},{7,11,13})]
ck('matching constants',list(map(str,R))==c['paired_response_constants'])
r0,r7,r11,r711=R
c00=r0-r7/6-r11/10+r711/60
c10=r7-r711/10
c01=r11-r711/6
c11=r711
ck('positive tau blocks',all(x>0 for x in (c00,c10,c01,c11)))
ck('tau coefficients',list(map(str,(c00,c10,c01,c11)))==c['tau_block_coefficients'])
mass=c00+c10/6+c01/10+c11/60
pairmean=c00+c10*(F(6,5)-F(5,6))+c01*(F(10,9)-F(9,10))+c11*(F(6,5)-F(5,6))*(F(10,9)-F(9,10))
mean=F(32,11)*pairmean
ck('complete mass mean',mass==r0==F(c['complete_tau_mass']) and mean==F(c['complete_product_mean']) and mean-mass==F(c['complete_count_mean']))

def tail(p,e):
    if e==0:return F(1)
    if p==3:return F(2,3**e)
    if p==5:return F(4,3*5**e)
    if p in Q:return F(1,p-1) if e==1 else F(1,(p-2)*p**(e-1))
    if p==23:return F(5,3*23**e)
    if p==29:return F(20,11*29**e)
    if p==31:return F(2,31**e)
    if p=='outside37':return F(1,10*37**(e-1))
    raise ValueError(p)
def ex(p):
    if p==3:return F(2)
    if p==5:return F(4,3)
    if p in Q:return F(p-1,p-2)
    if p==23:return 1+F(5,66)
    if p==29:return 1+F(20,308)
    if p==31:return 1+F(2,30)
    if p=='outside37':return 1+F(37,360)
@lru_cache(None)
def atoms(p):
    ts=[tail(p,k) for k in range(N+1)]
    v=[F(0)]+[ts[k-1]-ts[k] for k in range(1,N+1)]
    ck('positive reference atoms',all(x>0 for x in v[1:]))
    return v
def conv(a,b):
    # Accumulate by product output, visiting its ordered divisors.
    z=[F(0)]*(N+1)
    for k in range(1,N+1):
        val=F(0)
        for d in range(1,math.isqrt(k)+1):
            if k%d:continue
            e=k//d
            val+=a[d]*b[e]
            if d!=e:val+=a[e]*b[d]
        z[k]=val
    return z
def prod_dist(ps):
    z=[F(0)]*(N+1);z[1]=F(1)
    for p in ps:z=conv(z,atoms(p))
    return z
def fee_list(dist,fullmass,fullmean):
    prob=[F(0)]*(N+1); weighted=[F(0)]*(N+1)
    for k in range(1,N+1):
        prob[k]=prob[k-1]+dist[k]
        weighted[k]=weighted[k-1]+k*dist[k]
    ans=[]
    for row in rows:
        s=F(row['s']); k=math.ceil(s)-1
        ans.append((fullmean-s*fullmass+s*prob[k]-weighted[k])/row['h'])
    ck('positive complete hinges',all(x>0 for x in ans))
    return ans
def enclosed(x,row,lk,uk,name):ck(name,F(row[lk])<=x<=F(row[uk]))

progress('Constructing exact dependent pair product and central/reference convolution.')
pair=[F(0)]*(N+1)
for k in range(1,N+1):
    for i in range(1,k+1):
        if k%i:continue
        j=k//i
        pair[k]+=(c00 if i==j==1 else c10*atoms(7)[i] if j==1 else c01*atoms(11)[j] if i==1 else c11*atoms(7)[i]*atoms(11)[j])
paired_dist=conv(prod_dist((3,5,13)),pair)
paired=fee_list(paired_dist,mass,mean)
for x,row in zip(paired,rows):enclosed(x,row,'paired_lower','paired_upper','exact paired row enclosed')
phash=hashlib.sha256(compact(list(map(str,paired)))).hexdigest()
ck('exact paired fee fingerprint',phash==c['exact_canonical_row_fees_sha256'])
enclosed(sum(paired),c['canonical_total'],'lower','upper','exact paired total enclosed')
progress('All 193 exact paired hinges verified. Constructing old canonical and five runner candidates.')

base=prod_dist((3,5,7,11))
base_mean=math.prod(ex(p) for p in (3,5,7,11))
oldfees={}
for p in (13,17,23,29,31,'outside37'):
    zeta=math.prod(D[q] for q in Q if q not in (7,11,p))
    raw=fee_list(conv(base,atoms(p)),F(1),base_mean*ex(p))
    oldfees[p]=[zeta*x for x in raw]
    progress('Verified exact old comparison distribution '+str(p))
old=oldfees[13]
for x,row in zip(old,rows):enclosed(x,row,'old_canonical_lower','old_canonical_upper','exact old canonical enclosed')
ohash=hashlib.sha256(compact(list(map(str,old)))).hexdigest()
ck('exact old fee fingerprint',ohash==c['exact_old_five_row_fees_sha256'])
enclosed(sum(old),c['old_five_total'],'lower','upper','exact old total enclosed')
combined=[];exception=[];runner_types=Counter()
for idx,row in enumerate(rows):
    eligible=(17,23,29,31) if row['owner']==37 else (17,23,29,31,'outside37')
    p=max(eligible,key=lambda q:oldfees[q][idx])
    runner=oldfees[p][idx]
    typ={'head':[3,5,7,11,p],'outside_count':0} if p!='outside37' else {'head':[3,5,7,11],'outside_count':1}
    ck('analytic runner type',typ==row['maximizing_noncanonical_type'])
    enclosed(runner,row,'old_noncanonical_max_lower','old_noncanonical_max_upper','exact runner enclosed')
    maximum=max(paired[idx],runner)
    combined.append(maximum)
    enclosed(maximum,row,'combined_lower','combined_upper','exact allbranch maximum enclosed')
    ck('row improvement',maximum<old[idx])
    ck('five above inherited four',F(four['rows'][idx]['paired_upper'])<maximum)
    if runner>paired[idx]:exception.append(row['owner'])
    runner_types[str(p)]+=1
ck('unique owner41 exception',exception==[41]==c['exceptional_owners'])
ck('row winner counts',c['canonical_wins_rows']==192 and c['noncanonical_wins_rows']==1)
enclosed(sum(F(r['combined_upper']) for r in rows),c['allbranch_upper_total'],'lower','upper','published upper-total enclosure')
ck('exact combined total bounded',sum(combined)<=F(c['allbranch_upper_total']['upper']))

head=(3,5,7,11,13,17,19,23,29,31)
types={(tuple(s),5-k) for k in range(6) for s in combinations(head,k)}
published={(tuple(t['head']),t['outside_count']) for t in c['branch_census']}
ck('638 complete branch identities',len(types)==638 and published==types-{((3,5,7,11,13),0)})
counts=[]
for i,row in enumerate(rows):
    count=sum(l<=i for _,l in types)
    counts.append(count)
ck('all early eligibility counts',counts==c['branch_counts'])
for t in c['branch_census']:
    ck('branch eligible count',t['eligible_rows']==sum(t['outside_count']<=i for i in range(n)))

progress('Exact old runner fees and owner41 exception verified. Auditing unchanged-tail policies and all-pair fingerprints.')
gate=F(fixed['head_gate']);alpha=F(fixed['projection_alpha'])
W5=F(domain['complete_five_parent_tail']);typeI=F(domain['ordinary_typeI_fee'])
ck('unchanged tail constants',F(c['unchanged_five_parent_tail'])==W5==F(fixed['unchanged_five_parent_tail']) and F(c['unchanged_TypeI'])==typeI==F(fixed['unchanged_TypeI']))
ck('unchanged projection gate',F(c['head_gate'])==gate and F(c['projection_alpha'])==alpha)
ck('unchanged Euler counts',c['unchanged_Euler_counts']==domain['Euler_counts']==four['unchanged_Euler_counts'] and not c['all326_Euler_factors_changed'] and not c['actual_rows_reoptimized'])

def prefix(vals):
    z=[F(0)]
    for x in vals:z.append(z[-1]+x)
    return z
three=(prefix([F(r['three_lower']) for r in fixed['rows']]),prefix([F(r['three_upper']) for r in fixed['rows']]))
paired4=(prefix([F(r['paired_lower']) for r in four['rows']]),prefix([F(r['paired_upper']) for r in four['rows']]))
legacy4=(prefix([F(r['four_lower']) for r in fixed['rows']]),prefix([F(r['four_upper']) for r in fixed['rows']]))
new5=(prefix([F(r['combined_lower']) for r in rows]),prefix([F(r['combined_upper']) for r in rows]))
old5=(prefix([F(r['old_canonical_lower']) for r in rows]),prefix([F(r['old_canonical_upper']) for r in rows]))
cutoffs=primes+[1253];cutidx={v:i for i,v in enumerate(cutoffs)}
target=F(1,2000000)
policy_results=[]
for pol in c['policies']:
    orig=next(x for x in fixed['policies'] if x['kind']==pol['kind'])
    arb=F(orig['arbitrary_tail'])
    ck('unchanged arbitrary tail',arb==F(pol['unchanged_arbitrary_tail']))
    ck('unchanged switch',pol['final_switch_power']==orig['K'])
    budget=gate-W5-typeI-arb
    def reserves(i,j,p4=paired4,p5=new5):
        return tuple(alpha*(budget-(three[side][i]+p4[side][j]-p4[side][i]+p5[side][n]-p5[side][j])) for side in (1,0))
    stream=hashlib.sha256();success=[]
    for i in range(n+1):
        for j in range(i,n+1):
            lo,hi=reserves(i,j)
            stream.update((str(i)+':'+str(j)+':'+str(lo)+':'+str(hi)+'\n').encode())
            ck('allpair interval',lo<=hi)
            if lo>target:success.append((i,j))
    ck('allpair count',pol['all_cutoff_pair_count']==(n+1)*(n+2)//2==18915)
    ck('allpair fingerprint',stream.hexdigest()==pol['all_cutoff_pairs_sha256'])
    def verify_record(rec,p4=paired4,p5=new5):
        i,j=cutidx[rec['four_cutoff']],cutidx[rec['five_cutoff']]
        lo,hi=reserves(i,j,p4,p5)
        ck('policy exact endpoints',lo==F(rec['reserve_lower']) and hi==F(rec['reserve_upper']))
        ck('policy target',lo>target)
        if j>i:
            prev=reserves(i,j-1,p4,p5)[1]
            ck('previous cutoff minimality',prev<target and rec['previous_five_cutoff']==cutoffs[j-1] and F(rec['previous_reserve_upper'])==prev)
        return i,j
    fixedij=verify_record(pol['fixed_four_policy'])
    for rec in pol['baseline_policy_comparison']:
        name=rec['comparison']
        p4=legacy4 if name=='legacy666_four_and655_five' else paired4
        p5=new5 if name=='paired_four_andfive' else old5
        verify_record(rec,p4,p5)
    for rec in pol['direct_three_to_five']:
        k=cutidx[rec['cutoff']];lo,hi=reserves(k,k);tar=F(rec['target'])
        ck('direct policy endpoints',lo==F(rec['reserve_lower']) and hi==F(rec['reserve_upper']) and lo>tar)
        prev=reserves(k-1,k-1)[1]
        ck('direct policy predecessor',cutoffs[k-1]==rec['previous_cutoff'] and prev==F(rec['previous_upper']) and prev<tar)
    frontier=[];smallest_j=n+1
    for i,j in success:
        if j<smallest_j:
            frontier.append((i,j));smallest_j=j
    ck('complete Pareto frontier',frontier==[(cutidx[r['four_cutoff']],cutidx[r['five_cutoff']]) for r in pol['density_pareto_frontier']])
    for rec in pol['density_pareto_frontier']:verify_record(rec)
    policy_results.append({'kind':pol['kind'],'fixed_cutoffs':[cutoffs[x] for x in fixedij], 'allpair_sha256':stream.hexdigest(),'baseline_cutoffs':[[r['comparison'],r['four_cutoff'],r['five_cutoff']] for r in pol['baseline_policy_comparison']]})

result={
    'status':'PASS','scope':'Exact independent pair-product divisor convolution for193 hinges, old canonical and five analytic runner candidates; complete638 metadata plus ordinary exchange proof; unchanged-tail policy/fingerprint audit. Candidate producer was neither read as source nor imported/executed. No new seventh-moment tail audited.',
    'candidate_sha256':sha(CANDIDATE),'candidate_program_sha256':sha(PRODUCER),
    'program_sha256':sha(Path(__file__)),
    'paired_exact_sha256':phash,'old_exact_sha256':ohash,
    'exceptional_owners':exception,'runner_types':dict(runner_types),
    'paired_total_decimal':float(sum(paired)), 'combined_total_decimal':float(sum(combined)),
    'policies':policy_results,'checks':dict(checks),'check_count':sum(checks.values()),
}
OUT.write_text(json.dumps(enc(result),indent=2)+'\n')
progress(json.dumps(enc(result),indent=2))
