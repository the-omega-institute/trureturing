#!/usr/bin/env python3
"""Independent complete-moment and fixed-policy audit; candidate JSON only.

Geometric raw moments are rebuilt from factorial moments and Stirling numbers,
using the exact mixture X=1, X=2, X=3+Geom0. No candidate producer is opened,
imported, or executed. All checks remain active with Python -O.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import hashlib
import json
import math
import sys

sys.set_int_max_str_digits(0)
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
parser.add_argument('--output',type=Path)
args=parser.parse_args()
BASE=args.directory.resolve()
candidate=BASE/'paired_five_owner_prime_tail_certificate.json'
output=args.output if args.output is not None else BASE/'paired_five_owner_prime_tail_independent.json'
checks=Counter()
def ck(name,condition):
    checks[name]+=1
    if not condition:raise AssertionError(name)
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def compact(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def read(name):return json.loads((BASE/name).read_text())
def enc(x):
    if isinstance(x,F):return str(x)
    if isinstance(x,dict):return {str(k):enc(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [enc(v) for v in x]
    return x
def enclosure(name,x,record):ck(name,F(record['lower'])<=x<=F(record['upper']))

c=json.loads(candidate.read_text())
fixed=read('four_parent_tail_fixed_schedule.json')
domain=read('ordinary_domain_five_parent_certificate.json')
four=read('paired_owner_fixed_rows_certificate.json')
five=read('paired_five_owner_fixed_rows_certificate.json')
ck('schema scope',c['schema']=='paired-five-owner-prime-tail-certificate-v1' and c['new_lean_verification'] is False)
for name,digest in c['input_sha256'].items():ck('input SHA256',sha(BASE/name)==digest)
primes=[p for p in range(37,1253) if all(p%d for d in range(2,math.isqrt(p)+1))]
n=len(primes)
ck('193 complete finite rows',n==193==c['finite_row_count'] and [r['owner'] for r in five['rows']]==primes)
for a,b,d,e in zip(five['rows'],four['rows'],fixed['rows'],domain['finite_rows']):
    p,h=a['owner'],a['h']
    ck('fixed row identity',p==b['owner']==d['owner']==e['owner'] and h==b['h']==d['h']==e['h'])
    ck('fixed full-history caps',F(a['cap'])==F(b['cap'])==F(d['cap'])==F(e['cap'])==F(p-1,h) and F(p-1,p*h)<F(1,10))
    ck('fixed thresholds',F(a['threshold'])==F(d['threshold'])==F(e['t'])==F(p-2)-F(1,65536)-h and F(a['s'])==F(b['s'])==F(a['threshold'])+1)
ck('no row or Euler change',not c['actual_rows_reoptimized'] and not c['all326_Euler_factors_changed'] and c['unchanged_Euler_counts']==domain['Euler_counts']==five['unchanged_Euler_counts'])

Q=(7,11,13,17,19)
head=(3,5,7,11,13,17,19,23,29,31)
outside=(37,41,43,47,53)
D={q:F(5,6) if q==7 else 1-F(1,q-1)-F(2,q*(q-2)) for q in Q}
edges={(q,s):F(1,q*(q-2)*(s-1))+F(1,(q-1)*s*(s-2)) for q,s in combinations(Q,2)}
def matching(vs):
    total=F(0)
    for count in range(len(vs)//2+1):
        for es in combinations(tuple(combinations(vs,2)),count):
            occupied=[p for edge in es for p in edge]
            if len(set(occupied))!=2*count:continue
            term=F((-1)**count)
            for edge in es:term*=edges[edge]
            for p in vs:
                if p not in occupied:term*=D[p]
            total+=term
    return total
R=[matching(tuple(q for q in Q if q not in s)) for s in ({13},{7,13},{11,13},{7,11,13})]
r0,r7,r11,r711=R
tau=(r0-r7/6-r11/10+r711/60,r7-r711/10,r11-r711/6,r711)
ck('independent matching responses',list(map(str,R))==c['paired_response_constants']==five['paired_response_constants'])
ck('independent positive tau',all(t>0 for t in tau) and list(map(str,tau))==c['tau_block_coefficients']==five['tau_block_coefficients'])

# Stirling numbers: G has factorial moment k!/(p-1)^k.
stirling=[[0]*8 for _ in range(8)]
stirling[0][0]=1
for j in range(1,8):
    for k in range(1,j+1):stirling[j][k]=stirling[j-1][k-1]+k*stirling[j-1][k]
def moments(p,kappa,deep):
    geom=[sum(F(stirling[j][k]*math.factorial(k),(p-1)**k) for k in range(j+1)) for j in range(8)]
    weights=(1-kappa,kappa-deep/F(p*p),deep/F(p*p))
    ck('complete geometric mixture',all(w>=0 for w in weights) and sum(weights)==1)
    result=[]
    for j in range(8):
        shifted=sum(math.comb(j,k)*3**(j-k)*geom[k] for k in range(j+1))
        result.append(weights[0]+weights[1]*2**j+weights[2]*shifted)
    ck('positive moments',result[0]==1 and all(result[i]<result[i+1] for i in range(7)))
    return result
def law(p):
    if p==3:return F(2,3),F(2)
    if p==5:return F(4,15),F(4,3)
    if p in Q:return F(1,p-1),F(p,p-2)
    if p==23:return F(5,69),F(5,3)
    if p==29:return F(20,319),F(20,11)
    if p==31:return F(2,31),F(2)
    if p in outside:return F(1,10),F(p,10)
    raise ValueError(p)
mus={}
for p in head+outside:
    kappa,deep=law(p)
    mus[p]=moments(p,kappa,deep)
    record=c['coordinate_laws'][str(p)]
    ck('coordinate law formula',F(record['first_cap'])==kappa and F(record['deep_multiplier'])==deep)
    ck('all coordinate moments',list(map(str,mus[p]))==record['moments0to7'])

c00,c10,c01,c11=tau
pair_product=[]
for j in range(8):
    pos7=mus[7][j]-F(5,6);pos11=mus[11][j]-F(9,10)
    pairmoment=c00+c10*pos7+c01*pos11+c11*pos7*pos11
    pair_product.append(mus[3][j]*mus[5][j]*mus[13][j]*pairmoment)
ck('all paired product moments',list(map(str,pair_product))==c['paired_product_moments0to7'])
ck('unnormalized mass and mean',pair_product[0]==r0==F(five['complete_tau_mass']) and pair_product[1]==F(five['complete_product_mean']) and pair_product[1]-pair_product[0]==F(five['complete_count_mean']))
def centered7(product_moments):return sum((-1)**(7-j)*math.comb(7,j)*product_moments[j] for j in range(8))
paired7=centered7(pair_product)
ck('exact paired count moment',paired7==F(c['paired_count_moment7']) and paired7>0)

branches=[];oldcanonical=None;noncanonical=[]
for k in range(6):
    for selected in combinations(head,k):
        l=5-k
        zeta=math.prod(D[q] for q in Q if q not in selected)
        role_ids=selected+outside[:l]
        old=zeta*centered7([math.prod(mus[p][j] for p in role_ids) for j in range(8)])
        canon=selected==(3,5,7,11,13) and l==0
        adopted=paired7 if canon else old
        method='paired' if canon else 'old-product-omitted-mass'
        if canon:oldcanonical=old
        else:noncanonical.append((old,selected,l))
        ck('positive branch moment',old>0 and adopted>0)
        branches.append({'head':list(selected),'outside_count':l,'old_count_moment7':str(old),'adopted_count_moment7':str(adopted),'method':method})
ck('638 reconstructed branches',len(branches)==638)
# Compare mathematical fields individually; candidate method spelling is metadata.
for actual,reported in zip(branches,c['branch_census']):
    ck('branch moment and identity',all(actual[k]==reported[k] for k in ('head','outside_count','old_count_moment7','adopted_count_moment7')))
    ck('branch method',actual['method']==reported['method'])
branchhash=hashlib.sha256(compact(branches)).hexdigest()
ck('all638 branch fingerprint',branchhash==c['all638_branch_moments_sha256'])
runner,runnerhead,runneroutside=max(noncanonical)
ck('old canonical complete moment',oldcanonical==F(c['old_canonical_count_moment7']) and oldcanonical>paired7)
ck('noncanonical runner',runner==F(c['old_noncanonical_max_count_moment7']) and list(runnerhead)==c['old_noncanonical_max_type']['head'] and runneroutside==c['old_noncanonical_max_type']['outside_count'])
ck('all637 below new canonical',len(noncanonical)==637 and all(x[0]<paired7 for x in noncanonical))
Mstar=max(F(b['adopted_count_moment7']) for b in branches)
ck('complete allbranch moment',Mstar==paired7==F(c['allbranch_count_moment7']))

generic13=moments(13,F(1,10),F(13,10))
generic7=centered7([mus[3][j]*mus[5][j]*mus[7][j]*mus[11][j]*generic13[j] for j in range(8)])
ck('inherited generic full moment',generic7==F(c['old_generic_count_moment7'])==F(domain['complete_fifth_role_count_moment7']))
A7=F(2**7*6**6,7**7)
den=6*1249**6
Wold=A7*generic7/den
Wpairedinteger=A7*Mstar/den
ck('sharp scalar coefficient',A7==F(c['sharp_halfrow_constant7'])==F(domain['sharp_halfrow_constant7']) and A7*F(7,12)**7==F(1,6))
ck('original tail start',c['tail_start']==1253)
ck('halfrow cap at smallest padded argument',F(2*(1253-1),1253*(1253-3))<F(1,10))
ck('same actual halfrow declaration',c['actual_tail_row']=='N=0 relative half threshold; c_v=2(v-1)/(v-3)' and c['owner_tail_fee']=='A7*M7/(v-3)^7')
ck('old tail reconstructed',Wold==F(c['old_complete_five_parent_tail'])==F(domain['complete_five_parent_tail'])==F(five['unchanged_five_parent_tail']))
ck('paired integer baseline',Wpairedinteger==F(c['paired_integer_tail_baseline']))

# Independent trial division, rather than the producer's sieve.
tail_primes=[p for p in range(1253,10000) if all(p%d for d in range(2,math.isqrt(p)+1))]
ck('exact prime window',c['prime_window_end_exclusive']==10000 and c['finite_prime_count']==1025==len(tail_primes) and tail_primes==c['finite_prime_values'])
scale=int(c['prime_rounding_scale'])
ck('directed prime scale',scale==10**90)
terms=[]; exact_scalar=F(0)
for p in tail_primes:
    q=(p-3)**7
    lo=scale//q;hi=(scale+q-1)//q
    terms.append((p,lo,hi));exact_scalar+=F(1,q)
    ck('each directed prime term',F(lo,scale)<=F(1,q)<=F(hi,scale) and hi-lo<=1)
termhash=hashlib.sha256(compact(terms)).hexdigest()
ck('finite prime term fingerprint',termhash==c['finite_prime_terms_sha256'])
Slo=F(sum(t[1] for t in terms),scale);Shi=F(sum(t[2] for t in terms),scale)
ck('finite prime interval endpoints',Slo==F(c['finite_prime_scalar_lower']) and Shi==F(c['finite_prime_scalar_upper']))
ck('finite prime interval against exact sum',Slo<=exact_scalar<=Shi)
residual=F(1,12*9996**6)
ck('odd integral residual',c['odd_remainder_first_integer']==10001 and residual==F(c['odd_remainder_scalar_upper']))
Flo,Fhi=Slo+residual,Shi+residual
ck('constructed scalar interval',Flo==F(c['complete_scalar_upper_expression_lower']) and Fhi==F(c['complete_scalar_upper_expression_upper']))
def floorq(x):return F((x.numerator*scale)//x.denominator,scale)
def ceilq(x):return F((x.numerator*scale+x.denominator-1)//x.denominator,scale)
def prime_tail_interval(moment):return floorq(A7*moment*Flo),ceilq(A7*moment*Fhi)
Wnew=prime_tail_interval(Mstar)
exact_constructed_new=A7*Mstar*(exact_scalar+residual)
ck('new tail interval reconstruction',Wnew==(F(c['new_complete_five_parent_tail_lower']),F(c['new_complete_five_parent_tail_upper'])) and 0<Wnew[0]<=exact_constructed_new<=Wnew[1]<Wpairedinteger<Wold)
gate=F(fixed['head_gate']);alpha=F(fixed['projection_alpha']);typeI=F(fixed['unchanged_TypeI'])
ck('same gate projection TypeI',gate==F(c['head_gate']) and alpha==F(c['projection_alpha']) and typeI==F(c['unchanged_TypeI']))
enclosure('exact constructed tail saving',Wold-exact_constructed_new,c['tail_saving'])
enclosure('exact constructed fractional reduction',(Wold-exact_constructed_new)/Wold,c['fractional_tail_reduction'])
enclosure('exact constructed projected gain',alpha*(Wold-exact_constructed_new),c['constant_projected_reserve_gain'])
print('All638 moments,1025 trial-division primes, exact finite sum and odd residual verified.',flush=True)

def prefix(xs):
    out=[F(0)]
    for x in xs:out.append(out[-1]+x)
    return out
p3=(prefix([F(r['three_lower']) for r in fixed['rows']]),prefix([F(r['three_upper']) for r in fixed['rows']]))
p4=(prefix([F(r['paired_lower']) for r in four['rows']]),prefix([F(r['paired_upper']) for r in four['rows']]))
p5=(prefix([F(r['combined_lower']) for r in five['rows']]),prefix([F(r['combined_upper']) for r in five['rows']]))
cutoffs=primes+[1253];index={p:i for i,p in enumerate(cutoffs)};target=F(1,2000000)
policy_results=[]
for policy in c['policies']:
    prior=next(p for p in five['policies'] if p['kind']==policy['kind'])
    inherited=next(p for p in fixed['policies'] if p['kind']==policy['kind'])
    arb=F(inherited['arbitrary_tail'])
    ck('arbitrary tail and switch unchanged',arb==F(policy['unchanged_arbitrary_tail'])==F(prior['unchanged_arbitrary_tail']) and policy['final_switch_power']==prior['final_switch_power']==inherited['K'])
    def reserves(i,j,tail=Wnew):
        if isinstance(tail,F):tail=(tail,tail)
        return tuple(alpha*(gate-tail[s]-typeI-arb-(p3[s][i]+p4[s][j]-p4[s][i]+p5[s][n]-p5[s][j])) for s in (1,0))
    successes=[];digest=hashlib.sha256()
    for i in range(n+1):
        for j in range(i,n+1):
            lo,hi=reserves(i,j)
            digest.update((str(i)+':'+str(j)+':'+str(lo)+':'+str(hi)+'\n').encode())
            ck('policy interval ordered',lo<=hi)
            ck('density threshold separated',hi<target or lo>target)
            ck('positivity threshold separated',hi<0 or lo>0)
            if lo>target:successes.append((i,j))
    ck('18915 complete cutoff pairs',policy['all_cutoff_pair_count']==18915==(n+1)*(n+2)//2)
    ck('allpair policy fingerprint',digest.hexdigest()==policy['all_cutoff_pairs_sha256'])
    def verify(rec):
        i,j=index[rec['four_cutoff']],index[rec['five_cutoff']]
        lo,hi=reserves(i,j)
        ck('displayed policy endpoints',lo==F(rec['reserve_lower']) and hi==F(rec['reserve_upper']) and lo>target)
        if j>i:
            prev=reserves(i,j-1)[1]
            ck('displayed predecessor failure',rec['previous_five_cutoff']==cutoffs[j-1] and prev==F(rec['previous_reserve_upper']) and prev<target)
        return i,j
    i,j=verify(policy['fixed_four_policy'])
    ck('finite role row counts',policy['finite_row_counts']=={'three':i,'four':j-i,'five':n-j})
    prevpolicy=prior['fixed_four_policy']
    oldj=index[prevpolicy['five_cutoff']]
    ck('inherited cutoff identity',prevpolicy['four_cutoff']==cutoffs[i] and policy['old_five_cutoff']==cutoffs[oldj])
    oldlo,oldhi=reserves(i,oldj,Wold)
    ck('reproduce old complete policy',oldlo==F(prevpolicy['reserve_lower']) and oldhi==F(prevpolicy['reserve_upper']))
    oldatnew=reserves(i,j,Wold)[1]
    ck('new cutoff failed with old tail',oldatnew==F(policy['old_tail_reserve_at_new_cutoff_upper']) and oldatnew<target)
    for rec in policy['direct_three_to_five']:
        k=index[rec['cutoff']];lo,hi=reserves(k,k);tar=F(rec['target'])
        ck('direct policy interval',lo==F(rec['reserve_lower']) and hi==F(rec['reserve_upper']) and lo>tar)
        prev=reserves(k-1,k-1)[1]
        ck('direct predecessor',rec['previous_cutoff']==cutoffs[k-1] and F(rec['previous_upper'])==prev and prev<tar)
    frontier=[];bestj=n+1
    for pair in successes:
        if pair[1]<bestj:frontier.append(pair);bestj=pair[1]
    ck('entire Pareto frontier',frontier==[(index[r['four_cutoff']],index[r['five_cutoff']]) for r in policy['density_pareto_frontier']])
    for rec in policy['density_pareto_frontier']:verify(rec)
    variants={
        'inherited_generic_integer_tail':(Wold,Wold),
        'paired_integer_tail':(Wpairedinteger,Wpairedinteger),
        'old_generic_prime_tail':prime_tail_interval(generic7),
        'old_canonical_prime_tail':prime_tail_interval(oldcanonical),
        'paired_prime_tail':Wnew,
    }
    attribution=[]
    for rec in policy['attribution']:
        tail=variants[rec['comparison']]
        ck('attribution tail endpoints',tail==(F(rec['tail_lower']),F(rec['tail_upper'])))
        k=next(k for k in range(i,n+1) if reserves(i,k,tail)[0]>target)
        lo,hi=reserves(i,k,tail)
        ck('attribution cutoff and reserve',cutoffs[k]==rec['five_cutoff'] and lo==F(rec['reserve_lower']) and hi==F(rec['reserve_upper']))
        prev=reserves(i,k-1,tail)[1]
        ck('attribution predecessor',prev<target and prev==F(rec['previous_reserve_upper']) and cutoffs[k-1]==rec['previous_five_cutoff'])
        attribution.append([rec['comparison'],cutoffs[k]])
    # Optimistic test: use the raw finite-prefix LOWER charge and remove all residual.
    zero_residual=(A7*Mstar*Slo,A7*Mstar*Slo)
    optimistic=reserves(i,j-1,zero_residual)[1]
    ck('zero residual still misses previous cutoff',optimistic==F(policy['preceding_cutoff_zero_residual_reserve_upper']) and optimistic<target)
    ck('prime scalar alone reaches final cutoff',next(x[1] for x in attribution if x[0]=='old_generic_prime_tail')==cutoffs[j])
    policy_results.append({'kind':policy['kind'],'fixed_cutoffs':[cutoffs[i],cutoffs[j]],'allpair_sha256':digest.hexdigest(),'direct_density_cutoff':next(r['cutoff'] for r in policy['direct_three_to_five'] if F(r['target'])==target),'attribution':attribution})

result={
    'status':'PASS','new_lean_verification':False,
    'scope':'Independent exact factorial-moment construction, explicit matching enumeration, all638 count moments, trial division of1025 primes, exact finite scalar sum, odd integral upper remainder and unchanged193-row policies. Candidate producer was not opened, imported or executed. Tail intervals enclose the constructed upper bound, not the actual unknown infinite prime fee. Mathematical source/halfrow scope is the separate ordinary theorem.',
    'candidate_sha256':sha(candidate),'program_sha256':sha(Path(__file__)),
    'input_sha256':{name:sha(BASE/name) for name in c['input_sha256']},
    'all638_branch_moments_sha256':branchhash,
    'finite_prime_terms_sha256':termhash,'finite_prime_count':len(tail_primes),
    'paired_count_moment7':paired7,'old_noncanonical_max_count_moment7':runner,
    'new_complete_five_parent_tail_interval':Wnew,'old_complete_five_parent_tail':Wold,
    'tail_reduction_decimal':float((Wold-exact_constructed_new)/Wold),
    'attribution':{'old_canonical_count_moment7':oldcanonical,'old_canonical_prime_tail_interval':prime_tail_interval(oldcanonical),'old_generic_prime_tail_interval':prime_tail_interval(generic7)},
    'policies':policy_results,'checks':dict(checks),'check_count':sum(checks.values()),
}
output.write_text(json.dumps(enc(result),indent=2)+'\n')
print(json.dumps(enc(result),indent=2))
