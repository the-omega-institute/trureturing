"""Recompute exact v2 counterexamples from retained, previously inspected excerpts.

Reads local finite statement excerpts, never a live webpage. All checks remain
active under -O. --write writes the canonical result; --check compares it exactly.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations
from math import gcd, lcm
from pathlib import Path
import json

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--base',type=Path,required=True,help='erdos7-odd-covering report root')
mode=parser.add_mutually_exclusive_group(required=True)
mode.add_argument('--write',action='store_true')
mode.add_argument('--check',action='store_true')
args=parser.parse_args()
folder=args.base/'frontier/cover-geometry'
source_path=folder/'mcnew_setty_v2_counterexamples.source-statements.json'
result_path=folder/'mcnew_setty_v2_counterexamples.result.json'
owner343='profile-notes/321-384/343-original-prefix-sat-reductions-and-transport-obstructions.md'
owner334='profile-notes/321-384/334-same-chain-overlap-and-future-risk-certificates.md'
checks=0

def require(ok,message):
    global checks
    if not ok:raise ValueError(message)
    checks+=1

def coverage(classes,period):
    require(all(m>1 and period%m==0 for a,m in classes),'all nonunit moduli divide the checked period')
    masks=[sum(1<<x for x in range(a%m,period,m)) for a,m in classes]
    union=0
    for mask in masks:union|=mask
    return masks,union


def divisors(n):return [d for d in range(1,n+1) if n%d==0]


def omega(n):
    result=0;p=2
    while p*p<=n:
        if n%p==0:
            result+=1
            while n%p==0:n//=p
        p+=1
    return result+int(n>1)


def stirling(n,k):
    table=[[0]*(n+1) for _ in range(n+1)];table[0][0]=1
    for size in range(1,n+1):
        for parts in range(1,size+1):
            table[size][parts]=parts*table[size-1][parts]+table[size-1][parts-1]
    return table[n][k]


def bell(r,n):return -sum((-r)**k*stirling(n,k) for k in range(1,n+1))


source_raw=source_path.read_bytes()
source=json.loads(source_raw)
require(source['schema']=='mcnew-setty-v2-finite-excerpts-v1','recognized finite-excerpt schema')
require(source['source']['version']=='arXiv:2507.23041v2','version-specific source claim')
records=source['statements']
require(set(records)=={'S3.Thmtheorem1','S4.Thmtheorem10','S4.Thmtheorem11'},
        'three retained statement location identifiers')
for record in records.values():
    for item in record['math']:
        require(' '.join(item['alttext'].split())==' '.join(item['annotation'].split()),
                'the retained accessible and embedded-TeX transcriptions agree')
lemma=records['S4.Thmtheorem10'];theorem=records['S4.Thmtheorem11']
require('any set (or multiset) of moduli' in lemma['text'] and 'at most' in lemma['text'],
        'retained Lemma4.10 admits multisets and asserts an upper bound')
require(any('S\\subseteq M' in m['alttext'] and '(-1)^{|S|+1}' in m['alttext'] and '\\lcm S' in m['alttext'] for m in lemma['math']),
        'retained final formula sums nonempty pairwise-coprime subsets')
require('coprime' in theorem['text'] and 'almost-covering number' in theorem['text'],
        'retained Theorem4.11 has the coprime-factor and almost-covering hypotheses')
require(any('B(\\tau(\\ell),\\omega(d))' in m['alttext'] and 'c(n)\\leq' in m['alttext'] for m in theorem['math']),
        'retained inequality and Bell-polynomial argument order')
require(source['context']['section_4_2_B_definition']['tex']==r'B(r,n)\coloneqq-\sum_{k=1}^{n}(-r)^{k}S_{2}(n,k).',
        'retained B convention agrees with the exact recurrence below')

classes=[(a,3) for a in range(3)]+[(0,9)]+[(a,5) for a in range(5)]+[(0,25)]
require(len(classes)==len(set(classes))==10 and all(m%2 for a,m in classes),'ten different congruence classes, all moduli odd')
period=lcm(*(m for a,m in classes));masks,union=coverage(classes,period)
require(period==225 and union.bit_count()==period,'the stated system covers every residue')
restricted=[F(0)]*11;full=[F(0)]*11;eligible_counts=Counter();subset_count=0
for size in range(1,11):
    for ids in combinations(range(10),size):
        subset_count+=1;intersection=(1<<period)-1
        for i in ids:intersection&=masks[i]
        density=F(intersection.bit_count(),period)
        sign=(-1)**(size+1);full[size]+=sign*density
        if all(gcd(classes[i][1],classes[j][1])==1 for i,j in combinations(ids,2)):
            denominator=lcm(*(classes[i][1] for i in ids))
            require(density==F(1,denominator),'every coprime intersection agrees with literal CRT counting')
            restricted[size]+=sign*F(1,denominator);eligible_counts[size]+=1
require(subset_count==1023 and sum(full)==F(union.bit_count(),period)==1,'complete exact inclusion-exclusion agrees with the actual union')
claimed=sum(restricted)
A=sum((F(1,m) for a,m in classes if m%3==0),F(0))
B=sum((F(1,m) for a,m in classes if m%5==0),F(0))
require(A==F(10,9) and B==F(26,25) and claimed==A+B-A*B==F(224,225)<1,
        'restricted subset expression is strictly smaller than the actual union')
coprime_edges=[(i,j) for i,j in combinations(range(10),2) if gcd(classes[i][1],classes[j][1])==1]
require(coprime_edges==[(i,j) for i in range(4) for j in range(4,10)],
        'the exact coprime graph is K4,6')
active_labels=[[i for i,mask in enumerate(masks) if (mask>>x)&1] for x in range(period)]
retained_scores=[len(active)-sum(i in active and j in active for i,j in coprime_edges) for active in active_labels]
require(active_labels[0]==[0,3,4,9] and retained_scores==[0]+[1]*224,
        'the hit graph is an unfilled four-cycle at zero and retained scores equal one everywhere else')
tree_edges=[(0,j) for j in range(4,10)]+[(i,4) for i in range(1,4)]
parent=list(range(10))
def find(i):
    while parent[i]!=i:i=parent[i]
    return i
for i,j in tree_edges:
    ri,rj=find(i),find(j)
    require(ri!=rj,'each chosen tree edge joins different components')
    parent[ri]=rj
require(len(tree_edges)==9 and len({find(i) for i in range(10)})==1,
        'the selected coprime edges form a spanning tree')
tree_scores=[len(active)-sum(i in active and j in active for i,j in tree_edges) for active in active_labels]
require(all(score>=int(bool(active)) for score,active in zip(tree_scores,active_labels)),
        'the forest inequality holds for every actual residue')
tree_upper=sum((F(1,m) for a,m in classes),F(0))-sum((F((masks[i]&masks[j]).bit_count(),period) for i,j in tree_edges),F(0))
require(tree_upper==F(sum(tree_scores),period)==F(371,225),
        'the selected overlap tree gives the exact safe bound371/225')

n=1920;ell=128;b=15
require(n==ell*b and gcd(ell,b)==1,'all stated coprime factorization conditions')
almost=[(2**(i-1)-1,2**i) for i in range(1,8)]
all_ell_moduli=[d for d in divisors(ell) if d>1]
require([m for a,m in almost]==all_ell_moduli,'every permitted distinct nonunit divisor of128 is used once')
ell_masks,ell_union=coverage(almost,ell)
uncovered=[x for x in range(ell) if not (ell_union>>x)&1]
upper_r=sum(ell//d for d in all_ell_moduli)
require(uncovered==[127] and ell_union.bit_count()==upper_r==127,
        'explicit127-residue cover and phase-independent union bound prove r(128)=127 exactly')
cover=[(0,2),(0,3),(1,4),(5,6),(7,12)]
require(len({m for a,m in cover})==len(cover),'covering-number witness has distinct moduli')
_,whole=coverage(cover,n)
require(whole.bit_count()==n,'the five congruences prove r(1920)=1920 and c(1920)=2')
k=len(divisors(ell));terms=[{'divisor':d,'omega':omega(d),'B':bell(k,omega(d))} for d in divisors(b) if d>1]
tail=sum((F(t['B'],t['divisor']) for t in terms),F(0))
rhs=1+F(ell-1,ell)+tail/ell
require(k==8 and terms==[{'divisor':3,'omega':1,'B':8},{'divisor':5,'omega':1,'B':8},{'divisor':15,'omega':2,'B':-56}],
        'divisor and Stirling-number computation fixes every theorem summand')
require(tail==F(8,15) and rhs==F(3833,1920)<2 and 2-rhs==F(7,1920),
        'Theorem4.11 bound is strictly smaller than its attained left side')
require(n==2**7*3*5 and ell==2**7 and k==8,
        'the full increasing prime-power factorization begins with2^7')
next_prime=3;next_required_prime=k+1
require(next_prime!=next_required_prime==9,
        'Definition4.7 stops before3 because3 differs from tau(128)+1')
greedy_ell=2**7
require(greedy_ell==ell and n//greedy_ell==b,
        'Definition5.1 uses exactly ell(1920)=128 and b=15')
least_b_prime=min(d for d in divisors(b) if d>1)
cprime=2 if least_b_prime<=k else rhs
require(least_b_prime==3 and least_b_prime<=k and cprime==2,
        'Definition5.1 takes its trivial-bound branch at1920')
out={'schema':'mcnew-setty-v2-counterexamples-result-v1','status':'PASS',
     'source':{'url':source['source']['url'],'version':source['source']['version'],
         'previously_inspected_html_sha256':source['source']['inspected_html_sha256'],
         'retained_excerpts_sha256':sha256(source_raw).hexdigest(),
         'statement_ids':sorted(records),'retained_formula_pairs_checked':sum(len(r['math']) for r in records.values()),
         'runtime_scope':'Recompute retained excerpts and finite arithmetic; no webpage retrieval or renewed primary-source inspection.'},
     'lemma_4_10':{'classes':[list(x) for x in classes],'period':period,'covered':union.bit_count(),
         'nonempty_subsets':subset_count,'coprime_subset_counts':dict(eligible_counts),
         'coprime_signed_sums':{str(i):str(restricted[i]) for i in range(1,11)},
         'full_signed_sums':{str(i):str(full[i]) for i in range(1,11)},
         'claimed_upper':str(claimed),'actual_density':'1','omitted_signed_total':str(sum(full)-claimed),
         'coprime_graph':{'name':'K4,6','edges':[list(e) for e in coprime_edges],
             'zero_active_labels':active_labels[0],'retained_score_counts':dict(Counter(retained_scores)),
             'failure_residues':[x for x,score in enumerate(retained_scores) if score<int(bool(active_labels[x]))]},
         'existing_forest_repair':{'ordinary_reference':owner334,
             'tree_edges':[list(e) for e in tree_edges],'tree_score_counts':dict(Counter(tree_scores)),
             'tree_union_upper':str(tree_upper),'new_content':False}},
     'theorem_4_11':{'n':n,'ell':ell,'b':b,'tau_ell':k,'almost_cover':[list(x) for x in almost],
         'ell_uncovered':uncovered,'ell_universal_covered_count_upper':upper_r,'whole_cover':[list(x) for x in cover],
         'covered':whole.bit_count(),'actual_c_n':'2','summands':terms,'tail_sum':str(tail),
         'claimed_upper':str(rhs),'gap':str(2-rhs),
         'definition_4_7':{'prime_powers':[[2,7],[3,1],[5,1]],'j':1,'ell_n':greedy_ell,
             'next_prime':next_prime,'required_next_prime':next_required_prime},
         'definition_5_1':{'least_b_prime':least_b_prime,'branch':'least prime of b <= tau(ell)',
             'cprime':str(cprime),'branch_refuted':False}},
     'lemma_3_1':{'ordinary_reference':owner343,
         'reuse':'A minimal subcover of a primitive covering n has lcm n. Simpson at D=n/p gives p maximal-p-height labels; distinctness yields p<=tau(n/p^v_p(n))<=tau(n/p).',
         'validation':'Ordinary application of the cited result; no runtime validation of the prose reference.','new_content':False},
     'active_checks':checks,'producer_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
     'scope':'The two literal v2 statements fail. Journal version uninspected. No whole-paper invalidation, density-estimate audit or distinct-odd-covering conclusion.'}
encoded=(json.dumps(out,indent=2)+'\n').encode()
if args.write:
    result_path.write_bytes(encoded)
else:
    if result_path.read_bytes()!=encoded:
        raise ValueError('canonical result does not match recomputation and source/code bindings')
print(json.dumps({'mode':'write' if args.write else 'check','active_checks':checks,
                  'lemma_upper':str(claimed),'theorem_upper':str(rhs),'status':'PASS'},indent=2))
