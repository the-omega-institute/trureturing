#!/usr/bin/env python3
"""Independent small fixture and exact analytic dense-stage debit consumer.

Only N=A=E=1 is constructed (126 originals). N=A=E=4 is evaluated from
the proved reciprocal-tail formula, not by constructing its 31248 classes.
No external data, prior producer, or floating-point decision is used.
"""

from fractions import Fraction as F
from itertools import combinations, product
from math import prod
from hashlib import sha256
from pathlib import Path
import json


Q=(5,7,11,13,17,19)
LATER=(11,13,17,19)
SAFE={5:(4,),7:(5,),11:(7,8,9,10),13:(9,10,11,12),17:(11,12,13,14,15,16)}
CAP={11:F(5,3),13:F(3,2),17:F(2),19:F(9,5)}
THRESHOLD={11:2,13:2,17:4,19:4}
COEFFICIENT={11:F(1,3),13:F(1,4),17:F(1,4),19:F(1,5)}

# Masks here are relative to Rq: (11), (11,13), or (11,13,17).
# For each p, supports containing p are ordered by increasing bitmask and
# assigned successive entries of SAFE[p]. These are literal fixed phases.
PALETTE={
    11:{},
    13:{1:{11:7}},
    17:{1:{11:7},2:{13:9},3:{11:8,13:10}},
    19:{1:{11:7},2:{13:9},3:{11:8,13:10},4:{17:11},
        5:{11:9,17:12},6:{13:11,17:13},7:{11:10,13:12,17:14}},
}
checks={}


def check(name,condition):
    if name in checks or not condition:
        raise RuntimeError('failed or duplicate: '+name)
    checks[name]=True


def subset(primes,mask):
    return tuple(p for i,p in enumerate(primes) if mask & (1<<i))


def crt(phases):
    modulus=prod(phases)
    residue=sum(a*(modulus//p)*pow(modulus//p,-1,p) for p,a in phases.items()) % modulus
    return modulus,residue


def hit(phases,point):
    return all(point[p] % p == a for p,a in phases.items())


def old_phases(q,support):
    if support and not ({5,7} & set(support)):
        remaining=tuple(p for p in LATER if p<q)
        mask=sum(1<<i for i,p in enumerate(remaining) if p in support)
        return dict(PALETTE[q][mask])
    return {p:SAFE[p][0] for p in support}


for q in LATER:
    remaining=tuple(p for p in LATER if p<q)
    check('palette_q%d_has_every_nonempty_later_support' % q,
          set(PALETTE[q])==set(range(1,1<<len(remaining))))
    for i,p in enumerate(remaining):
        masks=[mask for mask in range(1,1<<len(remaining)) if mask & (1<<i)]
        check('palette_q%d_p%d_follows_bitmask_order' % (q,p),
              [PALETTE[q][mask][p] for mask in masks]==list(SAFE[p][:len(masks)]))
    check('palette_q%d_overlapping_supports_conflict' % q,all(
        all(PALETTE[q][left][p]!=PALETTE[q][right][p] for p in
            set(PALETTE[q][left]) & set(PALETTE[q][right]))
        for left,right in combinations(PALETTE[q],2)))

originals=[]


def add(kind,phases,largest,old_support=(),copy=0):
    modulus,residue=crt(phases)
    private={p:phases.get(p,0) for p in Q}
    carrier,private_integer=crt(private)
    originals.append(dict(kind=kind,phases=phases,modulus=modulus,residue=residue,
                          largest_prime=largest,old_support=old_support,copy=copy,
                          private_coordinates=private,private_integer=private_integer))


for p in (5,7):
    for digit in (1,2):
        add('old_pure',{p:digit},p,copy=digit-1)
for digit7 in (3,4):
    add('old_mixed',{5:3,7:digit7},7,old_support=(5,),copy=digit7-3)
for q in LATER:
    old=tuple(p for p in Q if p<q)
    for mask in range(1<<len(old)):
        support=subset(old,mask)
        phases=old_phases(q,support)
        for copy in (0,1):
            add('later',{**phases,q:2*len(support)+1+copy},q,support,copy)

label_counts={}
for original in originals:
    d=original['modulus']
    label_counts[d]=label_counts.get(d,0)+1
check('small_fixture_126_originals_63_labels',len(originals)==126 and len(label_counts)==63)
check('every_numerical_label_has_two_copies',set(label_counts.values())=={2})
check('all_labels_odd_nonunit',all(d>1 and d%2 for d in label_counts))
check('full_six_prime_support',set().union(*(r['phases'].keys() for r in originals))==set(Q))
check('all_zero_survives',not any(hit(r['phases'],dict.fromkeys(Q,0)) for r in originals))
private_counts=[]
for original in originals:
    integer=original['private_integer']
    literal=[integer % other['modulus']==other['residue'] for other in originals]
    coordinate=[hit(other['phases'],original['private_coordinates']) for other in originals]
    private_counts.append(sum(literal))
    check('private_point_%d_is_unique_and_CRT_consistent' % len(private_counts),
          literal==coordinate and sum(literal)==1 and integer%original['modulus']==original['residue'])
check('all_15876_private_point_class_pairs_checked',len(private_counts)*len(originals)==15876)

for q in LATER:
    row=[r for r in originals if r['kind']=='later' and r['largest_prime']==q]
    old=tuple(p for p in Q if p<q)
    check('q%d_small_fixture_complete_old_box' % q,
          len(row)==2*(1<<len(old)) and len({r['modulus']//q for r in row})==1<<len(old))
    check('q%d_current_terminal_colors_valid' % q,all(1<=r['phases'][q]<q for r in row))
    if q!=19:
        check('q%d_safe_digits_avoid_all_own_terminal_colors' % q,
              set(SAFE[q]).isdisjoint({r['phases'][q] for r in row}))
    by_label={d:[r for r in row if r['modulus']==d] for d in {r['modulus'] for r in row}}
    check('q%d_two_copies_have_identical_old_phases' % q,all(
        {p:a for p,a in pair[0]['phases'].items() if p!=q}==
        {p:a for p,a in pair[1]['phases'].items() if p!=q} for pair in by_label.values()))

# Finite representatives are exhaustive for the current head predicates:
# old 5/7 are the actual two eta roots (3,3),(3,4); each earlier later-prime
# coordinate is one of its used safe colors or a single nonmatching class.
# A representative 0 for the nonmatching class suffices because no current
# old predicate asks for anything except these listed safe colors.
representative_rows={}
total_representatives=0
for q in LATER:
    row=[r for r in originals if r['kind']=='later' and r['largest_prime']==q]
    slots=[r for r in row if r['copy']==0]
    remaining=tuple(p for p in LATER if p<q)
    categories={p:(0,)+tuple(sorted({palette[p] for palette in PALETTE[q].values() if p in palette}))
                for p in remaining}
    category_tuples=list(product(*(categories[p] for p in remaining)))
    records=[]
    for root7 in (3,4):
        for values in category_tuples:
            point={**dict.fromkeys(Q,0),5:3,7:root7,**dict(zip(remaining,values))}
            active=[]
            for original in slots:
                old={p:a for p,a in original['phases'].items() if p!=q}
                if hit(old,point):
                    active.append(original['old_support'])
            active_nonunit=[set(s) for s in active if s]
            pairwise_disjoint=all(not(left & right) for left,right in combinations(active_nonunit,2))
            forbidden={r['phases'][q] for r in row
                       if hit({p:a for p,a in r['phases'].items() if p!=q},point)}
            g=1-F(len(forbidden),q)
            mass=min(F(1),CAP[q]*g)
            check('q%d_representative_%d_head_and_kernel' % (q,len(records)),
                  pairwise_disjoint and len(active)<=1+len(remaining)<=THRESHOLD[q]
                  and g>=1/CAP[q] and mass==1)
            records.append(dict(old_coordinates={p:point[p] for p in Q if p<q},
                                active_supports=active,head_load=len(active),
                                forbidden_q_digits=sorted(forbidden),g=g,row_mass=mass))
    maxload=max(r['head_load'] for r in records)
    ming=min(r['g'] for r in records)
    coarse_g=1-F(2*(1+len(remaining)),q-1)
    check('q%d_max_head_load_attains_claimed_bound' % q,maxload==1+len(remaining))
    check('q%d_actual_g_dominates_general_union_bound' % q,ming>=coarse_g>=1/CAP[q])
    representative_rows[q]=dict(categories=categories,count=len(records),
        maximum_head_load=maxload,minimum_actual_g=ming,general_g_lower_bound=coarse_g,
        reciprocal_cap=1/CAP[q],representatives=records)
    total_representatives+=len(records)
check('274_exhaustive_head_predicate_representatives',total_representatives==274)

# The ACTUAL fibre union reuses one terminal color pair for every active
# support cardinality. Verify it on all finite predicate representatives,
# now including old safe 5/7 roots instead of restricting to eta.
actual_union_rows={}
actual_union_representatives=0
for q in LATER:
    row=[r for r in originals if r['kind']=='later' and r['largest_prime']==q]
    slots=[r for r in row if r['copy']==0]
    old=tuple(p for p in Q if p<q)
    categories={p:(0,)+tuple(sorted({r['phases'][p] for r in slots if p in r['phases']})) for p in old}
    records=[]
    for values in product(*(categories[p] for p in old)):
        point={**dict.fromkeys(Q,0),**dict(zip(old,values))}
        active=[r['old_support'] for r in slots
                if hit({p:a for p,a in r['phases'].items() if p!=q},point)]
        cardinalities=sorted({len(support) for support in active})
        k=len(cardinalities)
        digits={r['phases'][q] for r in row
                if hit({p:a for p,a in r['phases'].items() if p!=q},point)}
        forbidden_mass=F(len(digits),q)
        actual_loss=1-min(F(1),CAP[q]*(1-forbidden_mass))
        cardinality_loss=COEFFICIENT[q]*max(F(0),k*(1-F(1,q))-THRESHOLD[q])
        high_support_count=sum(len(support)>=THRESHOLD[q] for support in active)
        check('q%d_actual_union_representative_%d' % (q,len(records)),
              0 in cardinalities and len(digits)==2*k and forbidden_mass==F(2*k,q)
              and actual_loss==cardinality_loss
              and actual_loss<=COEFFICIENT[q]*high_support_count)
        records.append(dict(old_coordinates={p:point[p] for p in old},
            active_supports=active,active_cardinalities=cardinalities,
            forbidden_q_digits=sorted(digits),forbidden_mass=forbidden_mass,
            actual_row_loss=actual_loss,high_support_count=high_support_count))
    check('q%d_repeated_cardinalities_are_not_counted_as_distinct_colors' % q,
          any(len(r['active_supports'])>len(r['active_cardinalities']) for r in records))
    actual_union_rows[q]=dict(categories=categories,count=len(records),records=records)
    actual_union_representatives+=len(records)
check('548_actual_union_predicate_representatives',actual_union_representatives==548)

# N=A=E=4: evaluate the proved ALL-completion bound analytically. No such
# original family is constructed here. Reconstruct reciprocal tails by
# subtracting the finite geometric box from the full product, then check
# the equivalent closed tail formula independently.
N=A=E=4
analytic_rows={}
for q in LATER:
    old=tuple(p for p in Q if p<q)
    D=prod((CAP[p] for p in LATER if p<q),start=F(1))
    Z=prod((F(p,p-1) for p in old),start=F(1))
    finite_box=prod((sum((F(1,p**a) for a in range(A+1)),F(0)) for p in old),start=F(1))
    reciprocal_tail=Z-finite_box
    closed_tail=Z*(1-prod((1-F(1,p**(A+1)) for p in old),start=F(1)))
    head_beta=1-F(1,q**E)
    tail_beta=F(1,q**E)
    head_upper=D*head_beta*reciprocal_tail
    tail_upper=D*tail_beta*(Z-1)
    Jupper=head_upper+tail_upper
    check('q%d_independent_reciprocal_tail_identity' % q,reciprocal_tail==closed_tail and reciprocal_tail>0)
    check('q%d_complete_beta_head_tail_partition' % q,head_beta+tail_beta==1)
    analytic_rows[q]=dict(old_primes=old,density_cap=D,full_reciprocal_sum=Z,
        finite_reciprocal_box=finite_box,missing_reciprocal_tail=reciprocal_tail,
        head_beta=head_beta,tail_beta=tail_beta,head_debit_upper=head_upper,
        tail_debit_upper=tail_upper,total_debit_upper=Jupper,
        stage_coefficient=COEFFICIENT[q],weighted_debit_upper=COEFFICIENT[q]*Jupper)

sum5=sum((F(1,5**e) for e in range(1,N+1)),F(0))
sum7=sum((F(1,7**e) for e in range(1,N+1)),F(0))
d5=F(1,2)-2*sum5
d7=F(1,3)-2*sum7
mixed_mass=2*sum5*sum7
delta=F(1,12)-mixed_mass
T=F(257,51)
c0=F(6168733163201163811,542935350932041267200)
A5=F(44887686823492905683,27146767546602063360)
A7=F(20281636668601030051,20313907687933516800)
A57=F(585035299774741193,203139076879335168)
pure_credit=A5*d5+A7*d7+A57*d5*d7
weighted_stage=sum((r['weighted_debit_upper'] for r in analytic_rows.values()),F(0))
credit_upper=pure_credit+(T-2)*(delta+weighted_stage)
gap=c0-credit_upper
count_formula=4*N+2*N*N+2*E*sum((A+1)**k for k in range(2,6))
check('large_family_count_is_formula_only_31248',count_formula==31248)
check('analytic_old_defects_match_exact_values',
      (d5,d7,delta)==(F(1,1250),F(1,7203),F(121,720300)))
check('all_completion_stage_credit_upper_matches_reference',credit_upper==F(
    110382359184068166213935387347,16051257544045797121429180800000))
check('all_completion_stage_credit_gap_positive',gap==F(
    143978246159999205632374630181,32102515088091594242858361600000) and gap>0)

# Same-family repair: bound ACTUAL row losses by high-cardinality support
# events. Under reference Haar, each event is a product of safe combs and
# has mass at most product 1/(p-1). The actual pre-row law is dominated
# by Dq times Haar; it need not be a product law.
actual_loss_bounds={}
expected_losses={11:F(1,72),13:F(7,192),17:F(1,4608),19:F(49,46080)}
for q in LATER:
    old=tuple(p for p in Q if p<q)
    Dq=prod((CAP[p] for p in LATER if p<q),start=F(1))
    supports=[S for size in range(THRESHOLD[q],len(old)+1) for S in combinations(old,size)]
    event_sum=sum((prod((F(1,p-1) for p in S),start=F(1)) for S in supports),F(0))
    bound=COEFFICIENT[q]*Dq*event_sum
    check('q%d_uniform_actual_loss_bound' % q,bound==expected_losses[q])
    actual_loss_bounds[q]=dict(threshold=THRESHOLD[q],density_cap=Dq,
        high_supports=supports,reference_Haar_event_sum_upper=event_sum,loss_upper=bound)
total_actual_loss=sum((row['loss_upper'] for row in actual_loss_bounds.values()),F(0))
actual_mass_lower=F(1,4)-total_actual_loss
query_factor=prod((1+CAP[q]/(q-1) for q in LATER),start=F(1))
w5_N2=1-2*sum((F(1,5**e) for e in (1,2)),F(0))
w7_N2=1-2*sum((F(1,7**e) for e in (1,2)),F(0))
raw_query_upper=(w5_N2+F(1,4))*(w7_N2+F(1,6))*query_factor
actual_norm_upper=raw_query_upper/actual_mass_lower-1
check('uniform_actual_loss_sum_and_mass_lower',
      total_actual_loss==F(793,15360) and actual_mass_lower==F(3047,15360)>0)
check('conditional_backward_query_product_factor',query_factor==F(2079,1280))
check('N_at_least_two_pure_mass_upper_constants',w5_N2==F(13,25) and w7_N2==F(33,49))
check('common_raw_query_upper_includes_unit',raw_query_upper==F(268983,256000))
check('same_law_norm_subtracts_normalized_unit_once',actual_norm_upper==F(654599,152350)==F(59509,13850))
check('same_dense_family_norm_strictly_below_target',T-actual_norm_upper==F(524491,706350)>0)


def encode(value):
    if isinstance(value,F):
        return str(value.numerator)+'/'+str(value.denominator)
    if isinstance(value,dict):
        return {str(k):encode(v) for k,v in value.items()}
    if isinstance(value,(list,tuple)):
        return [encode(v) for v in value]
    return value


result=dict(scope='Finite N=A=E=1 actual irredundant fixture, analytic N=A=E=4 ALL-completion stage-debit upper bound, and a same-family actual-loss repair proving a norm upper bound for every N>=2; no actual-norm lower bound.',
    fixed_safe_digits=SAFE,fixed_palette_injection=PALETTE,
    palette_convention='For every q and old later prime p, supports S containing p are ordered by Rq bitmask; successive Safe_p digits are assigned. Supports containing 5 or 7 use each coordinate first safe digit.',
    small_fixture=dict(N=1,A=1,E=1,original_count=len(originals),label_count=len(label_counts),
        full_prime_support=Q,originals=originals,label_counts=label_counts,
        private_point_pair_checks=len(originals)**2,representative_rows=representative_rows,
        representative_count=total_representatives,
        representative_scope='Exhaustive truth-pattern classes of current old-phase predicates on eta; later coordinates collapse to each used safe color or a nonmatching class. No full original-period scan.'),
    actual_union_finite_guard=dict(representative_count=actual_union_representatives,rows=actual_union_rows,
        principle='q-terminal color pairs are indexed by distinct ACTIVE SUPPORT CARDINALITIES, not the number of active old numerical cofactors.',
        scope='N=A=E=1 exact actual fibre calculation on all truth patterns of its old-coordinate predicates, including histories outside eta.'),
    analytic_large_family=dict(N=N,A=A,E=E,original_count_formula=count_formula,
        family_constructed=False,rows=analytic_rows,d5=d5,d7=d7,mixed_mass=mixed_mass,delta=delta,
        pure_credit=pure_credit,weighted_stage_debit_upper=weighted_stage,
        total_credit_excluding_final_JL=credit_upper,c0=c0,c0_minus_upper=gap,
        formula='Jq <= Dq*((1-q^-E)*tau_q(A)+q^-E*(Zq-1)); Dq=product previous caps; tau_q=Zq-finite reciprocal box.',
        statement='The upper bound holds for every legal comparison completion of this one fixed finite family; it concerns pure, packing, and stage credits only.'),
    same_family_actual_loss_repair=dict(scope='For the stated support-cardinality-colored family, all N>=2 and every positive finite A,E. General conditional-integration and cardinality bounds are ordinary proofs.',
        row_loss_bounds=actual_loss_bounds,total_loss_upper=total_actual_loss,
        initial_mass_lower=F(1,4),final_mass_lower=actual_mass_lower,
        later_query_product_factor=query_factor,w5_upper=w5_N2,w7_upper=w7_N2,
        raw_complete_query_sum_including_unit_upper=raw_query_upper,
        normalized_query_norm_excluding_unit_upper=actual_norm_upper,
        target=T,strict_target_margin=T-actual_norm_upper,
        dependency_discipline='Integrate backwards: each queried conditional row is bounded by Cq/q^e, each unqueried row by one. Only the old pure-source reference factorizes. The unit raw term equals actual lambda(1); normalize once and subtract one.'),
    mathematical_boundaries=['The arbitrary-parameter irredundancy and uniform all-completion theorem are ordinary symbolic proofs, not consequences of the small fixture alone.',
        'The same eta is transported by the fixed completed kernels; the density bound does not assume independent coordinates.',
        'The same dense family has a proved ACTUAL norm upper bound despite the stage-debit obstruction. No final JL estimate, actual-law norm lower bound, all-laws lower witness, Lean result, or unrestricted Erdos #7 resolution.'],
    checks=checks,passed_count=len(checks),complete=True)
output=Path(__file__).with_suffix('.json')
output.write_text(json.dumps(encode(result),indent=2,ensure_ascii=False)+'\n')
print(json.dumps(dict(output=str(output),checks=len(checks),small_originals=len(originals),
    old_history_representatives=total_representatives,large_original_count_formula=count_formula,
    credit_upper=str(credit_upper),gap=str(gap),output_sha256=sha256(output.read_bytes()).hexdigest())))
