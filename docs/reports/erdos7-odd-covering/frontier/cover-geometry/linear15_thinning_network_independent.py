#!/usr/bin/env python3
"""Independent literal-source and complete-network check for the fixed183 fixture.

Reads frozen candidate data, never its producer. Reconstructs actual prefix
membership categories from canonical652 CRT data, the complete512 gate from640,
and the source-correct three-parent budget from pinned658. All checks survive -O.
"""
from argparse import ArgumentParser
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
from math import prod, lcm, isqrt, comb, factorial
from pathlib import Path
import json

PIN652='7645e344c353bcf2eedd4a903b0267db66e792f38e141f46b03cdc1b5bfe653d'
PIN658='cbdc3903174d5640ea6518160abaaa9ac567424f9f8afc717128e1202f378be5'
PIN640='dd00b0e9f6a93713d437394c368a4ef81407cabd5ecb931ae7753926d9d8c3e4'
PIN_CANDIDATE='8a6de84218912ef98db3380d3ea27023d8382338b3be0fdb63935d63b16e99cb'
p=ArgumentParser(description=__doc__)
p.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
p.add_argument('--candidate',type=Path,default=Path(__file__).with_name('linear15_thinning_network_certificate.json'))
p.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=p.parse_args();checks=Counter()
def ck(name,truth):
    checks[name]+=1
    if not truth:raise ArithmeticError('independent verification: '+name)
def load(path,pin,name):
    raw=path.read_bytes();ck(name+'_pin',sha256(raw).hexdigest()==pin);return json.loads(raw)
source=load(args.directory/'linear15_exact_boundary_obstruction.json',PIN652,'canonical652')
network=load(args.directory/'joint_square_pair_225_star_certificate.json',PIN658,'canonical658')
fees=load(args.directory/'remaining33_global_root_exclusion_certificate.json',PIN640,'canonical640')
candidate=load(args.candidate,PIN_CANDIDATE,'candidate660')
HEAD=(3,5,7,11,13,17,19,23,29,31);Q=(7,11,13,17,19)
g=F(200163067,201247200);alpha=F(2673,110656)
ck('same_constants',F(fees['constants']['g'])==F(network['g'])==g and F(fees['constants']['alpha'])==F(network['projection_alpha'])==alpha)
fixture=source['fixture']
ck('fixed183_distinct_odd_originals',len(fixture)==183==len({row['modulus'] for row in fixture}) and all(row['modulus']>1 and row['modulus']%2 for row in fixture))
ck('fixed_height12',source['pure_tail_height']==12)

def prime_power(n):
    for p in HEAD:
        m=n;e=0
        while m%p==0:m//=p;e+=1
        if m==1:return p,e
    raise ArithmeticError('undeclared prime-power component')
parsed=[];pures={p:[] for p in HEAD}
for row in fixture:
    pcs={}
    ck('original_CRT_modulus',prod(d for a,d in row['components'])==row['modulus'])
    for a,d in row['components']:
        prime,e=prime_power(d)
        ck('original_CRT_component',0<=a<d and row['residue']%d==a and prime not in pcs)
        pcs[prime]=(e,a)
    parsed.append((row,pcs))
    if len(pcs)==1:
        prime=next(iter(pcs));pures[prime].append(pcs[prime])
ck('fixed87_pure_originals',sum(map(len,pures.values()))==87)
for prime in HEAD:
    for (e,a),(f,b) in combinations(pures[prime],2):
        ck('disjoint_pure_cylinders',a%prime**min(e,f)!=b%prime**min(e,f))

leaf=lambda p,i:p*(i%p)+i//p
w=[F(2,9)]*6;w[3]=F(0);w[4]=F(1,9)
v=[F(4,75)]*20;v[5]=F(0);v[6]=F(1,25)
ck('normalized_corner',sum(w)==sum(v)==1)
capacities={}
eps3,eps5=F(1,3**12),F(1,3*5**12)
for prime,weights,cap,weak,eps in ((3,w,F(2),4,eps3),(5,v,F(4,3),6,eps5)):
    vals=[]
    for i,target in enumerate(weights):
        a=leaf(prime,i)
        killed=any(e<=2 and a%prime**e==b for e,b in pures[prime])
        haar=F(0) if killed else F(1,prime**2)-sum((F(1,prime**e) for e,b in pures[prime] if e>2 and b%prime**2==a),F(0))
        capacity=cap*haar;vals.append(capacity)
        ck('exact_actual_central_capacity',capacity==target+(eps if i==weak else 0))
        ck('corner_supported_by_actual_pure_survivor',0<=target<=capacity)
    capacities[prime]=vals
    ck('source_L1_positive_surplus',sum(vals)==1+eps)
coords=[(l,m) for l in range(6) for m in range(20) if w[l] and v[m] and not(l<3 and m<5)]
ck('actual80cells',len(coords)==80 and candidate['cells']==[list(c) for c in coords])

prefix={}
for prime in Q:
    masses={}
    for a in range(prime**2):
        root=a%prime
        if any(e==1 and root==b for e,b in pures[prime]):masses[a]=F(0);continue
        rootmass=F(1,prime)-sum((F(1,prime**e) for e,b in pures[prime] if e>=2 and b%prime==root),F(0))
        leafmass=F(1,prime**2)-sum((F(1,prime**e) for e,b in pures[prime] if e>=2 and b%prime**2==a),F(0))
        ck('positive_actual_root_and_prefix',rootmass>0 and leafmass>=0)
        masses[a]=leafmass/((prime-1)*rootmass)
    ck('normalized_actual_outside_law',sum(masses.values())==1)
    for root in range(1,prime):ck('actual_live_root_mass',sum(mu for a,mu in masses.items() if a%prime==root)==F(1,prime-1))
    ck('actual_forced_root1_mass',sum(mu for a,mu in masses.items() if a%prime==1)==F(1,prime-1))
    prefix[prime]=masses

square_pairs=[(row,pcs) for row,pcs in parsed if len(pcs)==2 and set(pcs)<=set(Q) and sorted(e for e,a in pcs.values())==[1,2]]
ck('twenty_actual_square_pairs',len(square_pairs)==20)
new_linear=[(row,pcs) for row,pcs in parsed if row['label'].split(':')[0] in ('45q','75q','225q')]
ck('all_fifteen_new_linear_originals_present',len(new_linear)==15)
square_stars=[(row,pcs) for row,pcs in parsed if row['label'].split(':')[0] in ('3q2','5q2','9q2')]
ck('all_fifteen_square_originals_present',len(square_stars)==15)
def active(pcs,l,m):
    return all(prime not in pcs or leaf(prime,i)%prime**pcs[prime][0]==pcs[prime][1] for prime,i in ((3,l),(5,m)))

# Literal CRT membership categories, independent of the closed F4 formula.
H=[[] for _ in range(32)]
for l,m in coords:
    categories=[]
    for prime in Q:
        unary=[pcs[prime] for row,pcs in parsed if (set(pcs)&set(Q))=={prime} and len(pcs)>1 and active(pcs,l,m)]
        groups={}
        for a,mu in prefix[prime].items():
            if not mu or a%prime==1 or any(a%prime**e==b for e,b in unary):continue
            mask=0
            for k,(row,pcs) in enumerate(square_pairs):
                if prime in pcs:
                    e,b=pcs[prime]
                    if a%prime**e==b:mask|=1<<k
            groups[mask]=groups.get(mask,F(0))+mu
        ck('raw_unary_mass_bound',sum(groups.values())<=F(prime-2,prime-1))
        ck('six_literal_pair_membership_categories',len(groups)==6)
        items=[]
        for mask,mu in groups.items():
            scaled=mu*prime*(prime-1)
            ck('integer_category_weight',scaled.denominator==1 and scaled>=0)
            items.append((mask,scaled.numerator))
        categories.append(items)
    for support in range(32):
        U=[i for i in range(5) if not(support>>i&1)]
        numerator=0
        for states in product(*(categories[i] for i in U)):
            used=0;weight=1
            for mask,mu in states:
                if used&mask:weight=0;break
                used|=mask;weight*=mu
            numerator+=weight
        h=F(numerator,prod(Q[i]*(Q[i]-1) for i in U))
        ck('literal_induced_response',h==F(source['induced_responses'][support][len(H[support])]))
        ck('response_interval',0<h<=1)
        H[support].append(h)
ck('minimum_actual_survivor',min(H[0])==F(378217789,1064194560)==F(source['minimum_actual_conditional_survivor']))

C=[F(c) for c in fees['combined512_coefficients']]
ck('exact_guarded_fee_removal',len(C)==512 and min(C)>=0 and C==[F(c) for c in source['complete512_coefficients']])
ck('candidate_complete_fee_count',len(candidate['complete512_fees'])==512)
denominator=candidate['theta_denominator'];nums=candidate['theta_numerators']
ck('candidate_rational_selector80',denominator==10**6 and len(nums)==80 and all(type(n) is int and 0<=n<=denominator for n in nums))
theta=[F(n,denominator) for n in nums]

def axis_menus(weights,p,deep):
    n=len(weights);live=[i for i,weight in enumerate(weights) if weight]
    return [[weights],[[weight if i//p==root else F(0) for i,weight in enumerate(weights)] for root in range(n//p)],
            [[weight if i==leaf else F(0) for i,weight in enumerate(weights)] for leaf in live],
            [[deep if i==leaf else F(0) for i in range(n)] for leaf in live]]
mx,my=axis_menus(w,3,F(1)),axis_menus(v,5,F(4,5))
selectors=[]
for mode in range(16):
    selectors.append([[xx[l]*yy[m] for l,m in coords] for xx in mx[mode//4] for yy in my[mode%4]])
    ck('opposite_selector_mass_at_most_one',all(sum(form)<=1 for form in selectors[-1]))
screens=[];argmax=[];literal_count=0
for j in range(512):
    mode,T=divmod(j,32)
    values=[sum((theta[c]*H[T][c]*weight for c,weight in enumerate(form)),F(0)) for form in selectors[mode]]
    best=max([F(0)]+values)
    screens.append(best);argmax.append(values.index(best) if best in values else -1)
    literal_count+=len(values)
    ck('all_actual_menu_maxima',all(best>=v for v in values))
mass=sum((w[l]*v[m]*theta[c]*H[0][c] for c,(l,m) in enumerate(coords)),F(0))
ck('empty_screen_equals_source_mass',mass==screens[0])
for j in range(512):ck('candidate_each_evaluated_fee',C[j]*screens[j]==F(candidate['complete512_fees'][j]))
debit=sum((C[j]*screens[j] for j in range(512)),F(0));gate=g*mass-debit
ck('exact_candidate_gate',gate==F(candidate['exact_gate'])==F(204587968819453865393077454016617,63669248958626525491200000000000000))
perturb=2*(g+sum(C))*(eps3+eps5)
ck('exact_uniform_capacity_perturbation',perturb==F(source['central_capacity_perturbation'])==F(candidate['uniform_capacity_perturbation']))
robust=gate-perturb
ck('exact_robust_gate_lower',robust==F(candidate['robust_gate_lower']))
old_upper=sum((max(F(0),F(c)) for c in source['dual_linear_coefficients']),F(0))+perturb
ck('old_uniform_gate_upper_preserved',old_upper==F(source['uniform_gate_upper'])<F(1,300))
old_budget=F(397,50000)+F(1,65536)+F(8,3)*F(19740202146111572828188083,495176015714152109959649689600)
ck('old_B647_obstruction_preserved',F(1,300)<old_budget==F(source['r4_network_budget'])==F(candidate['old_fixed_network_fee']))

raw=prod((F(q-2,q-1) for q in Q[1:]),start=F(1))
old=prod((F(q-2,q-1)-F(2,q*(q-2)) for q in Q[1:]),start=F(1))
ck('raw_omitted_factor187_256',raw==F(187,256)==F(candidate['raw_omitted_mass_factor']))
ck('old_omitted_factor',old==F(network['branch_parameters']['factor'])==F(candidate['old_omitted_mass_factor']))
scale=raw/old
ck('source_correct_factor_ratio',scale==F(452872503765,429470970629)==F(candidate['finite_fee_scale']))
for row in network['finite_rows']:
    owner,h=row['owner'],row['h'];D=F(owner-2)-F(1,65536)
    ck('same193_full_history_caps',row['r']==3 and row['N']==0 and F(row['D'])==D and F(row['t'])==D-h and F(row['cap'])==F(owner-1,h)<F(owner,10))
primes=[p for p in range(3,2188,2) if all(p%d for d in range(2,isqrt(p)+1))]
ck('complete_finite_prime_census',[row['owner'] for row in network['finite_rows']]==[p for p in primes if 37<=p<1253])
head_caps=dict(zip(HEAD,map(F,('2','4/3','7/5','11/9','13/11','17/15','19/17','5/3','20/11','2'))))
finite_caps={row['owner']:F(row['cap']) for row in network['finite_rows']}
m0=podd=F(1);counts=Counter()
for p in primes:
    if p in head_caps:cap=head_caps[p];counts['head']+=1
    elif p in finite_caps:cap=finite_caps[p];counts['finite']+=1
    else:cap=F(2*(p-1),p-3);counts['half']+=1
    factor=1+cap*(F(3,p-1)+F(2,(p-1)**2))
    ck('positive_same_cap_Euler_factor',factor>1)
    m0*=factor;podd*=F(p,p-1)
ck('all326_Euler_factor_counts',dict(counts)==network['Euler_counts']=={'head':10,'finite':193,'half':123})
ck('exact_Euler_product_in_inherited_interval',F(network['M0_lower'])<=m0<=F(network['M0_upper']))
ck('exact_prime_product_in_inherited_interval',F(network['Podd_lower'])<=podd<=F(network['Podd_upper']))
ck('complete_Euler_tail_correction',F(network['Ctail'])==F(2187,2186) and network['Euler_endpoint']==2187)
finite=scale*sum((F(row['fee_upper']) for row in network['finite_rows']),F(0))
ck('exact_new_finite_budget',finite==scale*F(network['finite_fee_upper'])==F(candidate['finite_fee_upper']))
# Exact complete moments of X=L+1 with P(L>=1)=A and
# P(L>=k)=c/p**k for k>=2; finite polynomial sums include all depths.
stirling=[[0]*8 for _ in range(8)];stirling[0][0]=1
for n in range(1,8):
    for k in range(1,n+1):stirling[n][k]=k*stirling[n-1][k]+stirling[n-1][k-1]
def geom_power(p,n):
    r=F(1,p)
    return sum((F(stirling[n][k]*factorial(k))*r**k/(1-r)**(k+1) for k in range(n+1)),F(0))-(1 if n==0 else 0)
def xmoment(spec,j):
    if j==0:return F(1)
    p,A,c=spec
    return 1+(A-c/p)*(2**j-1)+c*sum((comb(j,t)*geom_power(p,t) for t in range(j)),F(0))
specs=[(3,F(2,3),F(2)),(5,F(4,15),F(4,3)),(7,F(1,6),F(7,5)),(11,F(1,10),F(11,9)),(13,F(1,10),F(13,10))]
moments=[[xmoment(spec,j) for j in range(8)] for spec in specs]
for i in range(5):
    for j in range(8):ck('complete_geometric_coordinate_moment',moments[i][j]==F(network['coordinate_moments'][i][j]))
moment7=sum(((-1)**(7-j)*comb(7,j)*prod(moments[i][j] for i in range(5)) for j in range(8)),F(0))
sharp=F(2**7*6**6,7**7)
tail=sharp*moment7/(6*1249**6);typeI=F(network['ordinary_typeI_fee'])
ck('complete_generic_five_parent_moment',moment7==F(network['complete_generic_five_role_moment7']))
ck('complete_halfrow_tail_formula',sharp==F(network['sharp_halfrow_constant7']) and tail==F(network['complete_five_parent_tail']))
ck('unchanged_typeI',typeI==F(1,65536))
ck('all_policies_present',[(p['kind'],p['K']) for p in candidate['policies']]==[(p['kind'],p['K']) for p in network['policies']])
policies=[]
for nc,cc in zip(network['policies'],candidate['policies']):
    ck('same_policy_scope',nc['max_parents_below_switch']==3 and nc['arbitrary_threshold']==2**nc['K'])
    k=nc['K'];switch=2**k
    mhi,plo,ctail=F(network['M0_upper']),F(network['Podd_lower']),F(network['Ctail'])
    if nc['kind']=='RS':
        polynomial=sum((F(factorial(6),factorial(6-j))*F(7*k,10)**(6-j) for j in range(7)),F(0))
        arbitrary=mhi*ctail*F(99,97)**6*F(switch,switch-3)**2*polynomial/(2*(switch-1)*F(1841,240)**6)
    elif nc['kind']=='elementary':
        ratio=F(1,2)*F(k+3,k+2)**6
        ck('convergent_elementary_tail_ratio',ratio<1)
        arbitrary=2*mhi*ctail/plo**6*(4*(k+2))**6/F(switch)/(1-ratio)
    else:raise ArithmeticError('unexpected policy')
    ck('complete_arbitrary_parent_tail_formula',arbitrary==F(nc['fee']))
    total=finite+tail+typeI+arbitrary
    margin=robust-total;projected=alpha*margin
    ck('exact_total_network_fee',total==F(cc['new_complete_fee']))
    ck('exact_raw_and_projected_margins',margin==F(cc['raw_margin']) and projected==F(cc['projected_margin']))
    ck('complete_density_one35000',projected>F(1,35000))
    policies.append({'kind':nc['kind'],'K':nc['K'],'arbitrary_threshold':nc['arbitrary_threshold'],
                     'max_parents_below_switch':3,'inherited_arbitrary_parent_fee':nc['fee'],
                     'new_complete_fee':str(total),'raw_margin':str(margin),'projected_margin':str(projected),
                     'density_denominator':35000})
ck('candidate_status_and_scope',candidate['status']=='PASS' and candidate['new_lean_verification'] is False and candidate['source_hashes']==[PIN652,PIN658])
result={'schema':'linear15-thinning-network-independent-v1','status':'PASS','new_lean_verification':False,
        'verifier_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'candidate_sha256':PIN_CANDIDATE,
        'source_sha256':{'652':PIN652,'658':PIN658,'640':PIN640},'candidate_producer_read':False,
        'fixture_originals':183,'pure_height':12,'cells':[list(c) for c in coords],
        'actual_central_capacities':{str(p):[str(c) for c in v] for p,v in capacities.items()},
        'minimum_actual_response':str(min(H[0])),'complete512_screens':[str(s) for s in screens],
        'argmax_indices':argmax,'literal_selector_candidates':literal_count,'source_mass':str(mass),
        'complete_query_debit':str(debit),'exact_gate':str(gate),'uniform_capacity_perturbation':str(perturb),
        'robust_gate_lower':str(robust),'old_uniform_gate_upper':str(old_upper),'old_fixed_B647_budget':str(old_budget),
        'raw_omitted_factor':str(raw),'old_omitted_factor':str(old),'finite_fee_scale':str(scale),
        'finite_fee_upper':str(finite),'complete_five_parent_tail':str(tail),'ordinary_typeI_fee':str(typeI),
        'projection_alpha':str(alpha),'Euler_factor_counts':dict(counts),'complete_generic_moment7':str(moment7),'policies':policies,'checks':dict(sorted(checks.items())),'check_count':sum(checks.values()),
        'scope':'Fixed183 CRT fixture and its stated central capacity class; one common theta, full512 gate, corrected raw unary omission and pinned658 same-cap network. Finite coefficients do not prove actual-source or all-height transfer.',
        'not_claimed':['arbitrary fifteen-star phases','additional pure head originals','new Lean proof','necessary continuation loss','unrestricted Erdos7']}
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'PASS','check_count':result['check_count'],'gate':str(gate),'robust_gate':str(robust),
                  'raw_omitted_factor':str(raw),'projected':{p['kind']:float(F(p['projected_margin'])) for p in policies},
                  'verifier_sha256':result['verifier_sha256']},indent=2))
