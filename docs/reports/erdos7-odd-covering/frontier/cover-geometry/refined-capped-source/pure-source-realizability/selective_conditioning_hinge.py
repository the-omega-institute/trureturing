#!/usr/bin/env python3
"""Complete selective-conditioning certificate for one fixed retained source.

Standard library only. Defaults are sibling artifacts; --input-dir relocates
existing 827/828 dependencies. Verification does not rewrite saved results.
"""
from fractions import Fraction as F
from itertools import product
from functools import lru_cache
from pathlib import Path
from math import prod
import argparse, hashlib, json

checks=0

def check(ok,label):
    global checks
    checks+=1
    if not ok:raise RuntimeError(label)

def encode(value):
    if isinstance(value,F):return str(value)
    if isinstance(value,dict):return {str(k):encode(v) for k,v in value.items()}
    if isinstance(value,(tuple,list)):return [encode(v) for v in value]
    return value

parser=argparse.ArgumentParser(description=__doc__)
base=Path(__file__).resolve().parent
parser.add_argument('--certificate',type=Path,default=base/'selective_conditioning_hinge_certificate.json')
parser.add_argument('--result',type=Path,default=base/'selective_conditioning_hinge.json')
parser.add_argument('--input-dir',type=Path,default=base)
parser.add_argument('--write-result',type=Path)
args=parser.parse_args()
certificate_bytes=args.certificate.read_bytes()
contract=json.loads(certificate_bytes)
check(contract['schema']=='e7-selective-conditioning-certificate-v1','certificate schema')
PLAN_SHA='7ca6994a77d53ee6baa13a14454c3e6c98e48eaf3981a0e885b6dc190159f0d3'
check(contract['plan_sha256']==PLAN_SHA,'fixed preregistration')
check(contract['phase45']==31 and contract['sourcepoint']=='C','fixed candidate/sourcepoint')
check(contract['thresholds']==list(range(29)),'fixed threshold contract')
check(contract['partial_boxes']==2916 and contract['full_colour_boxes']==192,'fixed box inventory')
check(contract['normalization']=='nu_u restricted to U / nu_u(U)','same normalization')
check(contract['tree_tie_break']=='stop first, then smallest prime; colours in stored order','deterministic tree contract')
EXPECTED_INPUTS=(
 ('retained_factorial_hinge_certificate.json','17557f86d60a40310275025219d893e28ba103b5f099cf53886a8eb8ef970aca'),
 ('retained_factorial_hinge.json','1e76928fa5e63ca221913ad6cdd7ba0db4a54ab093a3a2c26086e1e08b1710e5'),
 ('conditional_root_hinge.json','66c87071b36d67ef2738cda721aed8495c78a5a52da3d209e11fbe60cb2d10ac'))
check(tuple((x['file'],x['sha256']) for x in contract['input_bindings'])==EXPECTED_INPUTS,'fixed dependency bindings')
data=[]
inputs=[]
for name,digest in EXPECTED_INPUTS:
    b=(args.input_dir/name).read_bytes()
    check(hashlib.sha256(b).hexdigest()==digest,'dependency content '+name)
    data.append(json.loads(b));inputs.append({'file':name,'sha256':digest})
cert,old,cond=data
check(cert['phase45']==old['phase45']==31,'fixed phase')
check(old['fixed_candidate_C']['point']==cond['point'],'same source point')
Q=tuple(cert['primes'])
check(Q==(5,7,11,13,17,19,23),'prime labels')
LEAVES=tuple(cert['leaves'])
check(LEAVES==(4,7,2,5,8),'ternary leaves')
PI=tuple(tuple(F(x) for x in block) for block in cond['point']['probabilities'])
W=tuple(F(x) for x in cert['weights'])
check(sum(W)==1,'normalized fixed weights')
check([str(x) for x in W]==old['weights'],'same inherited weights')
C=tuple(F(q-1,q-2) for q in Q)
K=tuple(len(block) for block in PI)
check(K==(3,2,2,2,2,2,2),'categorical dimensions')
PATTERNS=tuple(product(*(range(k) for k in K)))
check(len(PATTERNS)==192,'actual full-colour count')
U=[[F(0) for _ in W] for _ in PATTERNS]
seen=set()
for item in cert['nonzero_u']:
    l,s=item['leaf_index'],item['pattern_id']
    check((l,s) not in seen,'unique retained coefficient')
    seen.add((l,s))
    U[s][l]=F(item['u'])
    check(0<U[s][l]<=W[l],'genuine retained density')
check(len(seen)==106,'same fixed candidate entries')
U=tuple(tuple(v) for v in U)
P_ID={s:i for i,s in enumerate(PATTERNS)}
for i,q in enumerate(Q):
    check(sum(PI[i])==1,'source probability block')
    for p in PI[i]:
        check(p>0 and p>C[i]/q**2,'fixed all-live clipping guard')
INH={k:F(v) for k,v in cond['inherited_exact'].items()}
for key in INH:
    check(INH[key]==F(old['fixed_candidate_C']['exact'][key]),'same inherited '+key)
check(INH['L']>0 and INH['tail']>=0,'inherited gate signs')
M_actual=sum((sum(U[j])*prod(PI[i][s[i]] for i in range(7)) for j,s in enumerate(PATTERNS)),F(0))
check(M_actual==INH['M'],'actual retained table mass')
BOXS=tuple(product(*(tuple([-1]+list(range(k))) for k in K)))
check(len(BOXS)==2916,'complete partial-box inventory')
ROOT=(-1,)*7
HMAX=28
LIMIT=HMAX-1
DIVS={n:tuple(d for d in range(1,n+1) if n%d==0) for n in range(1,LIMIT+1)}

# Coordinate means and low atoms retain the complete geometric remainder.
RUNS={}
for i,q in enumerate(Q):
    for colour in range(-1,K[i]):
        m=F(1) if colour==-1 else PI[i][colour]
        shallow=C[i]/q if colour==-1 else min(m,C[i]/q)
        atom=[F(0)]*(LIMIT+1)
        atom[1]=m-shallow
        atom[2]=shallow-C[i]/q**2
        for n in range(3,LIMIT+1):atom[n]=C[i]*(q-1)/q**n
        check(all(x>=0 for x in atom),'positive coordinate atoms')
        mean=m+shallow+C[i]/(q*(q-1))
        tailmass=C[i]/q**LIMIT
        tailmean=tailmass*(LIMIT+1+F(1,q-1))
        check(sum(atom)+tailmass==m,'complete coordinate mass')
        check(sum(n*atom[n] for n in range(1,LIMIT+1))+tailmean==mean,'complete coordinate mean')
        RUNS[i,colour]=(m,mean,tuple(atom))

def convolution(a,b):
    return tuple([F(0)]+[sum((a[d]*b[n//d] for d in DIVS[n]),F(0)) for n in range(1,LIMIT+1)])

@lru_cache(None)
def product_run(i,suffix):
    if i==7:
        return F(1),F(1),tuple([F(0),F(1)]+[F(0)]*(LIMIT-1))
    am,ae,aa=RUNS[i,suffix[0]]
    bm,be,ba=product_run(i+1,suffix[1:])
    return am*bm,ae*be,convolution(aa,ba)

@lru_cache(None)
def v_box(box):
    if -1 not in box:return U[P_ID[box]]
    i=box.index(-1)
    kids=[v_box(box[:i]+(c,)+box[i+1:]) for c in range(K[i])]
    return tuple(max(v[l] for v in kids) for l in range(5))

def tau(v):
    mass=sum(v,F(0))
    root=max(v[0]+v[1],v[2]+v[3]+v[4])
    leaf=max(v)
    check(0<=leaf<=root<=mass,'box common ternary mixture')
    atoms=[F(0),mass-root,root-leaf]
    atoms += [2*leaf*F(3)**(2-n) for n in range(3,LIMIT+1)]
    return mass,mass+root+F(3,2)*leaf,tuple(atoms)

def curve_from_run(mass,mean,atoms):
    result=[]
    lowmass=F(0)
    lowmean=F(0)
    for h in range(HMAX+1):
        if h>=2:
            lowmass+=atoms[h-1]
            lowmean+=(h-1)*atoms[h-1]
        val=mean-h*mass+h*lowmass-lowmean
        check(val>=0,'nonnegative complete hinge')
        result.append(val)
    for h in range(HMAX):
        check(result[h]>=result[h+1],'hinge nonincreasing')
    return tuple(result)

COST={}
BOX_MASS={}
for idx,box in enumerate(BOXS):
    v=v_box(box)
    check(all(v[l]<=W[l] for l in range(5)),'box density under fixed weights')
    if not any(v):
        COST[box]=(F(0),)*(HMAX+1)
        BOX_MASS[box]=F(0)
        continue
    qm,qe,qa=product_run(0,box)
    tm,te,ta=tau(v)
    aa=convolution(qa,ta)
    COST[box]=curve_from_run(qm*tm,qe*te,aa)
    BOX_MASS[box]=qm*tm
ROOT_EQUALS_W=(v_box(ROOT)==W)
qm,qe,qa=product_run(0,ROOT)
tm,te,ta=tau(W)
OLD=curve_from_run(qm*tm,qe*te,convolution(qa,ta))
check(OLD[16]==INH['oldH16'],'old complete hinge reconstruction')
check(all(COST[ROOT][h]<=OLD[h] for h in range(HMAX+1)),'root stop below old curve')
FULL=tuple(sum((COST[s][h] for s in PATTERNS),F(0)) for h in range(HMAX+1))
for row in cond['curve']:
    check(FULL[row['h']]==F(row['Hroot']),'full split reproduces independent828 curve')
check(sum(BOX_MASS[s] for s in PATTERNS)==INH['M'],'full leaves retain actual total mass')

DP={}
ACT={}
for box in sorted(BOXS,key=lambda b:b.count(-1)):
    vals=list(COST[box])
    acts=[-1]*(HMAX+1)   # ties keep stop, then the earliest prime.
    for i in range(7):
        if box[i]!=-1:continue
        kids=[box[:i]+(c,)+box[i+1:] for c in range(K[i])]
        for h in range(HMAX+1):
            val=sum((DP[k][h] for k in kids),F(0))
            if val<vals[h]:vals[h],acts[h]=val,i
    DP[box]=tuple(vals)
    ACT[box]=tuple(acts)

@lru_cache(None)
def attaining_tree(box,h):
    i=ACT[box][h]
    if i==-1:return ('stop',box)
    return ('split',i,tuple(attaining_tree(box[:i]+(c,)+box[i+1:],h) for c in range(K[i])))

def audit_tree(tree,h):
    if tree[0]=='stop':
        box=tree[1]
        return COST[box][h],[box],0
    i=tree[1]
    val=F(0);leaves=[];splits=1
    check(len(tree[2])==K[i],'all live children retained')
    for sub in tree[2]:
        a,b,c=audit_tree(sub,h)
        val+=a;leaves.extend(b);splits+=c
    return val,leaves,splits

TREES={}
CURVE=[]
for h in range(HMAX+1):
    value=DP[ROOT][h]
    check(value<=COST[ROOT][h] and value<=FULL[h],'two safe boundary comparisons')
    tree=attaining_tree(ROOT,h)
    treevalue,leaves,splitcount=audit_tree(tree,h)
    check(treevalue==value,'attaining deterministic tree')
    for s in PATTERNS:
        check(sum(all(c==-1 or c==s[i] for i,c in enumerate(b)) for b in leaves)==1,
              'selected tree partitions one actual source')
    key=hashlib.sha256(json.dumps(tree,separators=(',',':')).encode()).hexdigest()[:16]
    if key in TREES:check(TREES[key]==tree,'tree id binding')
    TREES[key]=tree
    gate=(28-h)*INH['L']-value-INH['tail']
    oldgate=(28-h)*INH['L']-OLD[h]-INH['tail']
    row={'h':h,'root_stop':COST[ROOT][h],'dp':value,'full_split':FULL[h],
         'old':OLD[h],'gate':gate,'old_gate':oldgate,'hinge_improvement':OLD[h]-value,
         'dp_decimal':float(value),'gate_decimal':float(gate),'old_gate_decimal':float(oldgate),
         'hinge_improvement_decimal':float(OLD[h]-value),
         'root_choice':'stop' if ACT[ROOT][h]==-1 else Q[ACT[ROOT][h]],
         'tree_id':key,'stop_count':len(leaves),'split_count':splitcount}
    CURVE.append(row)
check(CURVE[16]['old_gate']==INH['oldGate'],'same inherited old gate')
for h in range(HMAX):check(DP[ROOT][h]>=DP[ROOT][h+1],'DP monotone thresholds')
best=max(CURVE[:28],key=lambda row:row['gate'])
closed=max(CURVE,key=lambda row:row['gate'])
allfail=all(row['gate']<=0 for row in CURVE)

# Integer-root equality plus interval concavity proves equality at every real h.
ROOT_ALWAYS_OPTIMAL=all(DP[ROOT][h]==COST[ROOT][h] for h in range(HMAX+1))
check(ROOT_ALWAYS_OPTIMAL,'fixed candidate all integer root stops optimal')
ROOT_V=v_box(ROOT)
check(tuple(W[i]-ROOT_V[i] for i in range(5))==(F(0),F(0),F(1,10**8),F(1,10**8),F(0)),
      'only inherited rationalization envelope deficit')

# Reusable small controls and class-internal counterexamples are below.

def control_source(qs,probabilities,table):
    """Tiny one-leaf comparison, using the same full-tail product mechanism."""
    boxes=tuple(product((-1,0,1),repeat=len(qs)))
    patterns=tuple(product((0,1),repeat=len(qs)))
    costs={}
    for box in boxes:
        matches=[s for s in patterns if all(c==-1 or c==s[i] for i,c in enumerate(box))
                 and all(probabilities[i][s[i]]>0 for i in range(len(qs)))]
        v=max((table[s] for s in matches),default=F(0))
        if v==0:
            costs[box]=(F(0),)*(HMAX+1)
            continue
        m,e,a=tau((v,F(0),F(0),F(0),F(0)))
        for i,q in enumerate(qs):
            cap=F(q-1,q-2)
            mass=F(1) if box[i]==-1 else probabilities[i][box[i]]
            shallow=cap/q if box[i]==-1 else min(mass,cap/q)
            check(mass>0 and shallow>=cap/q**2,'control live clipping')
            mean=mass+shallow+cap/(q*(q-1))
            atoms=tuple([F(0),mass-shallow,shallow-cap/q**2]
                        +[cap*(q-1)/q**n for n in range(3,LIMIT+1)])
            tailmass=cap/q**LIMIT
            check(sum(atoms)+tailmass==mass,'control complete local mass')
            check(sum(n*atoms[n] for n in range(1,LIMIT+1))
                  +tailmass*(LIMIT+1+F(1,q-1))==mean,'control complete local mean')
            m*=mass;e*=mean;a=convolution(a,atoms)
        costs[box]=curve_from_run(m,e,a)
    dp={}
    tree_options={}
    for b in sorted(boxes,key=lambda x:x.count(-1)):
        values=list(costs[b])
        candidates=[(b,)]
        for i,c in enumerate(b):
            if c!=-1:continue
            kids=[b[:i]+(t,)+b[i+1:] for t in (0,1) if probabilities[i][t]>0]
            for h in range(HMAX+1):
                values[h]=min(values[h],sum((dp[k][h] for k in kids),F(0)))
            for choice in product(*(tree_options[k] for k in kids)):
                candidates.append(tuple(z for branch in choice for z in branch))
        dp[b]=tuple(values)
        tree_options[b]=tuple(candidates)
    return costs,dp,tree_options

control_start=checks
ctrlqs=(7,11)
ctrlpi=((F(1,6),F(5,6)),(F(1,10),F(9,10)))
ctrltable={(a,b):F(a!=b) for a,b in product((0,1),repeat=2)}
cc,cd,ct=control_source(ctrlqs,ctrlpi,ctrltable)
cr=(-1,-1)
immediate=[sum((cc[cr[:i]+(c,)+cr[i+1:]][0] for c in (0,1)),F(0)) for i in range(2)]
full=sum((cc[s][0] for s in ctrltable),F(0))
check(cc[cr][0]==F(14,3),'actual finite-pure greedy root')
check(immediate==[F(293,54),F(2821,550)],'actual finite-pure immediate splits')
check(cd[cr][0]==full==F(3367,1650),'actual finite-pure optimal descendants')
check(all(x>cc[cr][0] for x in immediate) and full<cc[cr][0],'actual greedy obstruction')
check(len(ct[cr])==9,'all two-axis trees')
for h in (0,1,4,8):
    tree_values=[sum((cc[b][h] for b in leaves),F(0)) for leaves in ct[cr]]
    check(cd[cr][h]==min(tree_values),'independent enumeration of all tiny trees')
    for leaves in ct[cr]:
        for s in ctrltable:
            check(sum(all(c==-1 or c==s[i] for i,c in enumerate(b)) for b in leaves)==1,
                  'tiny tree common-source partition')
    actual={b:F(0) for b in cc}
    labels=tuple(3**a*7**b*11**c for a in range(3) for b in range(2) for c in range(2))
    phases={n:(8 if n==77 else 4)%n for n in labels}
    for x in range(693):
        if x%9!=4 or x%7==1 or x%11==1:continue
        s=(int(x%7!=0),int(x%11!=0))
        density=ctrltable[s]
        if density==0:continue
        load=sum(x%n==phase for n,phase in phases.items())
        for b in cc:
            if all(c==-1 or c==s[i] for i,c in enumerate(b)):
                actual[b]+=density*F(max(load-h,0),60)
    for b in cc:check(actual[b]<=cc[b][h],'literal tiny query all partial boxes')
    check(actual[cr]<=cd[cr][h],'literal tiny query DP')
    if h==0:check(actual[cr]==F(4,5),'finite-pure literal query mean')

# Class-internal convexity failures with the default caps.
u_values=[]
for t in (F(0),F(1,2),F(1)):
    _,d,_=control_source((7,),((F(1,6),F(5,6)),),{(0,):F(1),(1,):t})
    u_values.append(d[(-1,)][0])
check(u_values==[F(19,15),F(123,40),F(21,5)],'u nonconvex exact values')
u_gap=u_values[1]-(u_values[0]+u_values[2])/2
check(u_gap==F(41,120)>0,'u convexity failure in actual finite pure source')
pi_values=[]
for p in (F(1,7),F(13,84),F(1,6)):
    check(F(5,41)<=p<=F(6,35),'declared outer source interval')
    _,d,_=control_source((7,),((p,1-p),),{(0,):F(1),(1,):F(5,6)})
    pi_values.append(d[(-1,)][0])
check(pi_values==[F(251,60),F(21,5),F(21,5)],'source-block minimum exact values')
pi_gap=pi_values[1]-(pi_values[0]+pi_values[2])/2
check(pi_gap==F(1,120)>0,'negative optimized cost fails source-block concavity')
# All fixed-tree loads are positive integers, hence means-minus-h-mass for h<=1.
h_costs=[]
for h in (F(0),F(1,2),F(1)):
    h_costs.append(min(F(21,5)-h,F(104,25)-F(5,6)*h))
check(h_costs==[F(104,25),F(37,10),F(16,5)],'within-unit threshold switch values')
check(F(21,5)-F(6,25)==F(104,25)-F(5,6)*F(6,25),'threshold crossover')
h_gap=h_costs[1]-(h_costs[0]+h_costs[2])/2
check(h_gap==F(1,50)>0,'optimized hinge not linearly interpolated')
_,hz,_=control_source((7,),((F(1,6),F(5,6)),),{(0,):F(1),(1,):F(4,5)})
check(hz[(-1,)][0]==h_costs[0] and hz[(-1,)][1]==h_costs[2],'threshold example matches stop engine')
zero={s:F(0) for s in ctrltable}
_,zd,_=control_source(ctrlqs,ctrlpi,zero)
check(all(v==0 for v in zd[cr]),'zero retained table')
deadpi=((F(0),F(1)),ctrlpi[1])
dc,dd,_=control_source(ctrlqs,deadpi,ctrltable)
for b in dc:
    if b[0]==0:check(all(v==0 for v in dc[b]),'dead colour contributes zero')
check(all(v>=0 for v in dd[cr]),'dead-colour DP nonnegative')
finite_controls={'checks':checks-control_start,'actual_pure_originals':[[7,1],[11,1]],
 'query_period':693,'literal_query_phase_rule':'phase4 except numerical77 has phase8',
 'greedy':{'root':cc[cr][0],'immediate_splits':immediate,'full_split':full,'actual_query_mean':F(4,5)},
 'table_nonconvexity':{'values':u_values,'midpoint_gap':u_gap},
 'source_block_negative_cost_nonconcavity':{'points':[F(1,7),F(13,84),F(1,6)],'values':pi_values,'midpoint_cost_gap':pi_gap,
   'scope':'declared outer source cell; no finite pure-family realization of every interpolated point claimed'},
 'within_integer_interval_switch':{'thresholds':[F(0),F(1,2),F(1)],'values':h_costs,'crossover':F(6,25),'midpoint_gap':h_gap},
 'new_research_candidate':False}

# This is algebra on the computed curve, not another candidate evaluation.
TAIL_FREE=[{'h':row['h'],'gate_without_tail':row['gate']+INH['tail']} for row in CURVE]
tf=max(TAIL_FREE,key=lambda row:row['gate_without_tail'])
check(tf['h']==24 and tf['gate_without_tail']<0,'even zero tail debit cannot repair this fixed hinge/source')
check(best['gate']<-F(7,50),'exact negative complete-gate margin')
check(tf['gate_without_tail']<-F(9,100),'exact negative zero-tail margin')
result={'schema':'e7-selective-conditioning-result-v1','plan_sha256':PLAN_SHA,
 'certificate_sha256':hashlib.sha256(certificate_bytes).hexdigest(),
 'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'inputs':inputs,'point':cond['point'],'phase45':31,'weights':W,'root_leaf_envelope':ROOT_V,
 'weight_minus_root_envelope':tuple(W[i]-ROOT_V[i] for i in range(5)),
 'nonzero_u':106,'normalization':cert['normalization'],'inherited_exact':INH,
 'partial_boxes':2916,'full_colour_boxes':192,'all_live':True,
 'root_maxima_equal_original_weights':ROOT_EQUALS_W,'root_stop_equals_old_hinge':COST[ROOT]==OLD,
 'complete_geometric_heights':True,'tree_tie_break':contract['tree_tie_break'],
 'curve':CURVE,'selected_trees':TREES,'unique_selected_tree_count':len(TREES),
 'best_permitted_integer':best,'closed_interval_endpoint_max':closed,
 'positive_some_permitted_integer':best['gate']>0,'all_real_permitted_thresholds_fail':allfail,
 'root_stop_is_optimal_at_every_real_threshold_0_to28':ROOT_ALWAYS_OPTIMAL,
 'unique_optimal_tree_claimed':False,
 'real_threshold_guard':'Fixed-tree costs are affine on each integer unit interval. Their minimum D is concave and the gate is convex. Integer endpoint maxima bound the whole interval. Equality D=root-stop at every integer forces equality throughout, because root-stop is affine and D is never greater. Endpoint28 only bounds the last open interval.',
 'zero_tail_diagnostic':{'closed_endpoint_max':tf,'decimal':float(tf['gate_without_tail']),
   'all_real_thresholds_strictly_negative':tf['gate_without_tail']<0,
   'scope':'fixed candidate/C, inherited L and optimal stated proof-class hinge; improving only the nonnegative moment/tail debit cannot repair this diagnostic'},
 'finite_controls':finite_controls,
 'scope':'One unchanged fixed phase31/C candidate; no solver, new source/candidate, full-cell or all-kernel conclusion; no Lean claim.',
 'checks':checks}
serialized=encode(result)
if args.write_result:
    args.write_result.write_text(json.dumps(serialized,indent=2)+'\n')
else:
    saved=json.loads(args.result.read_text())
    check(saved==serialized,'complete saved result mismatch')
print(json.dumps({'verdict':'pass','checks':checks,'partial_boxes':2916,'unique_selected_trees':len(TREES),
                  'best_h':best['h'],'best_gate':float(best['gate']),
                  'zero_tail_best_gate':float(tf['gate_without_tail']),
                  'all_real_thresholds_fail':allfail,'mode':'write' if args.write_result else 'verify'}))
