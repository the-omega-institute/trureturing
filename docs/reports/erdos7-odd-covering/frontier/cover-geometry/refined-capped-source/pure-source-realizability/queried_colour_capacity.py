"""Exact queried-colour capacity bridge on one fixed rational retained table.
Complete heights use depth types 0/1/>=2. Standard library only; no solver.
Normal execution verifies the saved result; --write-result regenerates it.
"""
from fractions import Fraction as F
from itertools import product
from math import lcm, prod, comb, factorial, isqrt
from pathlib import Path
import json
import argparse
from functools import lru_cache

Q=(5,7,11,13,17,19,23)
LEAVES=(4,7,2,5,8)
POINTS=((4,63),(0,32),(3,63))
V5=((F(0),F(1,5),F(4,5)),(F(0),F(4,15),F(11,15)),
    (F(1,5),F(0),F(4,5)),(F(4,15),F(0),F(11,15)),
    (F(4,15),F(4,15),F(7,15)))
PATTERNS=list(product(range(3),*[range(2) for _ in range(6)]))
C=[F(q-1,q-2) for q in Q]
CAP1=[c/q for c,q in zip(C,Q)]
checks=0
def need(ok,message):
    global checks
    checks+=1
    if not ok: raise ValueError(message)
def a4(q):
    t=F(1,q-1)
    return 15*t+50*t*t+60*t**3+24*t**4
def subsets(D):
    S=D
    while True:
        yield S
        if not S: break
        S=(S-1)&D

def query_multiplier(inside,key,S,pi):
    if any(pi[i][colour]==0 for i,colour in zip(inside,key)):
        return F(0)
    return prod((min(CAP1[i],pi[i][colour])/CAP1[i]
                 for i,colour in zip(inside,key) if S>>i&1),start=F(1))

control_pi=[(F(0),F(1,5),F(4,5))]
need(query_multiplier([0],(0,),0,control_pi)==0,
     'zero colour cannot carry a deep query')
need(query_multiplier([0],(1,),0,control_pi)==1,
     'live deep query keeps the complete cap factor')
need(query_multiplier([0],(1,),1,control_pi)==F(3,4),
     'singleton depthone uses its own probability')

def unique_keys(pairs):
    result={}
    for key,value in pairs:
        if key in result: raise ValueError('duplicate JSON key: '+key)
        result[key]=value
    return result

def read_json(path):
    return json.loads(path.read_text(encoding='utf-8'),object_pairs_hook=unique_keys)

here=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--certificate',type=Path,default=here/'queried_colour_capacity_certificate.json')
parser.add_argument('--result',type=Path,default=here/'queried_colour_capacity.json')
parser.add_argument('--write-result',action='store_true')
args=parser.parse_args()
c=read_json(args.certificate)
need(c['schema']=='e7-queried-colour-capacity-v1','declared certificate schema')
need(c['primes']==list(Q) and c['leaves']==list(LEAVES) and c['threshold']==16,
     'literal source coordinates and h16')
parts=[[[0],[1],[2,3,4]]]+[[[0],list(range(1,q))] for q in Q[1:]]
need(c['partitions']==parts and list(map(F,c['source_caps']))==C,'literal partitions and all-height caps')
need(len(c['weights'])==5,'five shared leaf weights')
w=list(map(F,c['weights']))
U=[[F(0)]*192 for _ in range(5)]
seen=set()
for cell in c['nonzero_u']:
    leaf,sid=cell['leaf_index'],cell['pattern_id'];value=F(cell['u'])
    need(type(leaf)is int and type(sid)is int and 0<=leaf<5 and 0<=sid<192,
         'retained cell indices')
    need((leaf,sid) not in seen,'unique retained cell')
    seen.add((leaf,sid))
    need(0<value<=w[leaf],'genuine retained coefficient below same leaf weight')
    U[leaf][sid]=value
need(sum(w)==1 and min(w)>=0,'one normalized shared weight law')
need(len(c['points'])==3 and [x['key'] for x in c['points']]==[list(p) for p in POINTS],
     'exactly the three declared source points')
need(len(c['expected_old_values'])==3,'three prior exact diagnostic rows')
family=dict(c['actual_family'])
selected=c['selected_labels']
literal_family=[(3,0),(9,1),(15,10),(21,7),(45,11),(33,22),(35,0),(39,13),
 (63,49),(51,34),(57,19),(55,0),(105,70),(75,25),(69,46),(65,0),(99,22),
 (77,0),(85,0),(117,13),(95,0),(165,55),(91,0),(147,49),(225,175)]
need(len(family)==len(c['actual_family']) and family==dict(literal_family),
     'same actual opposing phase family with distinct numerical labels')
need(len(selected)==len(set(selected))==23 and set(selected)==set(family)-{3,9},
     'all23 selected numerical labels exactly once')
selected_old={}
selected_new={}
for modulus in selected:
    n=modulus;h=0
    while n%3==0: n//=3;h+=1
    D=S=0;rem=n
    for i,q in enumerate(Q):
        exponent=0
        while rem%q==0: rem//=q;exponent+=1
        if exponent: D|=1<<i
        if exponent==1: S|=1<<i
    need(rem==1 and h<=2 and D and (h>0 or D.bit_count()>1),'selected label belongs to charged inventory')
    value=prod((C[i] for i in range(7) if D>>i&1),start=F(1))/n
    selected_old[D,h]=selected_old.get((D,h),F(0))+value
    selected_new[D,S,h]=selected_new.get((D,S,h),F(0))+value
    for sid,pat in enumerate(PATTERNS):
        compatible=True
        for i,q in enumerate(Q):
            if D>>i&1:
                digit=family[modulus]%q
                colour=(digit if digit<2 else 2) if i==0 else int(digit!=0)
                compatible &= pat[i]==colour
        if compatible:
            for leaf,residue in enumerate(LEAVES):
                if residue%3**h==family[modulus]%3**h:
                    need(U[leaf][sid]==0,'same-source selected-null table entry')

unit=lcm(*(x.denominator for row in U for x in row))
UI=[[int(x*unit) for x in row] for row in U]
r=max(sum(w[:2]),sum(w[2:]));v=max(w)
# Complete product-run hinge: finite subthreshold convolution and full mean.
@lru_cache(None)
def pmf(k,n):
    if k==0:return F(n==1)
    q=Q[k-1];cq=C[k-1]
    def tail(e):return F(1) if e==0 else cq/q**e
    return sum(((tail(d-1)-tail(d))*pmf(k-1,n//d)
                for d in range(1,n+1) if n%d==0),F(0))
mean=prod((1+C[i]/(q-1) for i,q in enumerate(Q)),start=F(1))
H0,Hr,Hv=mean-16,mean,3*mean/2
for n in range(1,16):
    p1=pmf(7,n);p2=pmf(7,n//2) if n%2==0 else F(0)
    pv=sum((F(2,3**(d-2))*pmf(7,n//d)
            for d in range(3,n+1) if n%d==0),F(0))
    H0+=(16-n)*p1;Hr+=(16-n)*(p2-p1);Hv+=(16-n)*(pv-p2)
need(min(H0,Hr,Hv)>=0,'complete nonnegative hinge coefficients')
H=H0+Hr*r+Hv*v

def complete_tail(t):
    need((t['lower'],t['upper'],t['ell'],t['growth'])==(1600,3000,7,21),
         'complete804 tail shape')
    delta=F(t['delta']);grid=t['scale']
    need(delta==F(2,7) and grid==10**30,'tail distortion and rational rounding grid')
    constant=F(27,256)/(delta**3*(1-delta))
    need(constant==F(64827,10240),'analytic tail constant')
    need(all(F(x)/(1-delta)<=comb(21,i)
             for i,x in enumerate((15,50,60,24),1)),'quartic growth domination')
    series=sum((F(factorial(21),factorial(21-j)*21**j) for j in range(22)),F(0))
    total=constant/3*F(99,97)**21*F(3000,2999**4)*series
    ps=[p for p in range(1601,3001) if all(p%d for d in range(2,isqrt(p)+1))]
    need(ps==t['primes'] and len(ps)==179,'complete179-prime bridge to analytic tail')
    for p in reversed(ps):
        raw=constant/(p-1)**4+(1+F(7,5)*a4(p))*total
        total=F(-((-raw.numerator*grid)//raw.denominator),grid)
        need(0<=total-raw<F(1,grid),'upward rounding retains full tail')
    need(total==F(t['expected_upper'])==F(4301685063112470380207,10**30),
         'unchanged complete1600 tail')
    return total
T=complete_tail(c['tail']);T29=1+F(28,27)*a4(29)
need(T29==F(120361,74088),'exactlyone actual pure29 factor')
for i,q in enumerate(Q):
    lower=F(q-2,q*q-q-1)
    need(lower>C[i]/q**2 and q*q*(q-2)*(q-3)-1>0,
         'actual live singleton lower bound exceeds depth2 cap')
    other_lower=1-(2 if i==0 else 1)*CAP1[i]
    need(other_lower>CAP1[i],'other category saturates only at cylinder cap')
    # A4 is the exact complete depth sum, not a numerical truncation.
    need(CAP1[i]+C[i]/(q*(q-1))==C[i]/(q-1),'complete head depth split')
    need(15*CAP1[i]+C[i]*(a4(q)-F(15,q))==C[i]*a4(q),
         'complete quartic depth split')
need(9*(a4(3)-F(15,3))==216,'all ternary maximum depths at leasttwo')
# Full-height counterexample on the old cap domain; no additional source sweep.
ts=(F(2,75),F(4,75),F(6,75));head=[];moments=[]
for t in ts:
    S=t+min(F(4,75),t)+F(1,75)
    head.append(t/2-F(5,2)*S)
    S4=15*t+65*min(F(4,75),t)+F(4,3)*(a4(5)-F(15,5)-F(65,25))
    moments.append(232*(t+S4))
    need(0<t<F(4,15) and (1-t)/4<=F(4,15),'counterexample all-height Haar-suffix cap')
head_gap=head[1]-(head[0]+head[2])/2
moment_gap=moments[1]-(moments[0]+moments[2])/2
need(head_gap==F(c['expected_head_midpoint_gap'])==F(-1,30),
     'old-domain complete-head midpoint nonconcavity')
need(moment_gap==F(c['expected_moment_midpoint_gap'])==F(3016,15),
     'old-domain complete-moment midpoint nonconvexity')
rows=[]
for point_index,(vi,mask) in enumerate(POINTS):
    pi=[V5[vi]]+[(CAP1[i],1-CAP1[i]) if mask>>(i-1)&1 else (F(0),F(1)) for i in range(1,7)]
    need(pi==[tuple(map(F,ps)) for ps in c['points'][point_index]['pi']],
         'literal declared source probabilities')
    for i,q in enumerate(Q):
        need(sum(pi[i])==1 and min(pi[i])>=0,'normalized local probability block')
        need(all(p==0 or p>C[i]/q**2 for p in pi[i]),'live colours exceed second-depth cap')
    denoms=[lcm(*(x.denominator for x in ps)) for ps in pi]
    nums=[[int(x*d) for x in ps] for ps,d in zip(pi,denoms)]
    # Raw response groups are shared by every depth-type subdivision of D.
    data=[]
    for D in range(128):
        inside=[i for i in range(7) if D>>i&1]
        outside=[i for i in range(7) if not D>>i&1]
        groups={}
        for sid,pat in enumerate(PATTERNS):
            key=tuple(pat[i] for i in inside)
            values=groups.setdefault(key,[0]*5)
            weight=prod(nums[i][pat[i]] for i in outside)
            for leaf in range(5): values[leaf]+=weight*UI[leaf][sid]
        den=unit*prod(denoms[i] for i in outside)
        data.append((inside,groups,den))
    M=F(sum(data[0][1][()]),data[0][2])
    old_loss=new_loss=old_moment=new_moment=F(0)
    old_type_count=new_type_count=0
    for D,(inside,groups,den) in enumerate(data):
        old_env=tuple(F(z,den) for z in (
            max(map(sum,groups.values())),
            max(max(sum(x[:2]),sum(x[2:])) for x in groups.values()),
            max(max(x) for x in groups.values())))
        beta=prod((C[i]/(Q[i]-1) for i in inside),start=F(1))
        W=prod((C[i]*a4(Q[i]) for i in inside),start=F(1))
        old_moment+=W*sum(z*mult for z,mult in zip(old_env,(1,15,216)))
        for h in range(3):
            coefficient=(beta if D and (h or len(inside)>1) else F(0))-selected_old.get((D,h),F(0))
            if h==2: coefficient+=beta/2
            need(coefficient>=0,'old complete head coefficient nonnegative')
            old_loss+=coefficient*old_env[h]
            old_type_count+=1
        for S in subsets(D):
            weighted=[]
            for key,values in groups.items():
                multiplier=query_multiplier(inside,key,S,pi)
                if multiplier==0: continue
                weighted.append([multiplier*x for x in values])
            need(bool(weighted),'one realizable colour tuple survives in every query support')
            env=tuple(z/den for z in (
                max(map(sum,weighted)),
                max(max(sum(x[:2]),sum(x[2:])) for x in weighted),
                max(max(x) for x in weighted)))
            need(all(z<=old for z,old in zip(env,old_env)),'same-colour capacity improves each envelope')
            B=prod((CAP1[i] if S>>i&1 else C[i]/(Q[i]*(Q[i]-1)) for i in inside),start=F(1))
            W=prod((15*CAP1[i] if S>>i&1 else C[i]*(a4(Q[i])-F(15,Q[i])) for i in inside),start=F(1))
            new_moment+=W*sum(z*mult for z,mult in zip(env,(1,15,216)))
            for h in range(3):
                coefficient=(B if D and (h or len(inside)>1) else F(0))-selected_new.get((D,S,h),F(0))
                if h==2: coefficient+=B/2
                need(coefficient>=0,'new complete depth-type inventory coefficient nonnegative')
                new_loss+=coefficient*env[h]
                new_type_count+=1
    old_L=M-old_loss;new_L=M-new_loss
    old_tail=27*T29*T*old_moment;new_tail=27*T29*T*new_moment
    old_gate=12*old_L-H-old_tail;new_gate=12*new_L-H-new_tail
    previous=c['expected_old_values'][point_index]
    need(M==F(previous['M']) and H==F(previous['H'])
         and old_L==F(previous['L']) and old_moment==F(previous['K4'])
         and old_gate==F(previous['joint_slack']), 'exact agreement with existing815 diagnostic table')
    need(new_L>=old_L and new_moment<=old_moment,'simultaneous complete head and fourth improvement')
    need(old_type_count==384 and new_type_count==3*3**7,'complete support/depth/ternary inventory counts')
    values=dict(M=M,H=H,old_L=old_L,new_L=new_L,old_moment=old_moment,new_moment=new_moment,
                old_tail=old_tail,new_tail=new_tail,old_gate=old_gate,new_gate=new_gate,
                mass_improvement=new_L-old_L,moment_improvement=old_moment-new_moment)
    rows.append({'point':[vi,mask],'pi':[list(map(str,ps)) for ps in pi],
                 'exact':{key:str(z) for key,z in values.items()},
                 'decimal':{key:float(z) for key,z in values.items()}})
need(rows[0]['exact']['old_gate']==rows[0]['exact']['new_gate'],'all-upper queried capacities coincide with old caps')
need(F(rows[1]['exact']['new_gate'])>F(7,200),
     'second point has strict positive diagnostic gate')
need(all(F(rows[i]['exact']['new_gate'])<F(-3,100) for i in (0,2)),
     'first and third points remain negative')
need(rows[2]['exact']['old_gate']==rows[2]['exact']['new_gate'],
     'this fixed table also has no gain at the third point')
result={'schema':'e7-queried-colour-capacity-result-v1','scope':c['scope'],
        'normalization':'nu_u restricted to complete old survivorU / nu_u(U); same table, same source law for every deletion and mixed query.',
        'checks':checks,'weights':list(map(str,w)),'retained_nonzero_count':len(seen),
        'all_height_depth_types':3**7,'ternary_envelopes_per_point':3*3**7,
        'H0':str(H0),'Hr':str(Hr),'Hv':str(Hv),'H16':str(H),
        'T29':str(T29),'T1600':str(T),
        'counterexample':{'probabilities':list(map(str,ts)),
                          'head_midpoint_gap':str(head_gap),
                          'moment_midpoint_gap':str(moment_gap)},
        'rows':rows}
if args.write_result:
    args.result.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
elif read_json(args.result)!=result:
    raise ValueError('saved result differs from exact reconstruction')
print(json.dumps({'checks':checks,'rows':[{'point':x['point'],
       'old_gate':x['decimal']['old_gate'],'new_gate':x['decimal']['new_gate']}
       for x in rows]},indent=2))
