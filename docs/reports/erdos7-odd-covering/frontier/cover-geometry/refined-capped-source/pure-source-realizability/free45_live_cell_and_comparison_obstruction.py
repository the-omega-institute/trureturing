"""Exact824 phase20 live-cell certificate and phase31 comparison obstruction.
Standalone, standard library, no solver or network. Reads literal rational
certificates, rebuilds all mathematics, and compares the saved exact result.
"""
from fractions import Fraction as F
from itertools import product
from math import lcm,prod,isqrt,factorial,comb
from pathlib import Path
from time import perf_counter
from collections import Counter
import argparse,json,hashlib

Q=(5,7,11,13,17,19,23)
C=tuple(F(q-1,q-2)for q in Q)
CAP=tuple(C[i]/q for i,q in enumerate(Q))
V5=((F(1,5),F(4,15),F(8,15)),(F(4,15),F(1,5),F(8,15)),(F(4,15),F(4,15),F(7,15)))
LOW=tuple(F(q-2,q*q-q-1)for q in Q)
CHECKS=0

def need(ok,label):
    global CHECKS
    CHECKS+=1
    if not ok:raise ValueError(label)

def subsets(D):
    S=D
    while True:
        yield S
        if not S:break
        S=(S-1)&D

def read_json(path):
    def unique(pairs):
        out={}
        for k,v in pairs:
            if k in out:raise ValueError('duplicate JSON key '+k)
            out[k]=v
        return out
    return json.loads(path.read_text(),object_pairs_hook=unique)

def a4(q):
    z=F(1,q-1)
    return 15*z+50*z*z+60*z**3+24*z**4

class Evaluator:
    def __init__(self,c):
        self.api_checks=0
        need(c['normalization']=='nu_u restricted to U / nu_u(U)','retained normalized survivor')
        self.patterns=list(product(range(3),*[range(2) for q in Q[1:]]))
        leaves=(4,7,2,5,8)
        family=[(3,0),(9,1),(15,10),(21,7),(45,20),(33,22),(35,0),(39,13),
            (63,49),(51,34),(57,19),(55,0),(105,70),(75,25),(69,46),(65,0),(99,22),
            (77,0),(85,0),(117,13),(95,0),(165,55),(91,0),(147,49),(225,175)]
        parts=[[[0],[1],[2,3,4]]]+[[[0],list(range(1,q))] for q in Q[1:]]
        need(c['primes']==list(Q) and c['leaves']==list(leaves),'same literal coordinates')
        need(c['actual_family']==[list(z) for z in family] and c['phase45']==20,'new literal phase20 family; all24 originals fixed')
        need(c['partitions']==parts and c['selected_labels']==[m for m,a in family[2:]],'literal categorical projection and selected labels')
        self.w=tuple(map(F,c['weights']))
        need(self.w==tuple(F(x,10**8) for x in (22030622,22030623,13884439,21027158,21027158)),'same deterministic rational candidate weights')
        need(sum(self.w)==1 and min(self.w)>0,'normalized five leaf weights')
        self.unit=lcm(*(F(z['u']).denominator for z in c['nonzero_u']))
        self.UI=[[0]*192 for _ in leaves];seen=set()
        for row in c['nonzero_u']:
            l,sid=row['leaf_index'],row['pattern_id'];value=F(row['u'])
            need(type(l)is int and type(sid)is int and 0<=l<5 and 0<=sid<192,'retained index range')
            need((l,sid)not in seen and 0<value<=self.w[l],'unique retained cell between0 and leaf weight')
            seen.add((l,sid));self.UI[l][sid]=int(value*self.unit)
        need(len(seen)==198,'fixed198 positive entries')
        forced=set()
        for m,a in family[2:]:
            rem=m;h=0
            while rem%3==0:rem//=3;h+=1
            axes=[]
            for i,q in enumerate(Q):
                e=0
                while rem%q==0:rem//=q;e+=1
                if e:axes.append(i)
            need(rem==1 and axes and h<=2,'literal selected modulus inventory')
            for sid,pattern in enumerate(self.patterns):
                if all(a%Q[i] in parts[i][pattern[i]] for i in axes):
                    for l,leaf in enumerate(leaves):
                        if leaf%3**h==a%3**h:forced.add((l,sid))
        need(len(forced)==712 and all(self.UI[l][sid]==0 for l,sid in forced),'all712 new selected-null cells exactly zero')
        self.r=max(sum(self.w[:2]),sum(self.w[2:]));self.v=max(self.w)
        # Full lambda hinge: finite lower PMF plus exact infinite mean.
        need(c['threshold']==16,'fixedh16')
        pmf=[F(0)]*16;pmf[1]=F(1)
        for q,cap in zip(Q,C):
            new=[F(0)]*16
            for a in range(1,16):
                for b in range(1,15//a+1):new[a*b]+=pmf[a]*(1-cap/q if b==1 else cap*(q-1)/q**b)
            pmf=new
        mean=prod((1+cap/(q-1) for q,cap in zip(Q,C)),start=F(1))
        def hinge(rr,vv):
            value=mean*(1+rr+F(3,2)*vv)-16
            for a in range(1,16):
                for b in range(1,15//a+1):
                    probability=1-rr if b==1 else rr-vv if b==2 else 2*vv/3**(b-2)
                    value+=(16-a*b)*pmf[a]*probability
            return value
        H0=hinge(F(0),F(0));Hr=hinge(F(1),F(0))-H0;Hv=hinge(F(1),F(1))-H0-Hr
        for key,value in dict(H0=H0,Hr=Hr,Hv=Hv).items():need(F(c['expected_hinge'][key])==value and value>=0,'complete full-lambda hinge '+key)
        self.H=H0+Hr*self.r+Hv*self.v
        need(self.H==hinge(self.r,self.v),'literal full-lambda specialization')
        self.T29=1+F(28,27)*a4(29)
        need(self.T29==F(120361,74088),'pure29 exactly once')
        need(9*a4(3)-45==216,'all ternary depths>=2 fourth moment')
        # Full804 bridge and analytic tail, with upward rational rounding.
        tail=c['tail'];delta=F(2,7);grid=10**30
        need((tail['lower'],tail['upper'],tail['ell'],tail['growth'])==(1600,3000,7,21),'same complete804 support')
        need(F(tail['delta'])==delta and tail['scale']==grid,'same tail parameters')
        constant=F(27,256)/(delta**3*(1-delta))
        need(constant==F(64827,10240),'tail comparison constant')
        need(all(F(z)/(1-delta)<=comb(21,i) for i,z in enumerate((15,50,60,24),1)),'quartic growth bound')
        polynomial=sum((F(factorial(21),factorial(21-j)*21**j) for j in range(22)),F(0))
        T=constant/3*F(99,97)**21*F(3000,2999**4)*polynomial
        primes=[q for q in range(1601,3001) if all(q%d for d in range(2,isqrt(q)+1))]
        need(primes==tail['primes'] and len(primes)==179,'all179 bridge primes')
        for q in reversed(primes):
            value=constant/(q-1)**4+(1+F(7,5)*a4(q))*T
            T=F(-((-value.numerator*grid)//value.denominator),grid)
            need(0<=T-value<F(1,grid),'tail upward rounding')
        self.T=T
        need(T==F(tail['expected_upper'])==F(4301685063112470380207,10**30),'complete unchanged804 infinite tail')
        deductions={}
        for m in c['selected_labels']:
            n=m;h=0
            while n%3==0:n//=3;h+=1
            D=S=0;rem=n
            for i,q in enumerate(Q):
                exponent=0
                while rem%q==0:rem//=q;exponent+=1
                if exponent:D|=1<<i
                if exponent==1:S|=1<<i
            need(rem==1 and D and h<=2,'exact selected depth inventory')
            value=prod((C[i]for i in range(7)if D>>i&1),start=F(1))/n
            deductions[D,S,h]=deductions.get((D,S,h),F(0))+value
        self.supports=[]
        for D in range(128):
            inside=tuple(i for i in range(7)if D>>i&1)
            outside=tuple(i for i in range(7)if not D>>i&1)
            keys=list(product(*(range(len(c['partitions'][i]))for i in inside)))
            kindex={key:ki for ki,key in enumerate(keys)}
            memberships=[kindex[tuple(s[i]for i in inside)]for s in self.patterns]
            types=[]
            for S in subsets(D):
                B=prod((CAP[i]if S>>i&1 else C[i]/(Q[i]*(Q[i]-1))for i in inside),start=F(1))
                W=prod((15*CAP[i]if S>>i&1 else C[i]*(a4(Q[i])-F(15,Q[i]))for i in inside),start=F(1))
                losses=[]
                for h in range(3):
                    val=(B if D and(h or len(inside)>1)else F(0))-deductions.get((D,S,h),F(0))
                    if h==2:val+=B/2
                    need(val>=0,'nonnegative full residual depth-type coefficient')
                    losses.append(val)
                types.append((tuple(i for i in inside if S>>i&1),tuple(j for j,i in enumerate(inside)if S>>i&1),W,losses))
            self.supports.append((inside,outside,keys,memberships,types))
        need(sum(len(s[-1])for s in self.supports)==2187,'complete3depthtypes per coordinate')

    def evaluate(self,pi):
        for i,row in enumerate(pi):
            need(sum(row)==1 and min(row)>C[i]/Q[i]**2,'one normalized fully live source law')
        den=[lcm(*(x.denominator for x in row))for row in pi]
        nums=[[int(x*d)for x in row]for row,d in zip(pi,den)]
        ratios=[[min(x,CAP[i])/CAP[i]for x in row]for i,row in enumerate(pi)]
        rden=[lcm(*(x.denominator for x in row))for row in ratios]
        rnums=[[int(x*d)for x in row]for row,d in zip(ratios,rden)]
        loss=moment=F(0);mass=None
        for inside,outside,keys,memberships,types in self.supports:
            groups=[[0]*5 for _ in keys]
            for sid,s in enumerate(self.patterns):
                fac=prod(nums[i][s[i]]for i in outside)
                group=groups[memberships[sid]]
                for l in range(5):group[l]+=fac*self.UI[l][sid]
            den0=self.unit*prod(den[i]for i in outside)
            if not inside:mass=F(sum(groups[0]),den0)
            root_leaf=[(sum(a),max(a[0]+a[1],sum(a[2:])),max(a))for a in groups]
            # Equal response types are aggregated before arithmetic; this is
            # exact and automatically reduces all-upper menus to old supports.
            grouped={}
            for active,pos,W,losses in types:
                key=tuple((i,j)for i,j in zip(active,pos)if rden[i]!=1 or any(v!=1 for v in rnums[i]))
                old=grouped.get(key,(F(0),(F(0),)*3))
                grouped[key]=(old[0]+W,tuple(a+b for a,b in zip(old[1],losses)))
            for key,(W,losses)in grouped.items():
                maxes=[0,0,0]
                for digits,base in zip(keys,root_leaf):
                    factor=prod(rnums[i][digits[j]]for i,j in key)
                    for h in range(3):maxes[h]=max(maxes[h],factor*base[h])
                divisor=den0*prod(rden[i]for i,j in key)
                env=[F(x,divisor)for x in maxes]
                loss+=sum((a*b for a,b in zip(losses,env)),F(0))
                moment+=W*(env[0]+15*env[1]+216*env[2])
        L=mass-loss;tail=27*self.T29*self.T*moment;gate=12*L-self.H-tail
        return dict(M=str(mass),loss=str(loss),L=str(L),K4=str(moment),H=str(self.H),tail=str(tail),gate=str(gate),
                    L_decimal=float(L),K4_decimal=float(moment),gate_decimal=float(gate))


LEAVES=(4,7,2,5,8)
POINTS=V5

def build(c,phase45):
    started=perf_counter()
    need(c['primes']==list(Q) and c['leaves']==list(LEAVES),'same actual808 coordinates')
    parts=[[[0],[1],[2,3,4]]]+[[[0],list(range(1,q))]for q in Q[1:]]
    need(c['partitions']==parts,'same categorical source projection')
    need(phase45 in (20,31),'only the two preregistered mathematical representatives')
    expected_family=[(3,0),(9,1),(15,10),(21,7),(45,phase45),(33,22),(35,0),(39,13),(63,49),(51,34),(57,19),(55,0),(105,70),(75,25),(69,46),(65,0),(99,22),(77,0),(85,0),(117,13),(95,0),(165,55),(91,0),(147,49),(225,175)]
    need(c['actual_family']==[list(z)for z in expected_family],'literal25 actual originals with only declared45phase changed')
    need(c['threshold']==16,'fixed h16; no threshold search')
    family=dict(c['actual_family']);selected=c['selected_labels']
    need(len(family)==len(c['actual_family'])==25 and len(selected)==len(set(selected))==23
         and set(selected)==set(family)-{3,9},'complete actual family and selected numerical labels')
    need(family[3]==0 and family[9]==1 and family[45]==phase45,'declared actual45phase and fixed anchors')
    patterns=list(product(range(3),*[range(2)for _ in Q[1:]]))
    C=[F(q-1,q-2)for q in Q];caps=[C[i]/q for i,q in enumerate(Q)]
    forced=set();deductions={}
    for m in selected:
        n=m;h=0
        while n%3==0:n//=3;h+=1
        rem=n;exponents=[]
        for q in Q:
            e=0
            while rem%q==0:rem//=q;e+=1
            exponents.append(e)
        D=sum(1<<i for i,e in enumerate(exponents)if e)
        need(rem==1 and n>1 and h<=2 and (h or D.bit_count()>1),'selected residual inventory membership')
        t=0 if not exponents[0]else(1 if exponents[0]==1 else 2)
        value=prod((C[i]for i,e in enumerate(exponents)if e),start=F(1))/n
        deductions[D,t,h]=deductions.get((D,t,h),F(0))+value
        for sid,s in enumerate(patterns):
            if all(family[m]%Q[i] in parts[i][s[i]]for i,e in enumerate(exponents)if e):
                for l,leaf in enumerate(LEAVES):
                    if leaf%3**h==family[m]%3**h:forced.add((l,sid))
    need(len(forced)==({20:712,31:711}[phase45]),'new literal selected-null count for declared45phase')
    T=F(c['tail']['expected_upper']);T29=1+F(28,27)*a4(29)
    need(T==F(4301685063112470380207,10**30),'unchanged complete804 tail')
    H0,Hr,Hv=(F(c['expected_hinge'][key])for key in ('H0','Hr','Hv'))
    need(min(H0,Hr,Hv)>=0,'nonnegative complete full-lambda hinge coefficients')
    probabilities=[[p]+[(caps[i],1-caps[i])for i in range(1,7)]for p in POINTS]
    blocks=[]
    for vi,pi in enumerate(probabilities):
        need(all(min(row)>0 and sum(row)==1 for row in pi),'three fully live source corners')
        need(all(value>C[i]/Q[i]**2 for i,row in enumerate(pi)for value in row),'all positive colours exceed deep cap')
        for i in range(1,7):
            need(all(min(caps[i],value)/caps[i]==1 for value in pi[i]),'other-six shallow multipliers all one')
        local=[]
        for D in range(128):
            ts=(1,2)if D&1 and vi<2 else(0,)
            for t in ts:
                beta=prod((F(1,Q[i]-2)for i in range(7)if D>>i&1 and(t==0 or i)),start=F(1))
                W=prod((C[i]*a4(Q[i])for i in range(7)if D>>i&1 and(t==0 or i)),start=F(1))
                if t:
                    beta*=caps[0]if t==1 else C[0]/(Q[0]*(Q[0]-1))
                    W*=15*caps[0]if t==1 else C[0]*(a4(Q[0])-F(15,Q[0]))
                for h in range(3):
                    deduction=(sum((value for (dd,tt,hh),value in deductions.items()if dd==D and hh==h),F(0))
                               if t==0 else deductions.get((D,t,h),F(0)))
                    loss=(beta if D and(h or D.bit_count()>1)else F(0))-deduction
                    if h==2:loss+=beta/2
                    need(loss>=0,'complete type inventory after exact selected-label subtraction')
                    debit=12*loss+27*T29*T*W*(1,15,216)[h]
                    need(debit>0,'all head-or-moment types retained')
                    local.append(dict(D=D,t=t,h=h,beta=beta,W=W,loss=loss,debit=debit))
        blocks.append(local)
    need(list(map(len,blocks))==[576,576,384],'exact capacity-depth compression at these three points')
    names=[('w',l)for l in range(5)]+[('r',),('v',),('epsilon',)]
    uid={}
    for l in range(5):
        for sid in range(192):
            if(l,sid)not in forced:uid[l,sid]=len(names);names.append(('u',l,sid))
    zid={}
    for vi,local in enumerate(blocks):
        for b in local:
            key=(vi,b['D'],b['t'],b['h']);zid[key]=len(names);names.append(('z',*key))
    need(len(uid)==960-len(forced) and len(zid)==1536 and len(names)==1544+len(uid),'complete phase-specific variable dimensions')
    rows=[]
    def add(label,terms,rhs=F(0)):
        merged={}
        for idx,coef in terms:
            if coef:merged[idx]=merged.get(idx,F(0))+coef
        rows.append((label,[(idx,v)for idx,v in sorted(merged.items())if v],rhs))
    for(l,sid),idx in uid.items():add(('retained_cap',l,sid),[(idx,F(1)),(l,F(-1))])
    for root in((0,1),(2,3,4)):add(('root_cap',*root),[(l,F(1))for l in root]+[(5,F(-1))])
    for l in range(5):add(('leaf_cap',l),[(l,F(1)),(6,F(-1))])
    add(('v_le_r',),[(6,F(1)),(5,F(-1))])
    menu=Counter();omitted=Counter();epi=Counter()
    for vi,pi in enumerate(probabilities):
        groups_by_D={}
        for D in range(128):
            inside=[i for i in range(7)if D>>i&1];outside=[i for i in range(7)if not D>>i&1]
            groups={}
            for sid,s in enumerate(patterns):
                key=tuple(s[i]for i in inside)
                p=prod((pi[i][s[i]]for i in outside),start=F(1))
                groups.setdefault(key,[]).append((sid,p))
            groups_by_D[D]=(inside,groups)
        for b in blocks[vi]:
            D,t,h=b['D'],b['t'],b['h'];inside,groups=groups_by_D[D]
            leafsets=(tuple(range(5)),)if h==0 else(((0,1),(2,3,4))if h==1 else tuple((l,)for l in range(5)))
            for kappa,matching in groups.items():
                multiplier=min(pi[0][kappa[0]],caps[0])/caps[0]if t==1 else F(1)
                need(0<multiplier<=1,'fixed live capacity multiplier')
                for ls in leafsets:
                    menu[vi,h]+=1
                    terms=[(uid[l,sid],multiplier*p)for l in ls for sid,p in matching if(l,sid)in uid]
                    if not terms:omitted[vi,h]+=1;continue
                    add(('epigraph',vi,D,t,h,kappa,ls),terms+[(zid[vi,D,t,h],F(-1))]);epi[vi,h]+=1
        mass=[prod((pi[i][s[i]]for i in range(7)),start=F(1))for s in patterns]
        need(sum(mass)==1,'same-source full pattern mass')
        add(('joint_slack',vi),[(7,F(1)),(5,Hr),(6,Hv)]+
            [(zid[vi,b['D'],b['t'],b['h']],b['debit'])for b in blocks[vi]]+
            [(idx,-12*mass[sid])for(l,sid),idx in uid.items()],-H0)
    need(sum(menu.values())==104976,'all collapsed common-colour menus')
    bounds=[(F(0),F(1))for _ in names];bounds[7]=(-(H0+Hr+Hv),F(12))
    control=[F(0)]*len(names);control[0]=control[5]=control[6]=F(1);control[7]=bounds[7][0]
    need(sum(control[:5])==1,'zero-kernel control normalization')
    for label,terms,rhs in rows:need(sum((v*control[i]for i,v in terms),F(0))<=rhs,'zero-kernel feasible row '+str(label))
    info=dict(scope='Build only: one common retained table on A/B/C at six other upper caps; no solver or full livebox certificate.',
              normalization='mu=nu_u restricted to U / nu_u(U); full-lambda hinge; capacity-aware retained fourth moment',
              points=[[list(map(str,p))for p in pi]for pi in probabilities],
              variables=len(names),variable_counts=dict(w=5,r=1,v=1,epsilon=1,u=len(uid),z=len(zid)),
              epigraph_types_per_point=list(map(len,blocks)),inequality_rows=len(rows),equality_rows=1,
              matrix_nonzeros=sum(len(t)for _,t,_ in rows),row_counts=dict(Counter(label[0]for label,_,_ in rows)),
              epigraph_menu_rows=sum(menu.values()),identicallyzero_query_rows_omitted=sum(omitted.values()),
              epigraph_rows_by_point_type=[[epi[vi,h]for h in range(3)]for vi in range(3)],
              H0=str(H0),Hr=str(Hr),Hv=str(Hv),T29=str(T29),T1600=str(T),epsilon_bounds=list(map(str,bounds[7])),
              objective='maximize epsilon',weight_equality='sum_l w_l = 1',
              joint_row='epsilon+Hr*r+Hv*v+sum_b(12loss_b+27T29*T1600*W_b*(1,15,216)_h)z_point,b -12M(pi_point,u) <= -H0',
              coefficient_blocks=[[{key:str(value)if isinstance(value,F)else value for key,value in b.items()}for b in local]for local in blocks],
              phase45=phase45,actual_family=c['actual_family'],selected_labels=selected,
              forced_zero_count=len(forced),allowed_retained_entries=len(uid),
              equality_terms=[[l,'1']for l in range(5)],equality_rhs='1',
              objective_terms=[[7,'1']],objective_direction='maximize',solver_calls=0,
              build_seconds=perf_counter()-started)
    # A solver must use this same explicit equality, box and semantic matrix.
    digest=hashlib.sha256()
    for item in (names,[[str(a),str(b)]for a,b in bounds],info['equality_terms'],info['equality_rhs'],info['objective_terms']):
        digest.update((json.dumps(item,separators=(',',':'))+'\n').encode())
    for label,terms,rhs in rows:
        digest.update((json.dumps([label,[[i,str(a)]for i,a in terms],str(rhs)],separators=(',',':'))+'\n').encode())
    info['semantic_matrix_sha256']=digest.hexdigest()
    return names,bounds,rows,info

def verify_dual(c,certificate):
    need(certificate['schema']=='e7-free45-h16-rational-weak-dual-v1' and certificate['phase45']==31,'declared phase31 exact dual')
    c31=dict(c);c31['actual_family']=[[m,31 if m==45 else a] for m,a in c['actual_family']]
    names,bounds,rows,info=build(c31,31)
    need(info['semantic_matrix_sha256']==certificate['semantic_matrix_sha256']=='01eda5c87b3a7d81ccc3bfb5c1e3a8cc14fc02af96f9c189c45d8a2950c21bd8','reconstructed complete phase31 semantic matrix')
    need(certificate['objective_terms']==info['objective_terms'] and certificate['epsilon_bounds']==info['epsilon_bounds'],'actual objective and epsilon box')
    multipliers={}
    for entry in certificate['inequality_multipliers']:
        i=entry['row_index'];value=F(entry['y'])
        need(type(i)is int and 0<=i<len(rows) and i not in multipliers,'unique valid sparse dualrow index')
        need(json.loads(json.dumps(rows[i][0]))==entry['label'] and value>0,'actual rowlabel and positive multiplier')
        multipliers[i]=value
    lam=F(certificate['equality_lambda']);residual=[F(0)]*len(names)
    for i,value in info['objective_terms']:residual[i]=F(value)
    bdot=F(0);points=Counter()
    for i,y in multipliers.items():
        label,terms,rhs=rows[i];bdot+=y*rhs
        for j,a in terms:residual[j]-=y*a
        if label[0]in('joint_slack','epigraph'):points[label[1]]+=1
    for i,value in info['equality_terms']:residual[i]-=lam*F(value)
    correction=[max(z*lo,z*hi) for z,(lo,hi) in zip(residual,bounds)]
    box=sum(correction,F(0));upper=bdot+lam*F(info['equality_rhs'])+box
    entries=[{'variable_index':i,'name':list(names[i]),'r':str(z),'box_correction':str(correction[i])} for i,z in enumerate(residual) if z]
    need(entries==certificate['residual'],'complete exact objective residual and actualbox correction')
    for key,value in [('b_dot_y',bdot),('lambda_rhs',lam*F(info['equality_rhs'])),('box_correction',box),('epsilon_upper',upper)]:need(F(certificate[key])==value,'exact weakdual '+key)
    joint=[{'row_index':i,'point':label[1],'y':str(multipliers.get(i,F(0)))} for i,(label,_,_) in enumerate(rows) if label[0]=='joint_slack']
    need(joint==certificate['joint_rows'] and [z['y'] for z in joint]==['0','0','1'],'Ccorner alone carries the weakdual')
    need(set(points)=={2} and {str(k):v for k,v in points.items()}==certificate['point_dependent_nonzero_rows'],'no A/Bsourcepoint rows used')
    need(upper<F(-9,50),'strict negative comparison upper bound below-9/50')
    return dict(phase45=31,semantic_matrix_sha256=info['semantic_matrix_sha256'],nonzero_y=len(multipliers),residual_nonzero=len(entries),
        joint_rows=joint,nonzero_source_points=sorted(points),epsilon_upper=str(upper),epsilon_upper_decimal=float(upper),
        box_correction=str(box),epsilon_residual=str(residual[7]),epsilon_box_correction=str(correction[7]),strict_upper='-9/50')

def verify_transport(c):
    pats=list(product(range(3),*[range(2) for _ in range(6)]));parts=c['partitions'];fixed=dict(c['actual_family'])
    def nulls(m,a):
        n=m;h=0
        while n%3==0:n//=3;h+=1
        axes=[i for i,q in enumerate(Q) if n%q==0]
        return {(l,sid) for l,leaf in enumerate(LEAVES) if leaf%3**h==a%3**h for sid,state in enumerate(pats) if all(a%Q[i] in parts[i][state[i]] for i in axes)}
    def swap(entry):
        l,sid=entry
        return ((1 if l==0 else 0 if l==1 else l),sid)
    parents={63:21,99:33,117:39,225:15};containments=[]
    for child,parent in parents.items():
        need(child%parent==0 and fixed[child]%parent==fixed[parent],'actual cylinder containment')
        need(nulls(child,fixed[child])<=nulls(parent,fixed[parent]),'categorical null inclusion')
        containments.append({'child':[child,fixed[child]],'parent':[parent,fixed[parent]]})
    base=set().union(*(nulls(m,a) for m,a in fixed.items() if m not in(3,9,45,*parents)))
    need({swap(z) for z in base}==base,'base selectednull union invariant under shortleaf swap')
    unions={}
    for phase in (31,16):
        unions[phase]=set().union(*(nulls(m,phase if m==45 else a) for m,a in fixed.items() if m not in(3,9)))
        need(len(unions[phase])==711,'same711 literal nullities for31/16')
    need({swap(z) for z in nulls(45,31)}==nulls(45,16),'actual45 categorical nulls transported')
    for l in range(5):
        for sid in range(192):need(((l,sid)in unions[31])==(swap((l,sid))in unions[16]),'all960 nullities transported')
    need(31%9==fixed[63]%9 and 16%9!=fixed[63]%9,'actual fixed-label tree orbit obstruction')
    need(31%5==16%5==1 and (31%9,16%9)==(4,7),'actual45local coordinates')
    return dict(short_leaf_permutation=[1,0,2,3,4],forced_count=711,actual_h2_cylinder_containments=containments,
        complete_selected_null_union_transport=True,comparison_interface_transport=True,actual_family_orbit_equivalence=False)

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--certificate',type=Path,default=Path(__file__).with_name('free45_phase20_kernel_certificate.json'))
    parser.add_argument('--dual',type=Path,default=Path(__file__).with_name('free45_phase31_dual_certificate.json'))
    parser.add_argument('--result',type=Path,default=Path(__file__).with_name('free45_live_cell_and_comparison_obstruction.json'))
    parser.add_argument('--write-result',action='store_true')
    args=parser.parse_args();c=read_json(args.certificate);d=read_json(args.dual)
    evaluator=Evaluator(c);rows=[]
    for vi in range(3):
        for mask in range(64):
            pi=[V5[vi]]+[(CAP[i],1-CAP[i]) if mask>>(i-1)&1 else(LOW[i],1-LOW[i]) for i in range(1,7)]
            row=evaluator.evaluate(pi);row.update(vertex5=vi,mask=mask);rows.append(row)
            need(0<F(row['L'])<=F(row['M'])<=1,'positive retained source lower bound')
            need(F(row['gate'])>F(9,125),'every192livevertex gate strictly greater than9/125')
    worst=min(rows,key=lambda row:F(row['gate']))
    dual=verify_dual(c,d);transport=verify_transport(c)
    output=dict(schema='e7-free45-live-cell-and-comparison-obstruction-v1',scope='phase20root-other fullylive sourcecell positive; phase31/16Ccorner thish16comparison negative; fixed other24originals and complete804support; no structuralzero cells or arbitrarymixed phases',
        candidate_sha256=hashlib.sha256(args.certificate.read_bytes()).hexdigest(),dual_sha256=hashlib.sha256(args.dual.read_bytes()).hexdigest(),
        normalization=c['normalization'],weights=c['weights'],phase20=dict(forced_zero_cells=712,nonzero_u=len(c['nonzero_u']),depth_types=2187,vertex_count=192,
        min_gate=worst['gate'],min_gate_decimal=worst['gate_decimal'],worst=[worst['vertex5'],worst['mask']],strict_gate_lower='9/125',distorted_surviving_mass_lower='1/375',rows=rows),
        phase31=dual,phase31_to16=transport,checks=CHECKS)
    if args.write_result:
        with args.result.open('x') as f:f.write(json.dumps(output,indent=2)+'\n')
    else:need(read_json(args.result)==output,'exact saved mathematical result replay')
    print(json.dumps({'checks':CHECKS,'phase20_vertices':192,'phase20_min_gate':worst['gate_decimal'],'phase31_epsilon_upper':dual['epsilon_upper_decimal'],'phase31_supports_only_C':True,'result_matches':not args.write_result},indent=2))

if __name__=='__main__':main()
