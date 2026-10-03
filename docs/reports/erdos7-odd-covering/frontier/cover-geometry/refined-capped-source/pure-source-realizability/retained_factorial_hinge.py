"""Complete retained factorial hinge and one fixed-candidate failure certificate.
Standalone standard-library replay. Exact finite controls, full heights,
oneCpoint old/new diagnostic, and an analytic all-threshold obstruction.
"""
from fractions import Fraction as F
from itertools import product
from math import lcm,prod,isqrt,factorial,comb,gcd
from collections import Counter
from pathlib import Path
from time import perf_counter
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

def a2(q):
    return F(3,q-1)+F(2,(q-1)**2)

class Evaluator:
    def __init__(self,c):
        self.api_checks=0
        need(c['normalization']=='nu_u restricted to U / nu_u(U)','retained normalized survivor')
        self.patterns=list(product(range(3),*[range(2) for q in Q[1:]]))
        leaves=(4,7,2,5,8)
        family=[(3,0),(9,1),(15,10),(21,7),(45,31),(33,22),(35,0),(39,13),
            (63,49),(51,34),(57,19),(55,0),(105,70),(75,25),(69,46),(65,0),(99,22),
            (77,0),(85,0),(117,13),(95,0),(165,55),(91,0),(147,49),(225,175)]
        parts=[[[0],[1],[2,3,4]]]+[[[0],list(range(1,q))] for q in Q[1:]]
        need(c['primes']==list(Q) and c['leaves']==list(leaves),'same literal coordinates')
        need(c['actual_family']==[list(z) for z in family] and c['phase45']==31,'new literal phase31 family; all24 originals fixed')
        need(c['partitions']==parts and c['selected_labels']==[m for m,a in family[2:]],'literal categorical projection and selected labels')
        self.w=tuple(map(F,c['weights']))
        need(self.w==tuple(F(x,10**8) for x in (21173425,21173425,19217717,19217717,19217716)),'same deterministic rational candidate weights')
        need(sum(self.w)==1 and min(self.w)>0,'normalized five leaf weights')
        self.unit=lcm(*(F(z['u']).denominator for z in c['nonzero_u']))
        self.UI=[[0]*192 for _ in leaves];seen=set()
        for row in c['nonzero_u']:
            l,sid=row['leaf_index'],row['pattern_id'];value=F(row['u'])
            need(type(l)is int and type(sid)is int and 0<=l<5 and 0<=sid<192,'retained index range')
            need((l,sid)not in seen and 0<value<=self.w[l],'unique retained cell between0 and leaf weight')
            seen.add((l,sid));self.UI[l][sid]=int(value*self.unit)
        need(len(seen)==106,'fixed106 positive entries')
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
        need(len(forced)==711 and all(self.UI[l][sid]==0 for l,sid in forced),'all711 new selected-null cells exactly zero')
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
        self.deductions=deductions
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
                V=prod((3*CAP[i] if S>>i&1 else C[i]*(a2(Q[i])-F(3,Q[i])) for i in inside),start=F(1))
                fcoeff=(V-B,3*V-B,9*V-F(3,2)*B)
                need(min(fcoeff)>=0,'complete nonnegative global-distinct pair coefficients')
                types.append((tuple(i for i in inside if S>>i&1),tuple(j for j,i in enumerate(inside)if S>>i&1),W,losses,B,V,fcoeff))
            self.supports.append((inside,outside,keys,memberships,types))
        need(sum(len(s[-1])for s in self.supports)==2187,'complete3depthtypes per coordinate')


    def evaluate_C(self):
        pi=[V5[2]]+[(CAP[i],1-CAP[i]) for i in range(1,7)]
        for i,row in enumerate(pi):
            need(sum(row)==1 and min(row)>C[i]/Q[i]**2,'declared liveCsource')
            need(all(min(p,CAP[i])/CAP[i]==1 for p in row),'C allshallow capacity multipliers exactlyone')
        den=[lcm(*(p.denominator for p in row)) for row in pi]
        nums=[[int(p*d) for p in row] for row,d in zip(pi,den)]
        loss=moment=factorial=F(0);mass=None;closs=cmoment=cfactorial=F(0);rows=[];ntypes=0
        for D,(inside,outside,keys,memberships,types) in enumerate(self.supports):
            groups=[[0]*5 for _ in keys]
            for sid,state in enumerate(self.patterns):
                fac=prod(nums[i][state[i]] for i in outside);g=groups[memberships[sid]]
                for l in range(5):g[l]+=fac*self.UI[l][sid]
            denominator=self.unit*prod(den[i] for i in outside)
            if not inside:mass=F(sum(groups[0]),denominator)
            vector=[(sum(g),max(g[0]+g[1],sum(g[2:])),max(g)) for g in groups]
            env=tuple(F(max(z[h] for z in vector),denominator) for h in range(3))
            need(min(env)>=0 and max(env)<=1,'sameC commoncolour envelopes')
            lf=kf=ff=F(0)
            for active,pos,W,losses,B,V,fcoeff in types:
                ntypes+=1
                lf+=sum((a*b for a,b in zip(losses,env)),F(0))
                kf+=W*(env[0]+15*env[1]+216*env[2])
                ff+=sum((a*b for a,b in zip(fcoeff,env)),F(0))
            loss+=lf;moment+=kf;factorial+=ff
            # Separate closed coefficient reconstruction, not a second sourcepoint.
            bc=prod((C[i]/(Q[i]-1) for i in inside),start=F(1))
            vc=prod((C[i]*a2(Q[i]) for i in inside),start=F(1))
            wc=prod((C[i]*a4(Q[i]) for i in inside),start=F(1))
            fc=(vc-bc,3*vc-bc,9*vc-F(3,2)*bc);lc=[]
            for h in range(3):
                selected=sum((v for(dd,ss,hh),v in self.deductions.items() if dd==D and hh==h),F(0))
                value=(bc if D and(h or len(inside)>1) else F(0))-selected
                if h==2:value+=bc/2
                lc.append(value)
            cl=sum((a*b for a,b in zip(lc,env)),F(0));ck=wc*(env[0]+15*env[1]+216*env[2]);cf=sum((a*b for a,b in zip(fc,env)),F(0))
            need(lf==cl and kf==ck and ff==cf,'fulltypes agree with independent complete384coefficient reconstruction')
            closs+=cl;cmoment+=ck;cfactorial+=cf
            rows.append({'support':D,'depth_types':len(types),'envelopes':list(map(str,env)),'B_complete':str(bc),'V_complete':str(vc),'W_complete':str(wc),'factorial_coefficients':list(map(str,fc)),'loss_contribution':str(lf),'K4_contribution':str(kf),'F2_contribution':str(ff)})
        need(ntypes==2187 and len(rows)*3==384,'all2187types and384samepoint responses')
        need(loss==closs and moment==cmoment and factorial==cfactorial,'complete inventories identity')
        need(rows[0]['factorial_coefficients']==['0','2','15/2'],'empty support querypairs retained')
        L=mass-loss;tail=27*self.T29*self.T*moment;newH=factorial/62
        oldGate=12*L-self.H-tail;newGate=12*L-newH-tail
        need(F(0)<mass<=1 and L<=mass and factorial>=0,'sameC finite source quantities')
        need(newGate-oldGate==self.H-newH,'onlyhinge changed under same source')
        values=dict(M=mass,loss=loss,L=L,K4=moment,oldH16=self.H,F2=factorial,newH16=newH,tail=tail,oldGate=oldGate,newGate=newGate,hingeImprovement=self.H-newH)
        return {'point':{'name':'C','vertex5':2,'other_mask':63,'probabilities':[[str(p) for p in row] for row in pi]},
            'exact':{k:str(v) for k,v in values.items()},'decimal':{k:float(v) for k,v in values.items()},
            'success':newGate>0,'success_criterion':'strict newGate>0','scope':'one fixed rational31proposal atC; no sourcecell positivity or universalnegative conclusion',
            'nonternary_depth_types':ntypes,'collapsed_samepoint_responses':384,'full_vs_collapsed_identity':True,'support_rows':rows}


def finite_controls():
    startchecks=CHECKS
    # Integer hinge, exact identity, sharp equality, and real-number failure control.
    integer_checks=0
    for h in range(1,65):
     for n in range(4*h+4):
      need(2*(2*h-1)*max(n-h,0)<=n*(n-1),'integer factorial hinge')
      integer_checks+=1
      if n>=h:need(n*(n-1)-2*(2*h-1)*(n-h)==(n-(2*h-1))*(n-2*h),'exact adjacent-root identity')
     for n in (2*h-1,2*h):need(2*(2*h-1)*max(n-h,0)==n*(n-1),'sharp integer equality')
     x=F(4*h-1,2)
     need(x*(x-1)-2*(2*h-1)*(x-h)==F(-1,4),'noninteger counterexample protects domain')
    # Enumerate ordered numerical exponent-label pairs before any cap is applied.
    pair_rows=[]
    for dim in range(1,5):
     labels=list(product(range(4),repeat=dim));counts=Counter();allcounts=Counter()
     for a in labels:
      for b in labels:
       e=tuple(max(x,y) for x,y in zip(a,b));allcounts[e]+=1
       if a!=b:counts[e]+=1
     for e in labels:
      need(allcounts[e]==prod(2*z+1 for z in e),'complete ordered maximum-depth multiplicity')
      need(counts[e]==prod(2*z+1 for z in e)-1,'one global diagonal removed per maximum-depth vector')
     need(sum(counts.values())==len(labels)*(len(labels)-1),'all distinct labels exactly once')
     pair_rows.append({'axes':dim,'labels':len(labels),'ordered_distinct_pairs':sum(counts.values())})
    need((2*1+1)*(2*1+1)-1==8 and (2*1)*(2*1)==4,'coordinatewise diagonal deletion is invalid')
    Q=(5,7,11,13,17,19,23);C=tuple(F(q-1,q-2) for q in Q)
    def a2(q):return F(3,q-1)+F(2,(q-1)**2)
    def weighted_tail(q,E):
     z=F(1,q)
     return z**E*((2*E+1)/(1-z)+2*z/(1-z)**2)
    for q in (3,*Q):
     for E in range(1,13):
      prefix=sum((F(2*e+1,q**e) for e in range(1,E)),F(0))
      need(prefix+weighted_tail(q,E)==a2(q),'complete pair series with exact remainder')
    need(9*weighted_tail(3,2)==9,'complete ternary deep pair coefficient')
    need(sum((F(1,3**j) for j in range(2,8)),F(0))+F(1,3**8)/(1-F(1,3))==F(1,6),'complete ternary deep diagonal series')
    need(9*F(1,6)==F(3,2),'ternary deep diagonal coefficient')
    types=[]
    for ts in product(range(3),repeat=7):
     B=V=F(1)
     for i,t in enumerate(ts):
      if not t:continue
      q,cap=Q[i],C[i]
      b=cap/q if t==1 else cap/(q*(q-1))
      v=3*cap/q if t==1 else cap*(a2(q)-F(3,q))
      need(v/b==(3 if t==1 else 5+F(2,q-1)),'exact local pair/diagonal ratio')
      B*=b;V*=v
     coeff=(V-B,3*V-B,9*V-F(3,2)*B)
     need(min(coeff)>=0,'all aggregated global-distinct coefficients nonnegative')
     types.append({'depth_type':ts,'B':str(B),'V':str(V),'F2_coefficients':list(map(str,coeff))})
    need(len(types)==2187 and types[0]['F2_coefficients']==['0','2','15/2'],'empty support and complete type inventory')
    need(sum((F(z['B']) for z in types),F(0))==prod((1+cap/(q-1) for q,cap in zip(Q,C)),start=F(1)),'complete diagonal reconstruction')
    need(sum((F(z['V']) for z in types),F(0))==prod((1+cap*a2(q) for q,cap in zip(Q,C)),start=F(1)),'complete pair reconstruction')
    # One literal layout on a two-prime finite carrier, with one phase per label.
    labels=[3**i*5**j for i,j in product(range(3),repeat=2)];period=225
    phases={m:(i*i+2*i+1)%m for i,m in enumerate(labels)}
    weights=[x%7+1 for x in range(period)];total=sum(weights)
    loadsum=pairmass=0
    for x in range(period):
     hits={m for m in labels if x%m==phases[m]};n=len(hits)
     pairs=sum((x%m==phases[m] and x%k==phases[k]) for m in labels for k in labels if m!=k)
     need(pairs==n*(n-1),'one globally fixed layout identity')
     loadsum+=weights[x]*n*(n-1)
    for m in labels:
     for k in labels:
      if m==k:continue
      intersection=sum(weights[x] for x in range(period) if x%m==phases[m] and x%k==phases[k])
      pairmass+=intersection
      need(intersection==0 or phases[m]%gcd(m,k)==phases[k]%gcd(m,k),'compatible pair retains common residue')
    need(loadsum==pairmass,'same measure factorial expansion after integration')
    # Mixing two independently phased layouts does not have the same diagonal.
    qa=lambda x:1+int(x%3==0)
    qb=lambda x:1+int(x%3==1)
    need(sum(qa(x)*qb(x)-qa(x) for x in range(3))!=sum(int(x%3==0)+int(x%3==1) for x in range(3)),'mixed-layout subtraction failure control')
    out={'scope':'Elementary integer hinge and all-height distinct-label maximum-depth inventory; no candidate/sourcegate/optimizer evaluation',
     'integer_cases':integer_checks,'maximum_depth_pair_controls':pair_rows,'complete_nonternary_types':2187,'empty_support_coefficients':['0','2','15/2'],
     'ternary_second_moment_coefficients':['1','3','9'],'ternary_diagonal_coefficients':['1','1','3/2'],
     'finite_layout':{'period':period,'labels':labels,'phases':[[m,phases[m]] for m in labels],'factorial_integral':str(F(loadsum,total))},
     'complete_type_coefficients_sha256':hashlib.sha256(json.dumps(types,separators=(',',':')).encode()).hexdigest(),'checks':CHECKS-startchecks}
    return out

def all_threshold_obstruction(diagnostic):
    values={k:F(v) for k,v in diagnostic['exact'].items()}
    L,F2,tail=values['L'],values['F2'],values['tail']
    A=F(55,2)*L-tail;LF2=L*F2;gap=LF2-A*A
    need(L>0 and F2>0 and A>0 and gap>0,'onefixedcandidate analytic AMGM allthreshold obstruction')
    need(values['newGate']<0 and values['newH16']>values['oldH16'],'fixedCfactorial upper bound isnot automatic improvement')
    return {'formula':'G(h)=(55/2)L-tail-L(h-1/2)-F2/[4(h-1/2)] <= A-sqrt(L*F2)',
        'range':'AMGM on real h>1/2; factorial-hinge conclusion used only for integer h1..27',
        'A':str(A),'A_decimal':float(A),'L_times_F2':str(LF2),'L_times_F2_minus_A_squared':str(gap),'square_gap_decimal':float(gap),
        'all_valid_integer_thresholds_strictly_negative':True,'threshold_gate_scan_performed':False,
        'scope':'Only thisfixedrationalcandidate atC; no allkernel obstruction and no other source evaluation.'}

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--certificate',type=Path,default=Path(__file__).with_name('retained_factorial_hinge_certificate.json'))
    parser.add_argument('--result',type=Path,default=Path(__file__).with_name('retained_factorial_hinge.json'))
    parser.add_argument('--write-result',action='store_true')
    args=parser.parse_args();c=read_json(args.certificate)
    need(c['schema']=='e7-retained-factorial-hinge-fixed-candidate-v1','declared mathematical certificate')
    controls=finite_controls();evaluator=Evaluator(c);diagnostic=evaluator.evaluate_C();obstruction=all_threshold_obstruction(diagnostic)
    result={'schema':'e7-retained-factorial-hinge-result-v1','scope':'complete single-layout retained factorial bridge; fixedphase31Cproposal fails; no allkernel or actualcover conclusion',
        'certificate_sha256':hashlib.sha256(args.certificate.read_bytes()).hexdigest(),'normalization':c['normalization'],'phase45':31,'weights':c['weights'],'nonzero_u':len(c['nonzero_u']),
        'forcedzero_count':711,'weight_sum':str(sum(map(F,c['weights']))),'finite_controls':controls,'fixed_candidate_C':diagnostic,'all_threshold_obstruction':obstruction,'checks':CHECKS}
    if args.write_result:
        with args.result.open('x') as f:f.write(json.dumps(result,indent=2)+'\n')
    else:need(read_json(args.result)==result,'exact stored mathematical result replay')
    print(json.dumps({'checks':CHECKS,'old_hinge':diagnostic['decimal']['oldH16'],'factorial_hinge':diagnostic['decimal']['newH16'],
        'old_gate':diagnostic['decimal']['oldGate'],'new_gate':diagnostic['decimal']['newGate'],'all_useful_integer_thresholds_fail':True,'exact_result_matches':not args.write_result},indent=2))

if __name__=='__main__':main()
