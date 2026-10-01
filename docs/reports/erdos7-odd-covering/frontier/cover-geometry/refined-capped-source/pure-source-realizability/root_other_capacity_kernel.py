"""Replay one all-height queried-capacity certificate on the actual live cell.
Standard library only; no optimizer, floating inference, or source search.
Uses the existing parent-directory Report814 source and evaluator.
"""
from fractions import Fraction as F
from itertools import product
from math import lcm,prod
from pathlib import Path
import argparse,importlib.util,json

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

class Evaluator:
    def __init__(self,c,source_dir):
        need(c['normalization']=='nu_u restricted to U / nu_u(U)','retained normalized survivor')
        expected_family=[(3,0),(9,1),(15,10),(21,7),(45,11),(33,22),(35,0),(39,13),(63,49),(51,34),(57,19),(55,0),(105,70),(75,25),(69,46),(65,0),(99,22),(77,0),(85,0),(117,13),(95,0),(165,55),(91,0),(147,49),(225,175)]
        need([tuple(x)for x in c['actual_family']]==expected_family,'literal25 actual opposing-phase originals')
        spec=importlib.util.spec_from_file_location('literal_source814',source_dir/'three_kernel_atlas_counterexample.py')
        api=importlib.util.module_from_spec(spec);spec.loader.exec_module(api)
        _,leaves,self.patterns,self.w,U,self.UI,self.unit,beta,R,proj,nforced=api.setup(c)
        need(nforced==750 and len(c['nonzero_u'])==135,'same selected-null table,135 positive entries')
        self.r=max(sum(self.w[:2]),sum(self.w[2:]));self.v=max(self.w)
        H0,Hr,Hv=api.hinge_coefficients(Q,16)
        self.H=H0+Hr*self.r+Hv*self.v
        self.T=api.exact_tail(c['tail']);self.T29=1+F(28,27)*api.a4(29)
        need(c['threshold']==16 and self.T==F(4301685063112470380207,10**30),'same complete h16 comparison')
        for key,value in dict(H0=H0,Hr=Hr,Hv=Hv).items():need(F(c['expected_hinge'][key])==value,'complete hinge '+key)
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
                W=prod((15*CAP[i]if S>>i&1 else C[i]*(api.a4(Q[i])-F(15,Q[i]))for i in inside),start=F(1))
                losses=[]
                for h in range(3):
                    val=(B if D and(h or len(inside)>1)else F(0))-deductions.get((D,S,h),F(0))
                    if h==2:val+=B/2
                    need(val>=0,'nonnegative full residual depth-type coefficient')
                    losses.append(val)
                types.append((tuple(i for i in inside if S>>i&1),tuple(j for j,i in enumerate(inside)if S>>i&1),W,losses))
            self.supports.append((inside,outside,keys,memberships,types))
        self.api_checks=api.CHECKS
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

def main():
    parser=argparse.ArgumentParser()
    here=Path(__file__).resolve().parent
    parser.add_argument('--source-dir',type=Path,default=here.parent)
    parser.add_argument('--certificate',type=Path,default=here/'root_other_capacity_kernel_certificate.json')
    parser.add_argument('--result',type=Path,default=here/'root_other_capacity_kernel.json')
    parser.add_argument('--write-result',action='store_true')
    args=parser.parse_args()
    certificate=read_json(args.certificate)
    need(certificate['schema']=='e7-root-other-capacity-kernel-v1','certificate schema')
    source=read_json(args.source_dir/'three_kernel_atlas_counterexample_certificate.json')
    need(source['schema']==certificate['source_schema']=='e7-three-kernel-atlas-counterexample-v1','existing814 source dependency')
    need(source['normalization']=='mu=lambda_w restricted to U / lambda_w(U)','literal814 source contract')
    need(certificate['hinge_comparison']=='full product lambda_w dominates retained nu_u' and
         certificate['moment_comparison']=='same-source retained nu_u all-height queried-colour capacity',
         'one declared mixed hinge/moment comparison')
    need(certificate['pure5_deleted_roots']==[2,3,4] and
         certificate['other_reference_roots']=='all six reference roots0 remain live',
         'actual-source structural cell')
    need(certificate['prime_support']=='3,5,7,11,13,17,19,23,29 and any finite set of primes strictly above1600; primes31..1600 excluded',
         'continuation support scope')
    need(tuple(tuple(map(F,row))for row in certificate['q5_vertices'])==V5,'literal root-other source triangle')
    need(len(certificate['binary_live_intervals'])==6,'all six live intervals')
    for i,item in enumerate(certificate['binary_live_intervals'],1):
        need(item['q']==Q[i] and F(item['lower'])==LOW[i] and F(item['upper'])==CAP[i],
             'actual live binary interval endpoints')
        need(LOW[i]>C[i]/Q[i]**2 and 1-CAP[i]>CAP[i],'one fixed all-height capacity branch')
    need(min(x for v in V5 for x in v)>C[0]/Q[0]**2 and
         all(v[0]<=CAP[0] and v[1]<=CAP[0] and v[2]>CAP[0]for v in V5),
         'quinary live branches fixed throughout the triangle')
    need(certificate['expected_vertices']==192,'complete product vertex count')
    need(F(certificate['gate_floor'])==F(9,250) and F(certificate['final_mass_floor'])==F(1,750),
         'declared strict gate and final mass floors')
    need(F(certificate['gate_floor'])/27==F(certificate['final_mass_floor']),
         'same retained survivor final lower-bound arithmetic')
    c=dict(source['common'],weights=certificate['weights'],nonzero_u=certificate['nonzero_u'],
           normalization=certificate['normalization'])
    evaluator=Evaluator(c,args.source_dir)
    rows=[]
    for vi in range(3):
        for mask in range(64):
            pi=[V5[vi]]+[(CAP[i],1-CAP[i])if mask>>(i-1)&1 else(LOW[i],1-LOW[i])for i in range(1,7)]
            row=evaluator.evaluate(pi)
            need(F(row['gate'])>F(certificate['gate_floor']),'strict positive common gate at every product vertex')
            need(0<F(row['L'])<=F(row['M'])<=1,'valid positive retained source floor')
            row.update(vertex5=vi,mask=mask);rows.append(row)
    need(len(rows)==192,'complete three-by64 source cover')
    worst=min(rows,key=lambda row:F(row['gate']))
    need(worst['gate']==certificate['expected_min_gate'] and
         [worst['vertex5'],worst['mask']]==certificate['expected_worst_vertex']==[1,63],
         'exact global minimum and its source vertex')
    full=sum(F(entry['u'])==evaluator.w[entry['leaf_index']]for entry in c['nonzero_u'])
    need(full==4,'four full-weight and131 partial positive entries')
    summary=[]
    for vi in range(3):
        candidates=[row for row in rows if row['vertex5']==vi]
        low=min(candidates,key=lambda row:F(row['gate']))
        summary.append(dict(vertex5=vi,positive_count=64,min_gate=low['gate'],min_gate_decimal=low['gate_decimal'],worst_mask=low['mask']))
    result=dict(schema='e7-root-other-capacity-kernel-result-v1',normalization=c['normalization'],
                weights=c['weights'],nonzero_u=135,full_weight_entries=4,partial_weight_entries=131,
                vertices=192,positive_count=192,summary=summary,rows=rows,
                min_gate=worst['gate'],min_gate_decimal=worst['gate_decimal'],worst=[worst['vertex5'],worst['mask']],
                gate_floor=certificate['gate_floor'],final_mass_floor=certificate['final_mass_floor'],
                min_gate_over27=str(F(worst['gate'])/27),checks=CHECKS+evaluator.api_checks,
                scope='one fixed retained source throughout actual pure5-root-other triangle times six live reference-root intervals; full h16 hinge, all-height retained fourth moment and complete allowed tail; no other source cells or unrestricted covering claim')
    if args.write_result:args.result.write_text(json.dumps(result,indent=2)+'\n')
    else:need(read_json(args.result)==result,'exact saved result replay')
    print(json.dumps({k:result[k]for k in ('vertices','positive_count','min_gate_decimal','worst','gate_floor','final_mass_floor','checks')},indent=2))

if __name__=='__main__':main()
