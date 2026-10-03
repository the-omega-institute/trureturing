#!/usr/bin/env python3
"""Exact structural source atlas using fixed814 quarter and821 retained tables.
Replays the assigned39+2148 vertices. Standard library only; no optimizer.
"""
from fractions import Fraction as F
from itertools import product
from math import lcm,prod
from pathlib import Path
import argparse,hashlib,importlib.util,json

Q=(5,7,11,13,17,19,23)
C=tuple(F(q-1,q-2)for q in Q)
CAP=tuple(C[i]/q for i,q in enumerate(Q))
LOW=tuple(F(q-2,q*q-q-1)for q in Q)
V5=((F(1,5),F(4,15),F(8,15)),(F(4,15),F(1,5),F(8,15)),(F(4,15),F(4,15),F(7,15)))
CHECKS=0

def need(ok,label):
    global CHECKS
    CHECKS+=1
    if not ok:raise ValueError(label)

def read_json(path):
    def unique(pairs):
        out={}
        for k,v in pairs:
            if k in out:raise ValueError('duplicate JSON key '+k)
            out[k]=v
        return out
    return json.loads(path.read_text(),object_pairs_hook=unique)

def load_module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    api=importlib.util.module_from_spec(spec);spec.loader.exec_module(api);return api

def queried_maxima(keys,root_leaf,inside,pi,active_ratios,rnums):
    maxes=[0,0,0]
    for digits,base in zip(keys,root_leaf):
        # This support guard includes every queried coordinate, even when it
        # is deep and absent from active_ratios. Shallow clipping alone fails.
        if any(pi[i][colour]==0 for i,colour in zip(inside,digits)):continue
        factor=prod(rnums[i][digits[j]]for i,j in active_ratios)
        for h in range(3):maxes[h]=max(maxes[h],factor*base[h])
    return maxes

class CapacityEvaluator:
    def __init__(self,base,c,source_dir):
        prepared=base.Evaluator(c,source_dir)
        self.__dict__.update(prepared.__dict__)

    def evaluate(self,pi):
        for i,row in enumerate(pi):
            need(sum(row)==1 and min(row)>=0 and all(x==0 or x>C[i]/Q[i]**2 for x in row),
                 'one normalized actual zero-or-live source law')
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
                maxes=queried_maxima(keys,root_leaf,inside,pi,key,rnums)
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
    parser.add_argument('--kernel-dir',type=Path,default=here)
    parser.add_argument('--certificate',type=Path,default=here/'pure_source_structural_atlas_certificate.json')
    parser.add_argument('--result',type=Path,default=here/'pure_source_structural_atlas.json')
    parser.add_argument('--write-result',action='store_true')
    args=parser.parse_args()
    cert=read_json(args.certificate)
    need(cert['schema']=='e7-pure-source-structural-atlas-v1','atlas schema')
    saved=None if args.write_result else read_json(args.result)
    if saved is not None:
        if saved.get('vertices')!=2187 or saved.get('positive_vertices')!=2187 or len(saved.get('rows',[]))!=2187:
            raise ValueError('saved result must contain the complete positive atlas')
        for row in saved['rows']:
            branch=row.get('branch')
            if branch not in('quarter','retained') or F(row['gate'])<=F(cert[branch+'_gate_floor']):
                raise ValueError('saved result violates its assigned strict gate floor')
    need(cert['structural_rule']=='pure5 removes2/3/4: at mostone live other reference root uses quarter; at leasttwo use821 retained',
         'one table assigned by whole structural cell')
    need(cert['q5_vertices']==[list(map(str,p))for p in V5] and cert['other_primes']==list(Q[1:]),'actual source cell coordinates')
    need(cert['endpoint_codes']=='0=deleted reference;1=actual live lower;2=live upper cap','literal zero/live endpoint code')
    need(cert['expected_cells']==dict(quarter=7,retained=57,total=64) and
         cert['expected_vertices']==dict(quarter=39,retained=2148,total=2187),'complete disjoint structural partition')
    need(F(cert['quarter_gate_floor'])==F(6,25) and F(cert['retained_gate_floor'])==F(7,500),
         'fixed strict assigned gate floors')
    need(F(cert['root_other_mass_floor'])==F(7,13500) and F(cert['all_pure_mass_floor'])==F(1,2000),
         'fixed distorted surviving mass floors')
    need(min(F(cert['quarter_gate_floor']),F(cert['retained_gate_floor']))/27==F(cert['root_other_mass_floor'])
         and F(cert['root_other_mass_floor'])>F(cert['all_pure_mass_floor']),
         'same-denominator branch lower bounds imply common mass floor')
    expected_cases=dict(pure5_absent='Report819;C5=20/19 consistently;complete reserve>29/100',
        pure5_reference='Report817;actual phase0/1;complete source atlas;mass>1/800',
        pure5_other='This certificate;actual phase2/3/4;all64 zero/live patterns;mass>7/13500')
    need(cert['external_source_cases']==expected_cases,'precise separately proved source-case premises')
    need(min(F(29,100),F(1,800),F(cert['root_other_mass_floor']))>F(cert['all_pure_mass_floor']),
         'arithmetic composition with Report817/819 bounds; their theorems are separate premises')
    need(cert['scope']=='Fixed25 actual anchor/selected originals including23 mixed phases; arbitrary finite old pure inventories and other allowed head originals; support3..23,29,and finite primes>1600; primes31..1600 excluded; no arbitrary mixed-phase claim',
         'fixed phases and prime support')
    api=load_module('atlas_source814',args.source_dir/'three_kernel_atlas_counterexample.py')
    source=read_json(args.source_dir/'three_kernel_atlas_counterexample_certificate.json')
    need(source['schema']==cert['source814_schema']=='e7-three-kernel-atlas-counterexample-v1','shared literal814 source')
    need(source['normalization']==cert['quarter_normalization']=='mu=lambda_w restricted to U / lambda_w(U)',
         'quarter full-source normalization')
    common=source['common']
    retained_path=args.kernel_dir/'root_other_capacity_kernel_certificate.json'
    retained_hash=hashlib.sha256(retained_path.read_bytes()).hexdigest()
    need(retained_hash==cert['retained_certificate_sha256']=='b751e98a9e879887a6651e2e0d3e72db21b3af2e65ebc473edeb1f841a4185b5',
         'unchanged135-entry821 rational table')
    retained=read_json(retained_path)
    need(retained['normalization']==cert['retained_normalization']=='nu_u restricted to U / nu_u(U)',
         'retained branch uses its own source denominator')
    base=load_module('atlas_kernel821',args.kernel_dir/'root_other_capacity_kernel.py')
    rc=dict(common,weights=retained['weights'],nonzero_u=retained['nonzero_u'],normalization=retained['normalization'])
    evaluator=CapacityEvaluator(base,rc,args.source_dir)
    need(cert['quarter_kernel']=='quarter','assigned fixed quarter table')
    quarter=next(k for k in source['kernels']if k['name']=='quarter')
    _,leaves,patterns,w,U,UI,scale,beta,R,projections,forced=api.setup(dict(common,weights=quarter['weights'],nonzero_u=quarter['nonzero_u']))
    need(w==(F(1,4),F(1,4),F(1,6),F(1,6),F(1,6)) and forced==750 and len(quarter['nonzero_u'])==210 and
         all(F(e['u'])==w[e['leaf_index']]for e in quarter['nonzero_u']),
         'entire old K8-allowed quarter table')
    need(common['threshold']==16,'fixed common h16 gate')
    H0,Hr,Hv=api.hinge_coefficients(Q,16);T=api.exact_tail(common['tail'])
    T29=1+F(28,27)*api.a4(29)
    Kq=prod((1+C[i]*api.a4(q)for i,q in enumerate(Q)),start=F(1))*T29
    for key,val in dict(H0=H0,Hr=Hr,Hv=Hv,Kq=Kq,T1600=T).items():
        need(F(common['expected_hinge'][key])==val,'complete full-source comparison '+key)
    r=max(sum(w[:2]),sum(w[2:]));v=max(w)
    quarter_H=H0+Hr*r+Hv*v;quarter_K=Kq*(1+15*r+216*v);quarter_tail=27*quarter_K*T
    # A positive response on a source-dead queried colour must vanish at both
    # shallow and deep depths. The unguarded deep maximum would be5 here.
    live=[V5[0]]+[(CAP[i],1-CAP[i])for i in range(1,7)]
    dead=list(live);dead[1]=(F(0),F(1))
    keys=[(0,),(1,)];responses=[(5,3,2),(0,0,0)]
    nums=[[1]*len(row)for row in live];nums[1]=[0,1]
    need(queried_maxima(keys,responses,(1,),dead,(),nums)==[0,0,0],'dead deep colour cannot survive')
    need(queried_maxima(keys,responses,(1,),dead,((1,0),),nums)==[0,0,0],'dead shallow colour cannot survive')
    nums[1]=[1,1]
    need(queried_maxima(keys,responses,(1,),live,(),nums)==[5,3,2] and max(row[0]for row in responses)==5,
         'live deep control and genuine sensitivity to dead support')
    for i in range(1,7):
        need(0<LOW[i]<=CAP[i] and LOW[i]>C[i]/Q[i]**2 and 1-CAP[i]>CAP[i],
             'disjoint zero/live components and fixed all-height branches')
    cells=[]
    for mask in range(64):
        count=mask.bit_count();branch='quarter'if count<=1 else'retained'
        cells.append(dict(live_mask=mask,branch=branch,expected_vertices=3*2**count))
    need(sum(c['branch']=='quarter'for c in cells)==7 and sum(c['expected_vertices']for c in cells if c['branch']=='quarter')==39,
         'seven whole quarter cells and39 assigned vertices')
    need(sum(c['branch']=='retained'for c in cells)==57 and sum(c['expected_vertices']for c in cells if c['branch']=='retained')==2148,
         '57whole retained cells and2148 assigned vertices')
    rows=[];by_cell={mask:[]for mask in range(64)};by_branch={'quarter':[],'retained':[]}
    for vi in range(3):
        for codes in product(range(3),repeat=6):
            mask=sum((code!=0)<<j for j,code in enumerate(codes))
            branch=cells[mask]['branch']
            pi=[V5[vi]]
            for i,code in enumerate(codes,1):
                value=(F(0),LOW[i],CAP[i])[code];pi.append((value,1-value))
            if branch=='quarter':
                L,detail=api.evaluate(pi,patterns,UI,scale,beta,R,projections)
                gate=12*L-quarter_H-quarter_tail
                row=dict(M=detail['mass'],L=str(L),K4=str(quarter_K),H=str(quarter_H),tail=str(quarter_tail),gate=str(gate),
                         L_decimal=float(L),K4_decimal=float(quarter_K),gate_decimal=float(gate))
            else:row=evaluator.evaluate(pi)
            need(F(row['gate'])>F(cert[branch+'_gate_floor']),'one assigned table passes entire cell vertex menu')
            need(0<F(row['L'])<=F(row['M'])<=1,'positive floor for the same branch source denominator')
            row.update(vertex5=vi,endpoint_codes=list(codes),live_mask=mask,branch=branch)
            rows.append(row);by_cell[mask].append(row);by_branch[branch].append(row)
    need(len(rows)==2187 and len(by_branch['quarter'])==39 and len(by_branch['retained'])==2148,'complete assigned vertex cover')
    summaries={}
    for branch,items in by_branch.items():
        worst=min(items,key=lambda row:F(row['gate']))
        need(worst['gate']==cert['expected_'+branch+'_min_gate'] and
             [worst['vertex5'],worst['endpoint_codes']]==cert['expected_'+branch+'_worst'],
             'exact minimum on assigned '+branch+'cells')
        summaries[branch]=dict(vertices=len(items),min_gate=worst['gate'],min_gate_decimal=worst['gate_decimal'],
                               worst=[worst['vertex5'],worst['endpoint_codes']],gate_floor=cert[branch+'_gate_floor'])
    for cell in cells:
        items=by_cell[cell['live_mask']]
        need(len(items)==cell['expected_vertices'] and all(row['branch']==cell['branch']for row in items),
             'one complete assigned source per structural cell')
        worst=min(items,key=lambda row:F(row['gate']))
        cell.update(min_gate=worst['gate'],min_gate_decimal=worst['gate_decimal'])
    result=dict(schema='e7-pure-source-structural-atlas-result-v1',quarter_normalization=cert['quarter_normalization'],
                retained_normalization=cert['retained_normalization'],retained_certificate_sha256=retained_hash,
                summaries=summaries,cells=cells,vertices=2187,positive_vertices=2187,rows=rows,
                root_other_mass_floor=cert['root_other_mass_floor'],all_pure_mass_floor=cert['all_pure_mass_floor'],
                external_theorem_premises=cert['external_source_cases'],
                checks=CHECKS+api.CHECKS+base.CHECKS+evaluator.api_checks,
                scope=cert['scope'],
                proof_boundary='The exact consumer verifies the822 root-other atlas and composition arithmetic. Report817/819 source-case theorems and820 blockconcavity are mathematical premises, not re-proved by this replay.')
    if args.write_result:args.result.write_text(json.dumps(result,indent=2)+'\n')
    else:need(saved==result,'exact saved atlas result replay')
    print(json.dumps({'vertices':result['vertices'],'positive_vertices':result['positive_vertices'],
                      'quarter_min_gate':summaries['quarter']['min_gate_decimal'],
                      'retained_min_gate':summaries['retained']['min_gate_decimal'],
                      'root_other_mass_floor':cert['root_other_mass_floor'],
                      'all_pure_mass_floor':cert['all_pure_mass_floor'],'checks':result['checks']},indent=2))

if __name__=='__main__':main()
