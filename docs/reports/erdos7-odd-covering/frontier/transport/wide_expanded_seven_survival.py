#!/usr/bin/env python3
"""Complete expanded-seven denominator transport on both existing wide K domains."""
import argparse
from fractions import Fraction as F
from pathlib import Path
from itertools import product
from math import lcm
from hashlib import sha256
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/wide_expanded_seven_survival.json'
PINS = {'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232', 'frontier/transport/expanded_seven_pair_comparison.py': 'a651711988f8adf20dfc27cba9665f25d0d5863cb310c26e2f4b7fc16bab1c29', 'certificates/source_norms/expanded_seven_pair_comparison.json': '6d41632d57d45a3507abb8c95fdbbd09e12de08e635d261d583889a2872271ef', 'frontier/transport/expanded_seven_survival_comparison.py': '8b7ec8a9781a8c0038795960d3e2326435de0281a76429cf552bf1325aae035a', 'certificates/source_norms/expanded_seven_survival_comparison.json': 'e3a1c9661b7c5159dd90d72e417f5c2b8bf2f107401816c1aae5c22541b2743f', 'frontier/wide_fresh_full_slot_source_comparison.py': '8b92c7eda87c06ca763d50015b5dd6078730cdb3c7af81aa8a46c989ba3f425d', 'certificates/source_norms/wide_fresh_full_slot_source_comparison.json': '7e8ba6cbd1fa404bf9274cd32e102fa40bf9b7bc7c4ad4c46c2b42b71a61a71a', 'frontier/transport/extended_source_bridge_comparison.py': '4b9e21988e129c3aff849afefe563e92154cca7075e40eff5d20ae33418a403d', 'certificates/source_norms/extended_source_bridge_comparison.json': 'd38c7de4dc87e8467f4ee6e3a4ae3a71affccf652d88aa169e093b888e675451', 'profile-notes/181-a-fresh-complete-comparison-covers-source-radius-one-twentieth.md': '790572babc336ea8abd5f8e3b960df2cd87260337c646fcc9657a0bf3e404b01', 'profile-notes/transport/195-the-complete-source-comparison-extends-beyond-the-old-radius-domain.md': '4ce83eb8dce7127273b13d431f23d608eed3e152218a6eaf57406c60e339b991', 'profile-notes/transport/201-two-more-seven-labels-and-selected-intersections-control-both-heavy-costs.md': '2e78cd791bbbfbbe3ffbcb2be6845e02fdbbe2bbd17e06b9e7151e3ddd23cb5d'}

def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable source provider')
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def flatten(rows):
    return tuple(x for row in rows for x in row)


class RationalHead:
    def __init__(self,base,doc,row):
        self.bridge=module("wide_seven_bridge",base/"frontier/k_face_common_seven_hinges.py")
        self.mean=module("wide_seven_mean",base/"frontier/joint_deep_mean_transport.py")
        self.seven=module("wide_seven_face",base/"frontier/transport/expanded_seven_pair_comparison.py").CoupledSevenHead(base)
        pre,raw,wstar,eta=self.bridge.source_tables(2)
        self.fraw,self.fw=flatten(raw),flatten(wstar)
        self.doc=doc;self.row=row;self.a={int(t):F(v) for t,v in row['coefficients'].items()};self.A=sum(self.a.values());self.d=F(doc['parameters']['delta']);self.rho=F(doc['parameters']['rho']);self.g=F(doc['parameters']['gap']);self.par=doc['parameters'];self.kb=F(self.par['kbar']);self.a1=self.a.get(1,F(0));self.nsel=max(min(t-1,4) for t in self.a)
        self.caps=list(map(F,doc['complete_heads']['uniform_caps']));self.budgets=list(map(F,doc['complete_heads']['uniform_budgets']));self.v0=F(self.par['v0']);self.v1=F(self.par['v1']);self.candidates={}
        self.tailconst=F(row['selected_support']['tail']['constant']);self.slopes=tuple(map(F,row['selected_support']['tail']['slopes']));self.sourcecredit=F(row['selected_support']['mean_source_error']);self.faceconst=self.seven.prepare(self.a)['old_constant']*self.seven.prepare(self.a)['factor']/self.seven.total
        self.qs=[tuple(map(F,v['q'])) for v in row['exhaustive_vertices']]
        self.tables={}
        for q in [None]+self.qs:
            weights=self.fw if q is None else tuple(self.fw[i]+(self.d/5 if i//5 else 0)+(q[0] if i%5==4 else 0)+(q[1] if i//5>=2 and i%5==4 else 0) for i in range(25))
            ps=pre if q is None else [[pre[c][j]+((self.v0 if c<2 else self.v1) if j==3 else 0) for j in range(5)] for c in range(5)]
            es=eta if q is None else [[eta[c][j]+(self.d/18 if c==0 and eta[c][j]>0 else 0) for j in range(5)] for c in range(5)]
            H={};D={}
            for node,m,v in product(range(25),range(5),range(1,7)):
                f=lambda t,z:weights[node]*max(z-t,0)+self.bridge.seven_increment(t,z,m)
                H[node,m,v]=sum(a*f(t,v) for t,a in self.a.items())
                for step in range(1,self.nsel+1):
                    for k in range(step):D[step,k,node,m,v]=sum(a*(f(t,v+k+1)-f(t,v+k)) for t,a in self.a.items() if min(t-1,4)>=step)
            self.tables[q]=(H,D,ps,es)
    def finite(self,layout,projection,q,selected_choice=None):
        H,D,ps,es=self.tables[q];load=self.bridge.head_load(layout);r,f,c63,r105,f105=projection
        extras=tuple(int(self.bridge.ROOT[c]==r)+int(s==f)+(int(c==c63)+int(self.bridge.ROOT[c]==r105 and s==f105) if c63 is not None else 0) for c,s in product(range(5),repeat=2))
        arr=tuple(H[i,m,v] for i,(m,v) in enumerate(zip(extras,load)));caps=self.fraw if q is None else self.caps;budgets=self.bridge.GROUP_MASSES if q is None else self.budgets
        total=self.bridge.lp_bound(arr,caps,budgets)[0];choices=[]
        def P(z,step):
            if step in (2,4):return max(sum(ps[c][s]*z[5*c+s] for s in range(5)) for c in range(5))/([0,0,27,0,81][step])
            if step==1:return max(sum(es[c][s]*z[5*c+s] for c in range(5)) for s in range(5))/25
            return max(sum(es[c][s]*z[5*c+s] for c in range(5) if self.bridge.ROOT[c]==r) for r,s in product(range(2),range(5)))/25
        for step in range(1,self.nsel+1):
            ds=[tuple(D[step,k,i,m,v] for i,(m,v) in enumerate(zip(extras,load))) for k in range(step)];hi=ds[-1];opts=[P(hi,step)]
            if step in (2,3):lo=ds[-2];opts.append(P(lo,step)+max(h-l for h,l in zip(hi,lo))/675)
            if step==4:
                lo,mid=ds[1:3];opts.extend([P(lo,step)+max(max(2*(m-l),h-l) for l,m,h in zip(lo,mid,hi))/2025,P(mid,step)+max(h-m for h,m in zip(hi,mid))/2025])
            j=min(range(len(opts)),key=lambda j:opts[j]) if selected_choice is None else selected_choice[step-1]
            total+=opts[j];choices.append(j)
        return total,tuple(choices)

class IntegerHead(RationalHead):
    def __init__(self,base,doc,row):
        super().__init__(base,doc,row)
        self.C=lcm(*(v.denominator for H,D,_,_ in self.tables.values() for table in (H,D) for v in table.values()))
        coeff=[F(1,675),F(1,2025)]+self.caps+self.budgets+list(self.fraw)+list(self.bridge.GROUP_MASSES)
        for _,_,ps,es in self.tables.values():
            coeff += [x/27 for row in ps for x in row]+[x/81 for row in ps for x in row]+[x/25 for row in es for x in row]
        self.M=lcm(*(F(x).denominator for x in coeff));self.icaps=[self.bridge.integer(x*self.M) for x in self.caps];self.ibudgets=[self.bridge.integer(x*self.M) for x in self.budgets]
        Mload=sum(a*max(6+min(t-1,4)-t,0) for t,a in self.a.items());P3,P5,P1,Pc=self.slopes
        basic=[self.tailconst,self.sourcecredit,self.a1/F(54000),self.rho*F(8,27)*self.a1,self.rho*self.a1,self.rho*self.a1*(F(self.par['Cbar'])-1),self.rho*self.a1*F(self.par['tbar']),self.rho*self.a1*self.kb,self.A*(F(9,350)+self.d/210)]
        basic += [self.rho*x for x in (P3,self.kb*P3,P5,P1,Pc,Mload)]+[self.g*P3*(q[0]+self.kb*q[1]) for q in self.qs]
        self.S=lcm(self.C*self.M,*(x.denominator for x in basic));self.fac=self.S//(self.C*self.M)
        self.it={}
        for q,(H,D,ps,es) in self.tables.items():
            ops={1:[[(5*c+s,self.bridge.integer(es[c][s]*self.M/25)) for c in range(5)] for s in range(5)],2:[[(5*c+s,self.bridge.integer(ps[c][s]*self.M/27)) for s in range(5)] for c in range(5)],3:[[(5*c+s,self.bridge.integer(es[c][s]*self.M/25)) for c in range(5) if self.bridge.ROOT[c]==r] for r,s in product(range(2),range(5))],4:[[(5*c+s,self.bridge.integer(ps[c][s]*self.M/81)) for s in range(5)] for c in range(5)]}
            self.it[q]=({k:self.bridge.integer(v*self.C) for k,v in H.items()},{k:self.bridge.integer(v*self.C) for k,v in D.items()},ops)
        self.oldextras=[(r,f,tuple(int(self.bridge.ROOT[c]==r)+int(s==f) for c,s in product(range(5),repeat=2))) for r,f in product(range(2),range(5))]
        self.added=[(c63,r105,f105,tuple(int(c==c63)+int(self.bridge.ROOT[c]==r105 and s==f105) for c,s in product(range(5),repeat=2))) for c63,r105,f105 in product(range(5),range(2),range(5))]
        self.lp_count=0
    def choices(self,B,ex):
        _,D,ops=self.it[None];return self.selected(B,ex,D,ops,None)[1]
    def selected(self,B,ex,D,ops,choices):
        total=0;chosen=[]
        for step in range(1,self.nsel+1):
            def arr(k):return [D[step,k,i,m,v] for i,(m,v) in enumerate(zip(ex,B))]
            def P(z):return max(sum(weight*z[i] for i,weight in row) for row in ops[step])
            hi=arr(step-1);values=[P(hi)]
            if step in (2,3):
                lo=arr(step-2);values.append(P(lo)+(self.M//675)*max(h-l for h,l in zip(hi,lo)))
            if step==4:
                lo,mid=arr(1),arr(2);values.extend([P(lo)+(self.M//2025)*max(max(2*(m-l),h-l) for l,m,h in zip(lo,mid,hi)),P(mid)+(self.M//2025)*max(h-m for h,m in zip(hi,mid))])
            c=min(range(len(values)),key=lambda c:values[c]) if choices is None else choices[step-1]
            total+=values[c];chosen.append(c)
        return total,tuple(chosen)
    def shifts(self,layout,new):
        a=self.a1;d=self.mean.mean_data(F(0),F(3,4),F(1,2),F(3,4),self.bridge.ETA,(F(0),F(1,5),F(1,5),F(3,20),F(1,5)),layout);I,J=int(layout[0]==0),int(layout[3]==0)
        L27=d['joint_supremum']+max(d['wrong_cell_missing_supremum']*(F(self.par['Cbar'])-1),d['full_root1_missing_supremum']*F(self.par['tbar']));Lge4=d['Mxi']+I*(1+J)*F(self.par['tbar']);Mload=sum(v*max(6+min(t-1,4)-t,0) for t,v in self.a.items());P3,P5,P1,Pc=self.slopes
        prices=(P3+8*a/27,self.kb*P3,P5+a*L27,P5+a*Lge4,P3+a*d['E5deep_price'],self.kb*(P3+a*d['E15deep_price']/2),Mload+P3+P5+P1+Pc)
        constant=self.tailconst-a*d['reference']+self.sourcecredit-(self.A*(F(9,350)+self.d/210) if new else 0)
        values=[constant+self.g*P3*(q[0]+self.kb*q[1])+(self.rho-self.g*sum(q))*max(prices) for q in self.qs]
        require(all((v*self.S).denominator==1 for v in values),'Exact integer source/mean/tail shift')
        return [int(v*self.S) for v in values]
    def uniform(self,B,ex,shifts,ceiling=None):
        choice=self.choices(B,ex);best=None
        for q,shift in zip(self.qs,shifts):
            H,D,ops=self.it[q];z=[H[i,m,v] for i,(m,v) in enumerate(zip(ex,B))];head=self.bridge.lp_bound(z,self.icaps,self.ibudgets)[0];self.lp_count+=1
            total=self.fac*(head+self.selected(B,ex,D,ops,choice)[0])+shift
            best=total if best is None else max(best,total)
            if ceiling is not None and best>=ceiling:return ceiling
        return best
    def scan(self):
        best=None;witness=None;expanded=pruned=branches=checked=0;max_pruned=-1;digest=sha256()
        seed=(0,1,2,0,2,1,2)
        def consider(lay,B,ex,old,shift,old_projection):
            nonlocal best,witness,checked
            for c,r,f,add in self.added:
                nex=[a+b for a,b in zip(ex,add)];value=min(old,self.uniform(B,nex,shift,old))
                checked+=1;digest.update((str(value)+';').encode())
                if best is None or value>best:best=value;witness={"layout":lay,"seven21_root":old_projection[0],"seven35_slot":old_projection[1],"seven63_cell":c,"seven105_root":r,"seven105_slot":f}
        B=self.bridge.head_load(seed);so,sn=self.shifts(seed,False),self.shifts(seed,True)
        for r,f,ex in self.oldextras:consider(seed,B,ex,self.uniform(B,ex,so),sn,(r,f))
        for lay in product(range(2),range(5),range(5),range(2),range(5),range(5),range(5)):
            B=self.bridge.head_load(lay);so,sn=self.shifts(lay,False),self.shifts(lay,True)
            for r,f,ex in self.oldextras:
                old=self.uniform(B,ex,so);branches+=1
                if old<=best:pruned+=1;max_pruned=max(max_pruned,old);digest.update((str(old)+';').encode())
                else:expanded+=1;consider(lay,B,ex,old,sn,(r,f))
        require(branches==125000 and pruned+expanded==branches and checked==500+50*expanded
                and max_pruned<=best,'All old branches and every added projection covered')
        lay=tuple(witness['layout']);B=self.bridge.head_load(lay)
        r,f,c,rr,ff=(witness[k] for k in ('seven21_root','seven35_slot','seven63_cell','seven105_root','seven105_slot'))
        ex=tuple(int(self.bridge.ROOT[c0]==r)+int(s==f) for c0,s in product(range(5),repeat=2))
        nex=tuple(v+int(c0==c)+int(self.bridge.ROOT[c0]==rr and s==ff) for v,(c0,s) in zip(ex,product(range(5),repeat=2)))
        old_value=self.uniform(B,ex,self.shifts(lay,False));new_value=self.uniform(B,nex,self.shifts(lay,True))
        require(min(old_value,new_value)==best, 'Independent complete maximizing branch reevaluation')
        witness.update(old_complete_upper=F(old_value,self.S),new_complete_upper=F(new_value,self.S))
        return {'upper':F(best,self.S),'branches':branches,'expanded':expanded,'pruned':pruned,
                'expanded_choices_including_seed':checked,
                'maximum_unexpanded_upper':F(max_pruned,self.S) if pruned else None,
                'LPs':self.lp_count,'witness':witness,'digest':digest.hexdigest()}


def check_tail(row, par):
    a={int(t):F(v) for t,v in row['coefficients'].items()}
    delta=F(par['delta']);tail=row['selected_support']['tail'];constant=F(0)
    for t, amount in a.items():
        details=tail['supports'][str(t)]
        for j, name in enumerate(('pure3','pure5','root5','cell5')):
            constant+=amount*(F(par['c'][j])*F(details[name]['remaining_geometric'])
                              +F(par['H'][j])*F(details[name]['intercept_coefficient']))
        constant+=amount*(F(1,72)+F(779,12600)+3*delta/280)
    constant+=F(tail['slopes'][1])*delta/240
    require(constant==F(tail['constant']) and row['factorial_tail_coefficient']=='0'
            and F(row['selected_support']['mean_source_error'])==a.get(1,F(0))*299*delta/10800,
            'The exact original complete punctured tail and same-head mean source price')
    # These are the assigned raw63 and raw105 terms of the complete cap series.
    coefficients=(F(1,35),F(1,35),F(1,90),F(11,700),F(11,700),F(1,20),F(1,360))
    face=(F(5,36),F(1,12),F(3,4),F(1,2),F(1,3),F(1,9),F(1))
    prices=(F(1,420),F(1,168),F(1,1260),F(4,3150),F(0),F(0))
    source_prices=((F(1,12),F(1,12),F(1,36),F(1,72),F(0),F(0)),
                   (F(0),F(1,36),F(0),F(0),F(0),F(0)),
                   (F(0),F(1,4),F(0),F(0),F(0),F(0)),
                   (F(0),F(0),F(0),F(1,18),F(0),F(0)))+((F(0),)*6,)*3
    require(sum(x*y for x,y in zip(coefficients,face))==F(13,360)
            and tuple(sum(c*p[i] for c,p in zip(coefficients,source_prices)) for i in range(6))==prices
            and F(1,5)-F(6,35)==coefficients[1]
            and F(1,20)-F(6,175)==coefficients[4]
            and max(prices)==F(1,168) and F(1,420)<=(1-delta)/168
            and F(779,12600)+3*delta/280-(F(13,360)+delta/168)==F(9,350)+delta/210,
            'Complete positive-coefficient tail reconstruction and full-domain exposed price')
    return {'raw_coefficients':coefficients,'six_loss_prices':prices,
            'face_constant':F(13,360),'source_error':delta/168,
            'old_to_new_tail_decrease':F(9,350)+delta/210}


def check_compiler(engine):
    count=0
    for layout in ((0,1,2,0,2,1,2),(1,3,2,1,2,3,2)):
        B=engine.bridge.head_load(layout)
        for projection in ((0,2,None,None,None),(1,2,3,1,2)):
            r,f,c,rr,ff=projection
            ex=tuple(int(engine.bridge.ROOT[c0]==r)+int(s==f)
                     +(int(c0==c)+int(engine.bridge.ROOT[c0]==rr and s==ff) if c is not None else 0)
                     for c0,s in product(range(5),repeat=2))
            choice=engine.finite(layout,projection,None)[1]
            require(choice==engine.choices(B,ex),'The exact same face-selected inequality throughout the domain')
            for q in engine.qs:
                H,D,ops=engine.it[q]
                head=engine.bridge.lp_bound([H[i,m,v] for i,(m,v) in enumerate(zip(ex,B))],
                                           engine.icaps,engine.ibudgets)[0]
                value=F(head+engine.selected(B,ex,D,ops,choice)[0],engine.C*engine.M)
                require(value==engine.finite(layout,projection,q,choice)[0],
                        'Independent rational and compiled LP/cylinder/selected-intersection values')
                count+=1
    return count


def original_numerator(study, domain):
    par=domain['parameters'];heads=domain['complete_heads'];old=domain['comparison']
    A=F(53,360);rho=F(par['rho']);delta=F(par['delta'])
    H1=F(domain['complete_H1']['upper']);H2=F(heads['H2']['selected_support']['upper'])
    cS,cQ,C0=(F(study.old[k]) for k in ('signed_mass_coefficient','complete_square_weight','offset'))
    heavy=[]
    for row in domain['heavy_extension']['heavy_bounds']:
        i=row['index'];w=F(row['weight']);barrier=F(row['barrier'])
        require(w==study.weights[i] and barrier==F(study.engine.thresholds[i]['constant']),
                'Both original heavy tests and weights retained')
        heavy.append({'index':i,'weight':w,'barrier':barrier,
                      'endpoint_upper':barrier*A-F(row['margin_lower'])+F(row['one_residual_price'])*rho})
    simple=[{'index':row['index'],'weight':F(row['weight']),
             'endpoint_upper':F(row['at_one'])*A+F(row['first_difference'])*H1
                 +F(row['second_curvature'])*H2}
            for row in study.simple_prior['radii'][0]['cost_results']]
    require(all(row['weight']==study.weights[row['index']] for row in simple),
            'All28 original simple costs retain their independent labels and weights')
    raw46=study.square.retained_raw81(study.source,study.quadratic,study.old,study.read('k_face_complete_ratio'),delta)
    raw47=study.quadratic.retained_raw81_controller(study.source,study.old,delta)
    groups={'mean11':F(heads['mean_shared']['upper']),
            'single28_at_mass_floor':sum(row['weight']*row['endpoint_upper'] for row in simple),
            'quadratic9':F(heads['quadratic_shared']['upper']),
            'raw81_first':raw46['outside_weight']*raw46['uniform_upper'],
            'raw81_second':raw47['weight']*raw47['uniform_upper'],
            'heavy2_fixed_support':sum(row['weight']*row['endpoint_upper'] for row in heavy),
            'square_at_mass_floor':cQ*(A+F(domain['complete_square']['full_square_upper'])
                                      -F(domain['complete_square']['mass_upper']))}
    indices=[row['index'] for row in heads['mean_costs']+heads['quadratic_costs']+simple]+[0,16,46,47]
    require(sorted(indices)==list(range(52)) and old['all_original_indices']==list(range(52))
            and all(F(row['weight'])==study.weights[row['index']]
                    for row in heads['mean_costs']+heads['quadratic_costs'])
            and encode(groups)==old['cost_groups'] and encode(heavy)==old['heavy_costs']
            and encode(simple)==old['simple_costs'], 'Every original52-cost group reconstructed exactly')
    N=cS*A+sum(groups.values());M=cS+sum(row['weight']*row['barrier'] for row in heavy)+study.weights[40]+cQ
    require(N==F(old['signed_endpoint'])>0 and M==F(old['mass_coefficient']) and C0==F(old['offset']),
            'Original signed mass, complete square and actual-S coefficient')
    return {'signed_mass_coefficient':cS,'complete_square_weight':cQ,'offset':C0,
            'cost_groups':groups,'all_original_indices':sorted(indices),'heavy_costs':heavy,
            'simple_costs':simple,'signed_endpoint':N,'mass_coefficient':M}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest()==PINS['certificate_io.py'],
            'Pinned logical certificate reader')
    io=module('wide_seven_io',base/'certificate_io.py')
    read=lambda name:json.loads(io.read_artifact_bytes(base/'certificates/source_norms'/(name+'.json')))
    names=('wide_fresh_full_slot_source_comparison','extended_source_bridge_comparison')
    domains=[read(name) for name in names];face=read('expanded_seven_survival_comparison')
    pins=dict(PINS)
    for data in domains+[face]:
        for path,pin in data['source_sha256'].items():
            require(path not in pins or pins[path]==pin,'Consistent common source '+path)
            pins[path]=pin
    for path,pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest()==pin,'Pinned logical source '+path)
    study=module('wide_seven_study',base/'frontier/k_neighborhood_radius_study.py').Study(base)
    require(all(pins.get(path)==pin for path,pin in study.pins.items()),'Complete original source closure')
    output=[]
    for name,doc,provider in zip(names,domains,(study.get('wide_fresh_full_slot_source_comparison'), study.get('transport/extended_source_bridge_comparison')),strict=True):
        par,guards=provider.parameters_and_guards(study)
        par['positive7']=F(779,12600)+3*par['delta']/280
        require(encode(par)==doc['parameters'] and encode(guards)==doc['guards']
                and par['rbar']==5*par['rho'] and par['gap']>0,
                'Every original whole-domain packing, ratio, cap, residual and tail guard rechecked')
        costs=doc['complete_heads']['denominator_costs'];records=[];rational_count=0
        require(len(costs)==5,'All four AP11 blocks and the independent AP13 test')
        for i,row in enumerate(costs):
            expected=face['AP11_block_results'][i]['hinge_coefficients'] if i<4 else {'4':'1'}
            require(row['coefficients']==expected and F(row['weight'])==(F(1,7) if i<4 else F(1,6)),
                    'The same original complete count law and separate AP13 coefficient')
            tail=check_tail(row,par)
            engine=IntegerHead(base,doc,row)
            require(engine.qs==[(F(0),F(0)),(F(0),par['rho']/par['gap']),
                                (par['rho']/par['gap'],F(0))], 'The full common actual defect polygon')
            expected_caps=[]
            for node,cap in enumerate(engine.fraw):
                c,s=divmod(node,5);excluded=s==0 or(s==1 and c>=2) or(s==2 and c==2)
                du=F(0) if excluded else par['delta']/90 if c==0 else F(0)
                if not excluded and s==3:du+=par['v0']/18 if c==0 else par['v0']/9 if c==1 else par['v1']/9
                expected_caps.append(cap+du)
            require(expected_caps==engine.caps and tuple(engine.budgets)
                    ==tuple(a+b for a,b in zip(engine.bridge.GROUP_MASSES,par['budget_increments'])),
                    'Exact actual-source cap and group enlargement, including all mixed products')
            rational_count+=check_compiler(engine)
            scan=engine.scan();previous=F(row['selected_support']['upper'])
            bound=min(scan['upper'],previous)
            records.append({'name':row['name'],'weight':F(row['weight']),
                'hinge_coefficients':expected,'previous_upper':previous,'uniform_upper':bound,
                'selected_complete_tail_support':row['selected_support']['tail'],
                'new_positive7_tail':tail,'scan':scan})
            print(name+' '+row['name']+': '+str(float(bound))+'; '+str(scan['LPs'])+' exact LPs.',flush=True)
        numerator=original_numerator(study,doc)
        loss=sum(row['weight']*row['uniform_upper'] for row in records)
        oldloss=F(doc['complete_heads']['denominator_shared']['upper'])
        # The original shared-q bound remains another valid complete option.
        adopted_loss=min(loss,oldloss);A=F(53,360);cE=1-F(1,614922)
        H1=F(doc['complete_H1']['upper']);d=cE*A-adopted_loss-H1/55902
        oldd=cE*A-oldloss-H1/55902;C0=numerator['offset'];N=numerator['signed_endpoint'];M=numerator['mass_coefficient']
        K=C0+N/d;remaining=(K-C0)*cE-M
        require(oldd==F(doc['comparison']['denominator_at_mass_floor']) and d>oldd>0
                and C0+N/oldd==F(doc['comparison']['comparison_upper']) and remaining>0
                and 403<K<F(doc['comparison']['comparison_upper']),
                'Strict complete domain improvement for every actual S>=53/360, still above403')
        output.append({'source':name,'parameters':par,'guards':guards,
            'denominator_costs':records,'independent_rational_comparisons':rational_count,
            'rational_lp_count':sum(row['scan']['LPs'] for row in records),
            'full_count_tail':face['full_count_tail'],'complete_H1_upper':H1,
            'actual_survivor_mass_coefficient':cE,'actual_survivor_mass_floor':A,
            'separate_survival_loss_upper':loss,'previous_shared_survival_loss_upper':oldloss,
            'adopted_survival_loss_upper':adopted_loss,'denominator_gain':d-oldd,
            'comparison':{**numerator,'denominator_at_mass_floor':d,
                'remaining_S_coefficient':remaining,'raw_s_coefficient':F(0),
                'comparison_upper':K,'previous_comparison':F(doc['comparison']['comparison_upper'])}})
    return encode({'schema':'erdos7-wide-expanded-seven-survival-v1','source_sha256':pins,'domains':output,
        'scope':'Ordinary complete actual-source comparison on both whole181 and195 rectangles and both K orientations. Each selected inequality is chosen on the face then held fixed; each complete bridge is maximized over every q/defect vertex before the two whole-domain uppers are minimized. Every original head and all independent21/35/63/105 projections remain. All52 original costs, signed actual mass, complete count and exponent tails remain. No global complementary-region conclusion, actual-family attainment, Lean verification or unrestricted Erdos7 resolution.'})


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    modes=parser.add_mutually_exclusive_group()
    modes.add_argument('--write',action='store_true');modes.add_argument('--check',action='store_true')
    args=parser.parse_args();result=calculate(args.base)
    io=module('wide_seven_writer',args.base/'certificate_io.py')
    if args.write:io.write_certificate_text(args.base/CERTIFICATE,json.dumps(result,indent=2)+'\n')
    elif args.check:require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE))==result,
                           'Exact complete expanded-seven wide-domain certificate')
    print('PASS: both complete wide source domains, all52 costs and full survival denominators.')


if __name__=='__main__':
    try:main()
    except (ValueError,ArithmeticError,OSError,KeyError,TypeError,json.JSONDecodeError) as error:
        print('FAIL: '+str(error),file=sys.stderr);raise SystemExit(1)
