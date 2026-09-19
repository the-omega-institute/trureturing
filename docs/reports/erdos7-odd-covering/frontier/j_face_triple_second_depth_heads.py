#!/usr/bin/env python3
"""Complete J heads with seven135/125/225 states and independent147/245 projections."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import product, combinations
from math import lcm
from types import SimpleNamespace
import importlib.util
import json
from pathlib import Path
import sys
from time import perf_counter
sys.dont_write_bytecode=True
CERTIFICATE='certificates/source_norms/j_face_triple_second_depth_heads.json'
Z6=F(37,1225)
PINS={'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232', 'frontier/j_face_second_depth_retained_heads.py': '02cca63e4ea4dd3771d6212351186e92e3743df171ad78ea613219b688733957', 'certificates/source_norms/j_face_second_depth_retained_heads.json': 'e9bc7201404e9c70bce6b1614b9ebe9db53e03429bfd6d0f7468679017b86c3d', 'frontier/j_face_retained135125_heads.py': 'db804300e915d153152d1a0b078233e3ac026f82ec296fb2deea480813aebdd5', 'certificates/source_norms/j_face_retained135125_heads.json': 'b9a65e86cf068edc78cd66998683e19df409d437c82de36dbb22658c781f3ae8', 'profile-notes/251-two-retained-original-tests-sharpen-the-complete-j-heads.md': '92d00b93193b8a06da4c30921c91cf77b8bfe6d1c38f3ee846a37d73142d7d88', 'frontier/second_depth_seven_comparison.py': '5544b70201a721be7ca0dfa92155c4b186235a19f52a5fd85346f85c02cfc950'}
N,U,V,L135,L125,L225=6531,876,3676,6476,6501,6506
LABELS=(135,125,225)
CAPS=(F(1,135),F(13,3750),F(1,225))


def require(ok,message):
    if not ok: raise ValueError(message)


def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    require(spec is not None and spec.loader is not None,'Loadable original source')
    value=importlib.util.module_from_spec(spec);spec.loader.exec_module(value);return value


def encode(value):
    if isinstance(value,F):return str(value)
    if isinstance(value,dict):return {str(k):encode(v) for k,v in value.items()}
    if isinstance(value,(list,tuple)):return [encode(v) for v in value]
    return value


def max_min_affines(lines):
    """Every endpoint and pair intersection of the finite affine lower envelope."""
    candidates={F(0),F(1)}
    for a,b in combinations(lines,2):
        denominator=a[0]-b[0]-a[1]+b[1]
        if denominator:
            x=F(a[0]-b[0],denominator)
            if 0<x<1:candidates.add(x)
    values={x:min(a+(b-a)*x for a,b in lines) for x in candidates}
    at=max(sorted(candidates),key=lambda x:values[x])
    return values[at],at,len(candidates)-2


def make_lp(j,old,exact):
 require(old.nvars==876 and len(old.rows)==587 and len(old.equalities)==16,
         'The entire original244 model precedes every triple-state constraint')
 lp=SimpleNamespace(nvars=N,rows=[dict(r)for r in old.rows],rhs=list(old.rhs),equalities=[dict(r)for r in old.equalities],erhs=list(old.erhs))
 pre,absolute,desc,w=j.source_tables(j.LO);flatw=[x for row in w for x in row]
 require(max(v for row in desc for v in row)/25==CAPS[2]
         and j.REMAINDERS[4]-sum(CAPS)==F(6151,405000),
         'J-specific225 raw profile cap and complete nonnegative old remainder')
 def add(row,rhs=F(0)):lp.rows.append(row);lp.rhs.append(rhs)
 def cols(block,states,ks):return {block+400*(st-1)+k:F(1)for st in states for k in ks}
 states=[tuple(st for st in range(1,8)if st>>bit&1)for bit in range(3)]
 for start,stop in((L135,L125),(L125,L225),(L225,N)):
  lp.equalities.append({k:F(1)for k in range(start,stop)});lp.erhs.append(F(1))
 for i in range(25):
  c,s=divmod(i,5);ks=range(16*i,16*i+16)
  for bit,lam,cap in((0,L135+i,pre[c][s]/27),(1,L125+s,desc[c][s]/125),(2,L225+i,desc[c][s]/25)):
   add({lam:-cap,**cols(U,states[bit],ks)})
  for m in range(16):
   k=16*i+m;add({k:F(-1),**cols(U,range(1,8),(k,))});add({425+k:F(-1),**cols(V,range(1,8),(k,))})
   complement={425+k:F(1),k:-flatw[i]}
   for st in range(1,8):
    uk,vk=U+400*(st-1)+k,V+400*(st-1)+k
    add({vk:F(1),uk:-flatw[i]});complement[vk]=F(-1);complement[uk]=flatw[i]
   add(complement)
 for bit,cap in enumerate(CAPS):add(cols(V,states[bit],range(400)),cap)
 for bit,label in enumerate(LABELS):
  for oldbit,oldlabel in enumerate((25,27,75,81)):
   add(cols(U,states[bit],[16*i+m for i,m in product(range(25),range(16))if m>>oldbit&1]),F(1,lcm(label,oldlabel)))
 for b1,b2 in combinations(range(3),2):
  both=tuple(st for st in range(1,8)if st>>b1&1 and st>>b2&1)
  add(cols(U,both,range(400)),F(1,lcm(LABELS[b1],LABELS[b2])))
 lp.unit_rows=[]
 for k in range(N):lp.unit_rows.append(len(lp.rows));add({k:F(1)},F(1))
 lp.columns=[[]for _ in range(N)];lp.eqcolumns=[[]for _ in range(N)]
 for i,row in enumerate(lp.rows):
  for k,a in row.items():lp.columns[k].append((i,a))
 for i,row in enumerate(lp.equalities):
  for k,a in row.items():lp.eqcolumns[k].append((i,a))
 lp.checker=exact.IntegerDualChecker(lp)
 require(len(lp.rows)==11211 and len(lp.equalities)==19,'All6531 variables and11211/19 source constraints')
 return lp

def specification(lp,base_spec,j):
    return encode({'variables':N,'base244_model':base_spec,
        'marked_state_bit_labels':LABELS,'marked_states':list(range(1,8)),'implicit_complement':0,
        'marked_raw_variables':2800,'marked_survivor_variables':2800,
        'projection_variables':{'135':25,'125':5,'225':25},'survivor_caps':dict(zip(LABELS,CAPS)),
        'raw_intersection_caps':{label:{old:F(1,lcm(label,old))for old in(25,27,75,81)}for label in LABELS},
        'joint_raw_caps':{str(a)+'/'+str(b):F(1,lcm(a,b))for a,b in combinations(LABELS,2)},
        'complete_retained_tail':j.REMAINDERS[4]-sum(CAPS),'unit_repair_rows':N,
        'inequalities':len(lp.rows),'equalities':len(lp.equalities),
        'rows_sha256':sha256(json.dumps(encode([lp.rows,lp.rhs,lp.equalities,lp.erhs]),sort_keys=True,separators=(',',':')).encode()).hexdigest()})


class TripleSecondDepthJHead:
    def __init__(self,base,j,core,pair,depth,prior244,prior251,prior256,bank=None,proposer=None):
        self.j,self.core,self.pair,self.depth=j,core,pair,depth
        self.codec=module('j_triple_depth_codec',base/'frontier/retained135_heavy_comparison.py')
        oldbank=self.codec.decode_dual_bank(prior251['encoded_rational_duals'],inequality_count=6354,equality_count=18)
        self.previous=pair.RetainedJPairHead(base,j,core,prior244,bank=oldbank)
        self.head=self.previous.head
        require(self.previous.specification==prior251['model'],'Unchanged entire251 actual-source model')
        self.lp=make_lp(j,self.previous.previous.lp,self.codec)
        self.specification=specification(self.lp,self.previous.previous.specification,j)
        previous_depth=module('j_triple_previous_depth',base/'frontier/j_face_second_depth_retained_heads.py')
        depth_bank=self.codec.decode_dual_bank(prior256['encoded_rational_duals'],inequality_count=6354,equality_count=18)
        self.previous_depth=previous_depth.SecondDepthJHead(base,j,core,pair,depth,prior244,prior251,bank=depth_bank)
        require(self.previous_depth.specification==prior256['model'],'Unchanged256 source model for prior full-objective certificates')
        self.bank={} if bank is None else bank;self.proposer=proposer
        self.used,self.verified,self.prior_used,self.prior_depth_used=set(),{},set(),set()
        self.raw={}
        for t,w,m,e in product(range(1,9),sorted(set(self.head.w)),range(5),range(3)):
            values=[F(w,5)*max(v-t,0)+depth.seven_increment(t,v,m,e) for v in range(1,14)]
            increments=[b-a for a,b in zip(values,values[1:])]
            require(min(increments)>=0 and all(a<=b for a,b in zip(increments,increments[1:]))
                    and all(a==F(w,5) for a in increments[t-1:]),'All J two-depth transitions and exact affine continuation')
            if e==0:require(all(depth.seven_increment(t,v,m,e)==self.head.bridge.seven_increment(t,v,m)
                                  for v in range(1,14)),'Zero new projections recover the full one-depth bridge')
            self.raw[t,w,(m,e)]=[0]+[j.integer(j.SCALE*v) for v in values]

    def prepare_six(self,old):
        j=self.j;ints=old['primitive_coefficients'];highest=old['highest_selected_label']
        pairs=list(product(range(5),range(3)));weights=sorted(set(self.head.w))
        head={(w,p):[0]+[sum(a*self.raw[t,w,p][v] for t,a in ints.items()) for v in range(1,7)] for w,p in product(weights,pairs)}
        increments={(i,k):{(w,p):[0]+[sum(a*(self.raw[t,w,p][v+k+1]-self.raw[t,w,p][v+k])
                     for t,a in ints.items() if min(t-1,4)>=i) for v in range(1,7)]
                     for w,p in product(weights,pairs)} for i in range(1,highest+1) for k in range(i)}
        for i,w,p,v in product(range(1,highest+1),weights,pairs,range(1,7)):
            row=[increments[i,k][w,p][v] for k in range(i)]
            require(min(row)>=0 and all(a<=b for a,b in zip(row,row[1:])),'Ordered selected increments of the complete six-projection bridge')
        constant=j.integer(j.TOTAL*sum(a*(j.REMAINDERS[min(t-1,4)]+Z6) for t,a in ints.items()))
        return {**old,'head':head,'increments':increments,'constants':(constant,constant)}

    def rational_six(self,co,layout,projection,theta):
        j,head=self.j,self.head;B=head.bridge.head_load(layout)
        r,s,c63,r105,s105,r147,s245=projection
        first=[int(j.ROOT[c]==r)+int(k==s)+int(c==c63)+int(j.ROOT[c]==r105 and k==s105) for c,k in product(range(5),repeat=2)]
        second=[int(j.ROOT[c]==r147)+int(k==s245) for c,k in product(range(5),repeat=2)]
        p,caps,e,w=j.source_tables(theta);weights=[x for row in w for x in row]
        fn=lambda t,i,v:weights[i]*max(v-t,0)+self.depth.seven_increment(t,v,first[i],second[i])
        z=[sum(a*fn(t,i,B[i]) for t,a in co.items()) for i in range(25)]
        value=j.raw_source_lp(z,theta)
        def operator(arr,step):
            if step in (2,4):return max(sum(p[c][s]*arr[5*c+s] for s in range(5)) for c in range(5))/(27 if step==2 else 81)
            if step==1:return max(sum(e[c][s]*arr[5*c+s] for c in range(5)) for s in range(5))/25
            return max(sum(e[c][s]*arr[5*c+s] for c in range(5) if j.ROOT[c]==r) for r,s in product(range(2),range(5)))/25
        for step in range(1,max(min(t-1,4) for t in co)+1):
            levels=[[sum(a*(fn(t,i,B[i]+k+1)-fn(t,i,B[i]+k)) for t,a in co.items() if min(t-1,4)>=step)
                     for i in range(25)] for k in range(step)]
            hi=levels[-1];choices=[operator(hi,step)]
            if step in (2,3):
                lo=levels[-2];choices.append(operator(lo,step)+max(h-l for h,l in zip(hi,lo))/675)
            if step==4:
                lo,mid=levels[1:3]
                choices += [operator(lo,step)+max(max(2*(m-l),h-l) for l,m,h in zip(lo,mid,hi))/2025,
                            operator(mid,step)+max(h-m for h,m in zip(hi,mid))/2025]
            value+=min(choices)
        H=[sum(a*max(b-t,0) for t,a in co.items()) for b in B]
        return value-sum(j.deletion_correction(H))+sum(a*(j.REMAINDERS[min(t-1,4)]+Z6) for t,a in co.items())

    def objective(self,co,layout,projection):
        j=self.j;B=self.head.bridge.head_load(layout)
        r,s,c63,r105,s105,r147,s245=projection
        obj=[F(0)]*N
        for i,b in enumerate(B):
            c,k=divmod(i,5)
            m=int(j.ROOT[c]==r)+int(k==s)+int(c==c63)+int(j.ROOT[c]==r105 and k==s105)
            e=int(j.ROOT[c]==r147)+int(k==s245)
            g=lambda t,v:self.depth.seven_increment(t,v,m,e)
            for mask in range(16):
                cell=16*i+mask;v=b+mask.bit_count()
                obj[cell]=sum(a*g(t,v if t>=2 else b) for t,a in co.items())
                obj[425+cell]=sum(a*max((v if t>=2 else b)-t,0) for t,a in co.items())
                for state in range(1,8):
                    n=state.bit_count()
                    obj[U+400*(state-1)+cell]=sum(a*(g(t,v+n)-g(t,v)) for t,a in co.items() if t>=2)
                    obj[V+400*(state-1)+cell]=sum(a*(max(v+n-t,0)-max(v-t,0)) for t,a in co.items() if t>=2)
        constant=sum(a*((j.REMAINDERS[0] if t==1 else j.REMAINDERS[4]-sum(CAPS))+Z6) for t,a in co.items())
        require(min(obj)>=0 and all(v==0 for v in obj[400:425]+obj[825:876]+obj[L135:]),'Every exact complete raw/survivor objective and auxiliary column')
        return obj,constant

    def dual_upper(self,co,layout,projection):
        obj,constant=self.objective(co,layout,projection)
        key=sha256(json.dumps([self.specification['rows_sha256'],encode(obj)],separators=(',',':')).encode()).hexdigest()
        if key not in self.verified:
            if key not in self.bank:
                require(self.proposer is not None,'Missing exact second-depth J dual '+key)
                self.bank[key]=self.proposer(self.lp,obj)
            self.verified[key]=self.lp.checker.check(obj,self.bank[key])
        self.used.add(key)
        return self.verified[key]+constant,key,constant

    def prior_upper(self,co,layout,projection):
        obj,const=self.pair.objective(self.core,self.j,self.head,co,layout,projection)
        key=sha256(json.dumps([self.previous.specification['rows_sha256'],encode(obj)],separators=(',',':')).encode()).hexdigest()
        if key not in self.previous.bank:return None,None
        value,checked,constant=self.previous.dual_upper(co,layout,projection)
        require(key==checked and constant==const,'Only identical251 complete objectives are reused')
        self.prior_used.add(key);return value,key

    def prior_depth_upper(self,co,layout,projection):
        previous=self.previous_depth
        obj,const=previous.objective(co,layout,projection)
        key=sha256(json.dumps([previous.specification['rows_sha256'],encode(obj)],separators=(',',':')).encode()).hexdigest()
        if key not in previous.bank:return None,None
        value,checked,constant=previous.dual_upper(co,layout,projection)
        require(key==checked and constant==const,'Only identical256 complete objectives are reused on their original3306 columns')
        self.prior_depth_used.add(key);return value,key

    def scan(self,row):
        j,head=self.j,self.head;co={int(t):F(a) for t,a in row['scan']['coefficients'].items()}
        old=head.prepare(co);six=self.prepare_six(old);scale=old['factor']/j.TOTAL
        independent=head.check_compiler(old);start=perf_counter();digest=sha256();used_before=set(self.used)
        counts={k:0 for k in ('two_projection_branches','two_bounded','four_projection_branches','four_bounded','prior251_bounded','six_projection_branches','six_affine_bounded','prior256_bounded','joint_dual_branches','strict_pair_crossings')}
        def affines(layout,projection):
            B=head.bridge.head_load(layout);correction=head.correction(old,B)
            r,s,c,rr,ss=projection[:5]
            extra=tuple(int(j.ROOT[a]==r)+int(b==s) for a,b in product(range(5),repeat=2))
            first=tuple(v+int(a==c)+int(j.ROOT[a]==rr and b==ss) for v,(a,b) in zip(extra,product(range(5),repeat=2)))
            two=head.objective(old,B,extra,correction,False);four=head.objective(old,B,first,correction,True)
            if len(projection)==5:return two,four
            r147,s245=projection[5:]
            second=tuple(int(j.ROOT[a]==r147)+int(b==s245) for a,b in product(range(5),repeat=2))
            return two,four,head.objective(six,B,tuple(zip(first,second)),correction,True)
        source=row['scan']['maximizing_certificate_branch'];seed_layout=tuple(source['layout']);seed_projection=tuple(source['projection21_35_63_105'])
        best=F(-1);witness=None
        for r,s in product(range(2),range(5)):
            projection=seed_projection+(r,s);lines=affines(seed_layout,projection)
            value,x,_=max_min_affines(lines);joint,key,const=self.dual_upper(co,seed_layout,projection)
            previous,prior_key=self.prior_upper(co,seed_layout,seed_projection)
            previous_depth,depth_key=self.prior_depth_upper(co,seed_layout,projection)
            adopted=min(scale*value,joint,*(() if previous is None else (previous,)),*(() if previous_depth is None else (previous_depth,)))
            if adopted>best:
                best=adopted;witness={'layout':seed_layout,'projection21_35_63_105_147_245':projection,'affine_complete_upper':scale*value,
                    'affine_maximizing_late_coordinate':x,'joint_complete_upper':joint,'previous251_complete_upper':previous,
                    'adopted_complete_upper':adopted,'dual_key':key,'previous251_dual_key':prior_key,
                    'previous256_complete_upper':previous_depth,'previous256_dual_key':depth_key,'complete_tail_constant':const}
        seed_record=dict(witness)
        for layout in ((0,1,2,0,2,1,2),(1,3,2,1,2,3,2)):
            for projection in ((0,1,2,1,3,0,4),(1,4,4,1,2,1,1)):
                lines=affines(layout,projection)
                for theta,x in ((j.LO,F(0)),(j.HI,F(1))):
                    require(self.rational_six(co,layout,projection,theta)==scale*(lines[2][0]+(lines[2][1]-lines[2][0])*x),
                            'Independent unscaled full six-projection affine compiler')
                    independent+=1
        maxima={k:F(-1) for k in ('two','four','prior251','six','prior256')}
        for il,layout in enumerate(j.layouts()):
            B=head.bridge.head_load(layout);correction=head.correction(old,B)
            for r,s,extra in head.extras:
                two=head.objective(old,B,extra,correction,False);counts['two_projection_branches']+=1
                upper=scale*max(two)
                if upper<=best:
                    counts['two_bounded']+=1;maxima['two']=max(maxima['two'],upper)
                    digest.update(repr(('two',layout,r,s,two)).encode());continue
                for c,rr,ss,added in head.added:
                    first=tuple(a+b for a,b in zip(extra,added));four=head.objective(old,B,first,correction,True)
                    value,x,_=j.max_min_affines(two,four);upper=scale*value;counts['four_projection_branches']+=1
                    if upper<=best:
                        counts['four_bounded']+=1;maxima['four']=max(maxima['four'],upper)
                        digest.update(repr(('four',layout,r,s,c,rr,ss,two,four)).encode());continue
                    projection=(r,s,c,rr,ss);previous,prior_key=self.prior_upper(co,layout,projection)
                    if previous is not None and previous<=best:
                        counts['prior251_bounded']+=1;maxima['prior251']=max(maxima['prior251'],previous)
                        digest.update(repr(('prior251',layout,projection,prior_key,str(previous))).encode());continue
                    for r147,s245,second in head.extras:
                        extended=projection+(r147,s245);line=head.objective(six,B,tuple(zip(first,second)),correction,True)
                        value,x,crossings=max_min_affines((two,four,line));upper=scale*value
                        counts['six_projection_branches']+=1;counts['strict_pair_crossings']+=crossings
                        if upper<=best:
                            counts['six_affine_bounded']+=1;maxima['six']=max(maxima['six'],upper)
                            digest.update(repr(('six-affine',layout,extended,two,four,line)).encode());continue
                        previous_depth,depth_key=self.prior_depth_upper(co,layout,extended)
                        if previous_depth is not None and previous_depth<=best:
                            counts['prior256_bounded']+=1;maxima['prior256']=max(maxima['prior256'],previous_depth)
                            digest.update(repr(('prior256',layout,extended,depth_key,str(previous_depth))).encode());continue
                        joint,key,const=self.dual_upper(co,layout,extended)
                        adopted=min(upper,joint,*(() if previous is None else (previous,)),*(() if previous_depth is None else (previous_depth,)))
                        counts['joint_dual_branches']+=1
                        digest.update(repr(('joint',layout,extended,two,four,line,key,str(joint),prior_key,depth_key)).encode())
                        if adopted>best:
                            best=adopted;witness={'layout':layout,'projection21_35_63_105_147_245':extended,'affine_complete_upper':upper,
                                'affine_maximizing_late_coordinate':x,'joint_complete_upper':joint,'previous251_complete_upper':previous,
                                'adopted_complete_upper':adopted,'dual_key':key,'previous251_dual_key':prior_key,
                                'previous256_complete_upper':previous_depth,'previous256_dual_key':depth_key,'complete_tail_constant':const}
            if il%2500==0:print('J triple second depth '+str(row['index'])+': layouts='+str(il)+', LP branches='+str(counts['joint_dual_branches'])+', seconds='+str(round(perf_counter()-start,2)),flush=True)
        require(counts['two_projection_branches']==125000
                and counts['four_projection_branches']==50*(125000-counts['two_bounded'])
                and counts['six_projection_branches']==10*(counts['four_projection_branches']-counts['four_bounded']-counts['prior251_bounded'])
                and counts['joint_dual_branches']+counts['six_affine_bounded']+counts['prior256_bounded']==counts['six_projection_branches']
                and 500*counts['two_bounded']+10*(counts['four_bounded']+counts['prior251_bounded'])+counts['six_projection_branches']==62500000
                and max(maxima.values())<=best,'Every62500000 original containing choice is explicitly covered')
        layout=witness['layout'];projection=witness['projection21_35_63_105_147_245'];lines=affines(layout,projection)
        value,x,_=max_min_affines(lines);joint,key,const=self.dual_upper(co,layout,projection)
        previous,prior_key=self.prior_upper(co,layout,projection[:5])
        previous_depth,depth_key=self.prior_depth_upper(co,layout,projection)
        require(previous_depth==witness['previous256_complete_upper'] and depth_key==witness['previous256_dual_key']
                and scale*value==witness['affine_complete_upper'] and x==witness['affine_maximizing_late_coordinate']
                and joint==witness['joint_complete_upper'] and key==witness['dual_key'] and previous==witness['previous251_complete_upper']
                and min(scale*value,joint,*(() if previous is None else (previous,)),*(() if previous_depth is None else (previous_depth,)))==best,'Exact complete maximizing certificate branch; no actual attainment claim')
        for x in (F(0),F(1),witness['affine_maximizing_late_coordinate']):
            theta=j.LO+(j.HI-j.LO)*x
            require(self.rational_six(co,layout,projection,theta)==scale*(lines[2][0]+(lines[2][1]-lines[2][0])*x),
                    'Independent maximizing-branch six-projection endpoints and common crossing')
            independent+=1
        print('Finished complete264 target '+str(row['index'])+' in '+str(round(perf_counter()-start,6))+' seconds',flush=True)
        return {'coefficients':co,'complete_hinge_upper':best,'counts':counts,'covered_containing_choices':62500000,
                'seed':seed_record,'maximizing_certificate_branch':witness,'complete_tail_constant':const,
                'independent_affine_checks':independent,'maximum_pruned':maxima,'new_distinct_duals':len(self.used-used_before),
                'all_branch_decisions_sha256':digest.hexdigest()}


def calculate(base,bank=None,proposer=None):
    require(PINS,'Pinned existing mathematical sources')
    io=module('j_triple_depth_io',base/'certificate_io.py');core=module('j_triple_depth_core244',base/'frontier/j_face_joint_selected_heads.py')
    read=lambda name:json.loads(io.read_artifact_bytes(base/'certificates/source_norms'/(name+'.json')),object_pairs_hook=core.unique)
    prior244,prior251,prior256=(read(n)for n in('j_face_joint_selected_heads','j_face_retained135125_heads','j_face_second_depth_retained_heads'));pins=dict(PINS)
    for source in(prior244,prior251,prior256):
        for path,pin in source['source_sha256'].items():
            require(path not in pins or pins[path]==pin,'Consistent complete J source closure '+path);pins[path]=pin
    for path,pin in pins.items():require(sha256(io.read_artifact_bytes(base/path)).hexdigest()==pin,'Pinned mathematical input '+path)
    j=module('j_triple_depth_source',base/'frontier/j_face_coupled_seven_heads.py');pair=module('j_triple_depth_pair',base/'frontier/j_face_retained135125_heads.py')
    depth=module('j_triple_depth_formula',base/'frontier/second_depth_seven_comparison.py')
    require(j.Z4-F(6,245)*(F(1,8)+F(1,10))==Z6 and Z6>0,'Exactly the J-specific assigned147/245 cap summands are removed')
    require(prior244['geometry']==prior251['geometry']==prior256['geometry'] and prior251['source_mass']=='1/4' and prior251['survivor_mass']=='3/20','The same two actual saturated J faces')
    problem=TripleSecondDepthJHead(base,j,core,pair,depth,prior244,prior251,prior256,bank,proposer);rows=[]
    for src in prior251['results']:
        scan=problem.scan(src);at_one=F(src['at_one']);whole=at_one*F(3,20)+scan['complete_hinge_upper']
        old_upper=F(next(r for r in prior256['results'] if r['index']==src['index'])['adopted_upper']);mean=F(src['complete_mean_only_upper']);adopted=min(whole,old_upper,mean)
        rows.append({'index':src['index'],'at_one':at_one,'scan':scan,'complete_head_upper':whole,'previous_adopted_upper':old_upper,
                     'complete_mean_only_upper':mean,'adopted_upper':adopted,'improvement_over_previous':old_upper-adopted})
        print('Complete J triple second depth '+str(src['index'])+' <= '+str(float(adopted))+'; distinct new duals='+str(scan['new_distinct_duals']),flush=True)
        if proposer is not None:print('Complete maximizing certificate branch '+str(src['index'])+': '+json.dumps(encode(scan['maximizing_certificate_branch']),sort_keys=True),flush=True)
    require((proposer is not None or problem.used==set(problem.bank)) and any(r['improvement_over_previous']>0 for r in rows),'Every retained dual consumed and a strict complete original-target improvement')
    retained={key:problem.bank[key] for key in sorted(problem.used)}
    encoded=problem.codec.encode_dual_bank(retained,inequality_count=11211,equality_count=19)
    require(problem.codec.decode_dual_bank(encoded,inequality_count=11211,equality_count=19)==retained,'Lossless entire rational dual bank')
    return encode({'schema':'erdos7-j-face-triple-second-depth-heads-v1','source_sha256':pins,'geometry':prior251['geometry'],
        'source_mass':F(1,4),'survivor_mass':F(3,20),'complete_mean_upper':F(16,25),'model':problem.specification,
        'retained_positive7_labels':[21,35,63,105,147,245],'removed_assigned_tail_caps':[F(3,980),F(3,1225)],'complete_positive7_tail':Z6,
        'results':rows,'encoded_rational_duals':encoded,'distinct_dual_count':len(problem.used),'rational_column_checks':N*len(problem.used),
        'previous251_duals_used':sorted(problem.prior_used),'previous256_duals_used':sorted(problem.prior_depth_used),'total_containing_choices':sum(r['scan']['covered_containing_choices'] for r in rows),
        'total_independent_affine_checks':sum(r['scan']['independent_affine_checks'] for r in rows),
        'scope':'Three complete original AP13/heavy0/heavy16 comparisons on both entire actual saturated J faces. All62500000 original containing choices per target, all common late coordinates, 6531-variable actual-source model with seven independent135/125/225 membership states and their complement, all independent147/245 projections and every exponent tail are included. Only the general arbitrary-residue two-depth bridge is reused from204; no K source caps are imported. No actual-source attainment, off-face extension, complete52-cost/global comparison, Lean verification or unrestricted Erdos7 resolution is asserted.'})


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[1]);parser.add_argument('--check',action='store_true');args=parser.parse_args()
    io=module('j_triple_depth_read',args.base/'certificate_io.py');core=module('j_triple_depth_json',args.base/'frontier/j_face_joint_selected_heads.py')
    stored=json.loads(io.read_artifact_bytes(args.base/CERTIFICATE),object_pairs_hook=core.unique)
    codec=module('j_triple_depth_read_codec',args.base/'frontier/retained135_heavy_comparison.py')
    bank=codec.decode_dual_bank(stored['encoded_rational_duals'],inequality_count=11211,equality_count=19)
    require(calculate(args.base,bank=bank)==stored,'Every complete J second-depth certificate field recomputes exactly')
    print('PASS:3 complete second-depth J heads,187500000 original containing choices,'+str(stored['distinct_dual_count'])+' exact6531-column duals and full exponent tails.',flush=True)


if __name__=='__main__':
    try:main()
    except(ValueError,ArithmeticError,OSError,KeyError,TypeError,json.JSONDecodeError)as error:
        print('FAIL: '+str(error),file=sys.stderr);raise SystemExit(1)
