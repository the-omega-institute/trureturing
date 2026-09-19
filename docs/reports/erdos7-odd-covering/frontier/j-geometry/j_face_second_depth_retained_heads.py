#!/usr/bin/env python3
"""Complete J heads with retained135/125 and independent147/245 projections."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import product, combinations
import importlib.util
import json
from pathlib import Path
import sys
from time import perf_counter
sys.dont_write_bytecode=True
CERTIFICATE='certificates/source_norms/j-geometry/j_face_second_depth_retained_heads.json'
Z6=F(37,1225)
PINS={'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2', 'frontier/j-geometry/j_face_retained135125_heads.py': 'bb2ed1f5080200551856bdcb923173cb9304f2e81ee50275b47fd609c1ec4db3', 'certificates/source_norms/j-geometry/j_face_retained135125_heads.json': '349a926dddeb147354859b5fb908ab0eb33c84e6cadba7feb179155a22ead1c4', 'profile-notes/193-256/251-two-retained-original-tests-sharpen-the-complete-j-heads.md': '956114312252a12381562ce4b4dfd789108fe19c526411c4166b00e7b56243c2', 'frontier/comparison-bounds/second_depth_seven_comparison.py': 'b49a13dde9aa26ce8b1a132c11f3a9bc125d995b9497567c7bff26eb2f4bb239', 'profile-notes/193-256/204-a-second-seven-depth-strengthens-both-complete-heavy-costs.md': 'c42016b434400d533e56cc3778c3d110b2168d0763d700ebc47747058f7f446f'}


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


class SecondDepthJHead:
    def __init__(self,base,j,core,pair,depth,prior244,prior251,bank=None,proposer=None):
        self.j,self.core,self.pair,self.depth=j,core,pair,depth
        self.codec=module('j_depth_codec',base/'frontier/retained-transport/retained135_heavy_comparison.py')
        oldbank=self.codec.decode_dual_bank(prior251['encoded_rational_duals'],inequality_count=6354,equality_count=18)
        self.previous=pair.RetainedJPairHead(base,j,core,prior244,bank=oldbank)
        self.head,self.lp=self.previous.head,self.previous.lp
        self.specification=self.previous.specification
        require(self.specification==prior251['model'],'Unchanged entire251 actual-source model')
        self.bank={} if bank is None else bank;self.proposer=proposer
        self.used,self.verified,self.prior_used=set(),{},set()
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
        j,pair=self.j,self.pair;B=self.head.bridge.head_load(layout)
        r,s,c63,r105,s105,r147,s245=projection
        obj=[F(0)]*3306
        for i,b in enumerate(B):
            c,k=divmod(i,5)
            m=int(j.ROOT[c]==r)+int(k==s)+int(c==c63)+int(j.ROOT[c]==r105 and k==s105)
            e=int(j.ROOT[c]==r147)+int(k==s245)
            g=lambda t,v:self.depth.seven_increment(t,v,m,e)
            for mask in range(16):
                cell=16*i+mask;v=b+mask.bit_count()
                obj[cell]=sum(a*g(t,v if t>=2 else b) for t,a in co.items())
                obj[425+cell]=sum(a*max((v if t>=2 else b)-t,0) for t,a in co.items())
                for state,n in enumerate((1,1,2)):
                    obj[pair.U+400*state+cell]=sum(a*(g(t,v+n)-g(t,v)) for t,a in co.items() if t>=2)
                    obj[pair.V+400*state+cell]=sum(a*(max(v+n-t,0)-max(v-t,0)) for t,a in co.items() if t>=2)
        constant=sum(a*((j.REMAINDERS[0] if t==1 else j.REMAINDERS[4]-pair.CAP135-pair.CAP125)+Z6) for t,a in co.items())
        require(min(obj)>=0 and all(v==0 for v in obj[400:425]+obj[825:876]+obj[3276:]),'Every exact complete raw/survivor objective and auxiliary column')
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
        key=sha256(json.dumps([self.specification['rows_sha256'],encode(obj)],separators=(',',':')).encode()).hexdigest()
        if key not in self.previous.bank:return None,None
        value,checked,constant=self.previous.dual_upper(co,layout,projection)
        require(key==checked and constant==const,'Only identical251 complete objectives are reused')
        self.prior_used.add(key);return value,key

    def scan(self,row):
        j,head=self.j,self.head;co={int(t):F(a) for t,a in row['scan']['coefficients'].items()}
        old=head.prepare(co);six=self.prepare_six(old);scale=old['factor']/j.TOTAL
        independent=head.check_compiler(old);start=perf_counter();digest=sha256();used_before=set(self.used)
        counts={k:0 for k in ('two_projection_branches','two_bounded','four_projection_branches','four_bounded','prior251_bounded','six_projection_branches','six_affine_bounded','joint_dual_branches','strict_pair_crossings')}
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
            adopted=min(scale*value,joint,*(() if previous is None else (previous,)))
            if adopted>best:
                best=adopted;witness={'layout':seed_layout,'projection21_35_63_105_147_245':projection,'affine_complete_upper':scale*value,
                    'affine_maximizing_late_coordinate':x,'joint_complete_upper':joint,'previous251_complete_upper':previous,
                    'adopted_complete_upper':adopted,'dual_key':key,'previous251_dual_key':prior_key,'complete_tail_constant':const}
        seed_record=dict(witness)
        for layout in ((0,1,2,0,2,1,2),(1,3,2,1,2,3,2)):
            for projection in ((0,1,2,1,3,0,4),(1,4,4,1,2,1,1)):
                lines=affines(layout,projection)
                for theta,x in ((j.LO,F(0)),(j.HI,F(1))):
                    require(self.rational_six(co,layout,projection,theta)==scale*(lines[2][0]+(lines[2][1]-lines[2][0])*x),
                            'Independent unscaled full six-projection affine compiler')
                    independent+=1
        maxima={k:F(-1) for k in ('two','four','prior251','six')}
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
                        joint,key,const=self.dual_upper(co,layout,extended)
                        adopted=min(upper,joint,*(() if previous is None else (previous,)))
                        counts['joint_dual_branches']+=1
                        digest.update(repr(('joint',layout,extended,two,four,line,key,str(joint),prior_key)).encode())
                        if adopted>best:
                            best=adopted;witness={'layout':layout,'projection21_35_63_105_147_245':extended,'affine_complete_upper':upper,
                                'affine_maximizing_late_coordinate':x,'joint_complete_upper':joint,'previous251_complete_upper':previous,
                                'adopted_complete_upper':adopted,'dual_key':key,'previous251_dual_key':prior_key,'complete_tail_constant':const}
            if il%2500==0:print('J second depth '+str(row['index'])+': layouts='+str(il)+', LP branches='+str(counts['joint_dual_branches'])+', seconds='+str(round(perf_counter()-start,2)),flush=True)
        require(counts['two_projection_branches']==125000
                and counts['four_projection_branches']==50*(125000-counts['two_bounded'])
                and counts['six_projection_branches']==10*(counts['four_projection_branches']-counts['four_bounded']-counts['prior251_bounded'])
                and counts['joint_dual_branches']+counts['six_affine_bounded']==counts['six_projection_branches']
                and 500*counts['two_bounded']+10*(counts['four_bounded']+counts['prior251_bounded'])+counts['six_projection_branches']==62500000
                and max(maxima.values())<=best,'Every62500000 original containing choice is explicitly covered')
        layout=witness['layout'];projection=witness['projection21_35_63_105_147_245'];lines=affines(layout,projection)
        value,x,_=max_min_affines(lines);joint,key,const=self.dual_upper(co,layout,projection)
        previous,prior_key=self.prior_upper(co,layout,projection[:5])
        require(scale*value==witness['affine_complete_upper'] and x==witness['affine_maximizing_late_coordinate']
                and joint==witness['joint_complete_upper'] and key==witness['dual_key'] and previous==witness['previous251_complete_upper']
                and min(scale*value,joint,*(() if previous is None else (previous,)))==best,'Exact complete maximizing certificate branch; no actual attainment claim')
        for x in (F(0),F(1),witness['affine_maximizing_late_coordinate']):
            theta=j.LO+(j.HI-j.LO)*x
            require(self.rational_six(co,layout,projection,theta)==scale*(lines[2][0]+(lines[2][1]-lines[2][0])*x),
                    'Independent maximizing-branch six-projection endpoints and common crossing')
            independent+=1
        return {'coefficients':co,'complete_hinge_upper':best,'counts':counts,'covered_containing_choices':62500000,
                'seed':seed_record,'maximizing_certificate_branch':witness,'complete_tail_constant':const,
                'independent_affine_checks':independent,'maximum_pruned':maxima,'new_distinct_duals':len(self.used-used_before),
                'all_branch_decisions_sha256':digest.hexdigest()}


def calculate(base,bank=None,proposer=None):
    require(PINS,'Pinned existing mathematical sources')
    io=module('j_depth_io',base/'certificate_io.py');core=module('j_depth_core244',base/'frontier/j-geometry/j_face_joint_selected_heads.py')
    read=lambda name:json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', name+'.json')),object_pairs_hook=core.unique)
    prior244,prior251=read('j_face_joint_selected_heads'),read('j_face_retained135125_heads');pins=dict(PINS)
    for source in(prior244,prior251):
        for path,pin in source['source_sha256'].items():
            require(path not in pins or pins[path]==pin,'Consistent complete J source closure '+path);pins[path]=pin
    for path,pin in pins.items():require(sha256(io.read_artifact_bytes(base/path)).hexdigest()==pin,'Pinned mathematical input '+path)
    j=module('j_depth_source',base/'frontier/j-geometry/j_face_coupled_seven_heads.py');pair=module('j_depth_pair',base/'frontier/j-geometry/j_face_retained135125_heads.py')
    depth=module('j_depth_formula',base/'frontier/comparison-bounds/second_depth_seven_comparison.py')
    require(j.Z4-F(6,245)*(F(1,8)+F(1,10))==Z6 and Z6>0,'Exactly the J-specific assigned147/245 cap summands are removed')
    require(prior244['geometry']==prior251['geometry'] and prior251['source_mass']=='1/4' and prior251['survivor_mass']=='3/20','The same two actual saturated J faces')
    problem=SecondDepthJHead(base,j,core,pair,depth,prior244,prior251,bank,proposer);rows=[]
    for src in prior251['results']:
        scan=problem.scan(src);at_one=F(src['at_one']);whole=at_one*F(3,20)+scan['complete_hinge_upper']
        old_upper=F(src['adopted_upper']);mean=F(src['complete_mean_only_upper']);adopted=min(whole,old_upper,mean)
        rows.append({'index':src['index'],'at_one':at_one,'scan':scan,'complete_head_upper':whole,'previous_adopted_upper':old_upper,
                     'complete_mean_only_upper':mean,'adopted_upper':adopted,'improvement_over_previous':old_upper-adopted})
        print('Complete J second depth '+str(src['index'])+' <= '+str(float(adopted))+'; distinct new duals='+str(scan['new_distinct_duals']),flush=True)
        if proposer is not None:print('Complete maximizing certificate branch '+str(src['index'])+': '+json.dumps(encode(scan['maximizing_certificate_branch']),sort_keys=True),flush=True)
    require(problem.used==set(problem.bank) and any(r['improvement_over_previous']>0 for r in rows),'Every retained dual consumed and a strict complete original-target improvement')
    retained={key:problem.bank[key] for key in sorted(problem.used)}
    encoded=problem.codec.encode_dual_bank(retained,inequality_count=6354,equality_count=18)
    require(problem.codec.decode_dual_bank(encoded,inequality_count=6354,equality_count=18)==retained,'Lossless entire rational dual bank')
    return encode({'schema':'erdos7-j-face-second-depth-retained-heads-v1','source_sha256':pins,'geometry':prior251['geometry'],
        'source_mass':F(1,4),'survivor_mass':F(3,20),'complete_mean_upper':F(16,25),'model':problem.specification,
        'retained_positive7_labels':[21,35,63,105,147,245],'removed_assigned_tail_caps':[F(3,980),F(3,1225)],'complete_positive7_tail':Z6,
        'results':rows,'encoded_rational_duals':encoded,'distinct_dual_count':len(problem.used),'rational_column_checks':3306*len(problem.used),
        'previous251_duals_used':sorted(problem.prior_used),'total_containing_choices':sum(r['scan']['covered_containing_choices'] for r in rows),
        'total_independent_affine_checks':sum(r['scan']['independent_affine_checks'] for r in rows),
        'scope':'Three complete original AP13/heavy0/heavy16 comparisons on both entire actual saturated J faces. All62500000 original containing choices per target, all common late coordinates, unchanged3306-variable actual-source135/125 model, all independent147/245 projections and every exponent tail are included. Only the general arbitrary-residue two-depth bridge is reused from204; no K source caps are imported. No actual-source attainment, off-face extension, complete52-cost/global comparison, Lean verification or unrestricted Erdos7 resolution is asserted.'})


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2]);parser.add_argument('--check',action='store_true');args=parser.parse_args()
    io=module('j_depth_read',args.base/'certificate_io.py');core=module('j_depth_json',args.base/'frontier/j-geometry/j_face_joint_selected_heads.py')
    stored=json.loads(io.read_artifact_bytes(args.base/CERTIFICATE),object_pairs_hook=core.unique)
    codec=module('j_depth_read_codec',args.base/'frontier/retained-transport/retained135_heavy_comparison.py')
    bank=codec.decode_dual_bank(stored['encoded_rational_duals'],inequality_count=6354,equality_count=18)
    require(calculate(args.base,bank=bank)==stored,'Every complete J second-depth certificate field recomputes exactly')
    print('PASS:3 complete second-depth J heads,187500000 original containing choices,'+str(stored['distinct_dual_count'])+' exact3306-column duals and full exponent tails.',flush=True)


if __name__=='__main__':
    try:main()
    except(ValueError,ArithmeticError,OSError,KeyError,TypeError,json.JSONDecodeError)as error:
        print('FAIL: '+str(error),file=sys.stderr);raise SystemExit(1)
