#!/usr/bin/env python3
"""Complete original J AP13 keeps independent second-depth cofactors441/735."""
import argparse
import importlib.util
import json
import sys
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from hashlib import sha256
sys.dont_write_bytecode=True
CERTIFICATE='certificates/source_norms/j_face_second_cofactor_survival_heads.json'
PINS={'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232', 'frontier/j_face_coupled_seven_heads.py': 'd2794b380770dcd5529bacc0fb134d0e7ea82c26c572339b65e30c8222e24946', 'frontier/j_face_joint_selected_heads.py': '01033d19b43910a667954005342d2a03fe57dd6f621bf319398cfdb77ec821ec', 'frontier/j_face_retained135125_heads.py': 'db804300e915d153152d1a0b078233e3ac026f82ec296fb2deea480813aebdd5', 'frontier/second_depth_seven_comparison.py': '5544b70201a721be7ca0dfa92155c4b186235a19f52a5fd85346f85c02cfc950', 'frontier/j_face_second_depth_retained_heads.py': '02cca63e4ea4dd3771d6212351186e92e3743df171ad78ea613219b688733957', 'certificates/source_norms/j_face_joint_selected_heads.json': '87038435aecbfee3d5a3845c29fe9ece863652a79a35312af00f1096b952fed6', 'certificates/source_norms/j_face_retained135125_heads.json': 'b9a65e86cf068edc78cd66998683e19df409d437c82de36dbb22658c781f3ae8', 'certificates/source_norms/j_face_second_depth_retained_heads.json': 'e9bc7201404e9c70bce6b1614b9ebe9db53e03429bfd6d0f7468679017b86c3d'}

def require(ok,message):
    if not ok:raise ValueError(message)

def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    require(spec is not None and spec.loader is not None,'Loadable original source')
    value=importlib.util.module_from_spec(spec);spec.loader.exec_module(value);return value

def calculate(B,bank):
    pins=dict(PINS)
    def load(n):
     path=B/(n+'.py');require(sha256(path.read_bytes()).hexdigest()==PINS[n+'.py'],'Pinned original program '+n)
     sp=importlib.util.spec_from_file_location('cofactor_'+n.replace('/','_'),path);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m);return m
    io=load('certificate_io');j=load('frontier/j_face_coupled_seven_heads');core=load('frontier/j_face_joint_selected_heads');pair=load('frontier/j_face_retained135125_heads');depth=load('frontier/second_depth_seven_comparison');second=load('frontier/j_face_second_depth_retained_heads')
    def read(n):
     path='certificates/source_norms/'+n+'.json';raw=io.read_artifact_bytes(B/path);require(sha256(raw).hexdigest()==PINS[path],'Pinned original certificate '+n)
     value=json.loads(raw)
     for rel,pin in value['source_sha256'].items():
      require(rel not in pins or pins[rel]==pin,'Consistent complete source closure '+rel);pins[rel]=pin
     return value
    s244,s251,s256=[read(n)for n in ('j_face_joint_selected_heads','j_face_retained135125_heads','j_face_second_depth_retained_heads')]
    for rel,pin in pins.items():require(sha256(io.read_artifact_bytes(B/rel)).hexdigest()==pin,'Pinned whole original source '+rel)
    problem=second.SecondDepthJHead(B,j,core,pair,depth,s244,s251)
    require(problem.specification==s256['model'],'Same complete original actual source model')
    require(problem.lp.nvars==3306 and len(problem.lp.rows)==6354 and len(problem.lp.equalities)==18,'No source variables or constraints changed')
    # The independent original labels441/735 use the same absolute raw cofactor
    # caps as63/105, with seven multiplier6/245 instead of6/35.
    removed=F(6,245)*(F(1,12)+F(1,15));remainder=second.Z6-removed
    require(j.Z2-F(6,35)*(F(1,12)+F(1,15))==j.Z4,'Original63/105 assigned cap summands')
    require(removed==F(9,2450) and remainder==F(13,490)>0,'Exact complementary infinite positive-seven tail')
    # For v>=t the raw cap kernel is constant; finite differences below t
    # certify every remaining transition. These are all nonzero thresholds used.
    transition_count=0
    for t,m,e in product(range(1,5),range(5),range(5)):
     values=[depth.seven_increment(t,v,m,e) for v in range(1,t+3)]
     increments=[b-a for a,b in zip(values,values[1:])]
     require(min(increments)>=0,'Raw capped hinge increment is increasing')
     require(values[-1]==values[-2]==F(6,35)*(1+m)+F(6,245)*(1+e)+F(1,245),'Exact entire v>=t continuation')
     for w in (F(2,5),F(3,5),F(4,5),F(1)):
      total=[w*max(v-t,0)+depth.seven_increment(t,v,m,e)for v in range(1,t+3)]
      diff=[b-a for a,b in zip(total,total[1:])]
      require(min(diff)>=0 and all(a<=b for a,b in zip(diff,diff[1:])),'Full survivor-plus-raw bridge is integer convex')
     transition_count+=len(values)

    def objective(co,layout,projection,new):
     Bload=problem.head.bridge.head_load(layout);r,s,c63,r105,s105,r147,s245=projection;c441,r735,s735=new
     obj=[F(0)]*3306
     for i,b in enumerate(Bload):
      c,k=divmod(i,5)
      m=int(j.ROOT[c]==r)+int(k==s)+int(c==c63)+int(j.ROOT[c]==r105 and k==s105)
      e=int(j.ROOT[c]==r147)+int(k==s245)+int(c==c441)+int(j.ROOT[c]==r735 and k==s735)
      g=lambda t,v:depth.seven_increment(t,v,m,e)
      for mask in range(16):
       cell=16*i+mask;v=b+mask.bit_count()
       obj[cell]=sum(a*g(t,v if t>=2 else b) for t,a in co.items())
       obj[425+cell]=sum(a*max((v if t>=2 else b)-t,0) for t,a in co.items())
       for st,n in enumerate((1,1,2)):
        obj[pair.U+400*st+cell]=sum(a*(g(t,v+n)-g(t,v))for t,a in co.items()if t>=2)
        obj[pair.V+400*st+cell]=sum(a*(max(v+n-t,0)-max(v-t,0))for t,a in co.items()if t>=2)
     const=sum(a*((j.REMAINDERS[0]if t==1 else j.REMAINDERS[4]-pair.CAP135-pair.CAP125)+remainder)for t,a in co.items())
     require(min(obj)>=0 and all(v==0 for v in obj[400:425]+obj[825:876]+obj[3276:]),'Only original actual-source/survivor objective columns')
     return obj,const


    oldrow=next(r for r in s256['results']if r['index']=='AP13')
    controller=oldrow['scan']['maximizing_certificate_branch']
    seed_layout=tuple(controller['layout']);seed_projection=tuple(controller['projection21_35_63_105_147_245'])
    seed_bounds={};seedchecks=0;seed_records=[];seed_used=set()
    for new in product(range(5),range(2),range(5)):
     obj,const=objective({4:F(1)},seed_layout,seed_projection,new)
     key=sha256(json.dumps(second.encode(obj),separators=(',',':')).encode()).hexdigest()
     require(key in bank,'A complete exact original-controller seed dual')
     upper=problem.lp.checker.check(obj,bank[key])+const
     adopted=min(upper,F(oldrow['adopted_upper']))
     seed_bounds[seed_layout,seed_projection,new]=adopted;seedchecks+=3306;seed_used.add(key)
     seed_records.append({'layout':seed_layout,'projection':seed_projection,'projection441_735':new,'dual_upper':upper,'complete_tail_constant':const,'adopted_upper':adopted,'dual_key':key})
    require(len(seed_bounds)==50 and seed_used==set(bank),'Exactly all50 independent new label seeds and no unused duals')
    worst_seed=max(seed_records,key=lambda r:r['adopted_upper']);incumbent=worst_seed['adopted_upper']
    require(0<incumbent<F(oldrow['adopted_upper']),'Strict complete-source AP13 candidate improvement')
    problem.bank=problem.codec.decode_dual_bank(s256['encoded_rational_duals'],inequality_count=6354,equality_count=18)
    head=problem.head;old=head.prepare({4:F(1)});six=problem.prepare_six(old);scale=old['factor']/j.TOTAL;weights=sorted(set(head.w))
    # Generic integer-convex telescoping keeps all four independent old labels.
    # The fourth step is licensed by the same raw intersection bounds as the
    # existing t>=5 compiler; its applicability depends on ordered increments.
    pairs=list(product(range(5),range(5)))
    raw={}
    for w,(m,e) in product(weights,pairs):
     raw[w,m,e]=[0]+[j.integer(j.SCALE*(F(w,5)*max(v-4,0)+depth.seven_increment(4,v,m,e)))for v in range(1,11)]
     for v in range(1,7):
      inc=[raw[w,m,e][v+k+1]-raw[w,m,e][v+k]for k in range(4)]
      require(min(inc)>=0 and all(a<=b for a,b in zip(inc,inc[1:])),'Four-step integer convex telescoping for H4')
    def prepared(tail):
     tab={(w,p):[0]+[raw[w,*p][v]for v in range(1,7)]for w,p in product(weights,pairs)}
     inc={(i,k):{(w,p):[0]+[raw[w,*p][v+k+1]-raw[w,*p][v+k]for v in range(1,7)]for w,p in product(weights,pairs)}for i in range(1,5)for k in range(i)}
     const=j.integer(j.TOTAL*(j.REMAINDERS[4]+tail))
     return {**old,'highest_selected_label':4,'head':tab,'increments':inc,'constants':(const,const)}
    records={'two':prepared(j.Z2),'four':prepared(j.Z4),'six':prepared(second.Z6),'seven':prepared(second.Z6-F(1,490)),'eight':prepared(remainder)}
    # The independent rational formula reads actual p/e/w and original cap
    # operators directly; it shares no scaled tables with head.objective.
    def rational(lay,first,sec,tail,theta):
     BB=head.bridge.head_load(lay);p,caps,e,w=j.source_tables(theta);flatw=[v for row in w for v in row]
     f=lambda i,v:flatw[i]*max(v-4,0)+depth.seven_increment(4,v,first[i],sec[i])
     z=[f(i,v)for i,v in enumerate(BB)];value=j.raw_source_lp(z,theta)
     def op(a,step):
      if step in (2,4):return max(sum(p[c][s]*a[5*c+s]for s in range(5))for c in range(5))/(27 if step==2 else 81)
      if step==1:return max(sum(e[c][s]*a[5*c+s]for c in range(5))for s in range(5))/25
      return max(sum(e[c][s]*a[5*c+s]for c in range(5)if j.ROOT[c]==rr)for rr,s in product(range(2),range(5)))/25
     for step in range(1,5):
      levels=[[f(i,v+k+1)-f(i,v+k)for i,v in enumerate(BB)]for k in range(step)];hi=levels[-1];choices=[op(hi,step)]
      if step in (2,3):
       lo=levels[-2];choices.append(op(lo,step)+max(h-l for h,l in zip(hi,lo))/675)
      if step==4:
       lo,mid=levels[1:3]
       choices.extend([op(lo,step)+max(max(2*(m-l),h-l)for l,m,h in zip(lo,mid,hi))/2025,op(mid,step)+max(h-m for h,m in zip(hi,mid))/2025])
      value+=min(choices)
     return value-sum(j.deletion_correction([F(max(v-4,0))for v in BB]))+j.REMAINDERS[4]+tail
    verify_count=0
    for lay,pr in [((1,4,2,1,2,4,2),(1,4,4,1,4,1,4)),((0,1,2,0,2,1,2),(0,1,2,1,3,0,4)),((1,3,2,1,2,3,2),(1,2,3,0,3,1,1))]:
     BB=head.bridge.head_load(lay);cor=head.correction(old,BB);r,s,c63,r105,s105,r147,s245=pr
     first=tuple(int(j.ROOT[c]==r)+int(k==s)+int(c==c63)+int(j.ROOT[c]==r105 and k==s105)for c,k in product(range(5),repeat=2))
     sec=tuple(int(j.ROOT[c]==r147)+int(k==s245)for c,k in product(range(5),repeat=2))
     for c441,r735,s735 in product(range(5),range(2),range(5)):
      sec7=tuple(a+int(c==c441)for a,(c,k)in zip(sec,product(range(5),repeat=2)))
      sec8=tuple(a+int(j.ROOT[c]==r735 and k==s735)for a,(c,k)in zip(sec7,product(range(5),repeat=2)))
      for name,ss,tail in [('seven',sec7,second.Z6-F(1,490)),('eight',sec8,remainder)]:
       aff=head.objective(records[name],BB,tuple(zip(first,ss)),cor,True)
       for theta,x in ((j.LO,0),(j.HI,1)):
        require(scale*aff[x]==rational(lay,first,ss,tail,theta),'Independent complete rational affine endpoint')
        verify_count+=1

    threshold=incumbent/scale
    counts={k:0 for k in ('layouts','two_seen','two_old_bounded','two_enhanced_bounded','four_seen','four_old_bounded','four_enhanced_bounded','six_seen','six_old_bounded','six_enhanced_bounded','six_known_dual_bounded','seven_seen','seven_bounded','eight_seen','eight_bounded','seed_bounded','lp_remaining')}
    digest=sha256();remaining=[];old_dual_used=set();max_pruned={}
    def bounded(lines):
     value,at,_=second.max_min_affines(lines)
     return value<=threshold,value,at
    def mark(kind,record,upper):
     counts[kind]+=1;digest.update(repr((kind,record,upper)).encode());max_pruned[kind]=max(max_pruned.get(kind,F(0)),scale*upper)
    for il,lay in enumerate(j.layouts()):
     counts['layouts']+=1;BB=head.bridge.head_load(lay);cor=head.correction(old,BB)
     for r,s,ex in head.extras:
      counts['two_seen']+=1;two=head.objective(old,BB,ex,cor,False)
      if max(two)<=threshold:mark('two_old_bounded',(lay,r,s),max(two));continue
      two4=head.objective(records['two'],BB,tuple((m,0)for m in ex),cor,True);two_lines=(two,two4);ok,v,_=bounded(two_lines)
      if ok:mark('two_enhanced_bounded',(lay,r,s),v);continue
      for c63,r105,s105,added in head.added:
       counts['four_seen']+=1;first=tuple(a+b for a,b in zip(ex,added));four=head.objective(old,BB,first,cor,True);lines=two_lines+(four,);ok,v,_=bounded(lines)
       prefix=(r,s,c63,r105,s105)
       if ok:mark('four_old_bounded',(lay,prefix),v);continue
       four4=head.objective(records['four'],BB,tuple((m,0)for m in first),cor,True);lines+=(four4,);ok,v,_=bounded(lines)
       if ok:mark('four_enhanced_bounded',(lay,prefix),v);continue
       for r147,s245,sec in head.extras:
        counts['six_seen']+=1;pr=prefix+(r147,s245);sixline=head.objective(six,BB,tuple(zip(first,sec)),cor,True);sixlines=lines+(sixline,);ok,v,_=bounded(sixlines)
        if ok:mark('six_old_bounded',(lay,pr),v);continue
        six4=head.objective(records['six'],BB,tuple(zip(first,sec)),cor,True);sixlines+=(six4,);ok,v,_=bounded(sixlines)
        if ok:mark('six_enhanced_bounded',(lay,pr),v);continue
        # Reuse only a byte-identical original objective's existing source dual.
        oo,cc=problem.objective({4:F(1)},lay,pr);key=sha256(json.dumps([problem.specification['rows_sha256'],second.encode(oo)],separators=(',',':')).encode()).hexdigest()
        if key in problem.bank:
         ov,okey,oconst=problem.dual_upper({4:F(1)},lay,pr);require(key==okey and cc==oconst,'Existing source objective identity');old_dual_used.add(key)
         if ov<=incumbent:mark('six_known_dual_bounded',(lay,pr),ov/scale);continue
        for c441 in range(5):
         counts['seven_seen']+=1;sec7=tuple(a+int(c==c441)for a,(c,k)in zip(sec,product(range(5),repeat=2)))
         seven=head.objective(records['seven'],BB,tuple(zip(first,sec7)),cor,True);sevenlines=sixlines+(seven,);ok,v,_=bounded(sevenlines)
         if ok:mark('seven_bounded',(lay,pr,c441),v);continue
         for r735,s735,add735 in [(rr,ss,tuple(int(j.ROOT[c]==rr and k==ss)for c,k in product(range(5),repeat=2)))for rr,ss in product(range(2),range(5))]:
          counts['eight_seen']+=1;sec8=tuple(a+b for a,b in zip(sec7,add735));new=(c441,r735,s735)
          eight=head.objective(records['eight'],BB,tuple(zip(first,sec8)),cor,True);ok,v,at=bounded(sevenlines+(eight,))
          if ok:mark('eight_bounded',(lay,pr,new),v);continue
          if (lay,pr,new)in seed_bounds and seed_bounds[lay,pr,new]<=incumbent:mark('seed_bounded',(lay,pr,new),seed_bounds[lay,pr,new]/scale);continue
          counts['lp_remaining']+=1;remaining.append({'layout':lay,'projection':pr,'projection441_735':new,'affine_upper':scale*v,'maximizing_late_coordinate':at});digest.update(repr(('lp',lay,pr,new,scale*v)).encode())

    two=sum(counts[k]for k in ('two_old_bounded','two_enhanced_bounded'));four=sum(counts[k]for k in ('four_old_bounded','four_enhanced_bounded'));sixsum=sum(counts[k]for k in ('six_old_bounded','six_enhanced_bounded','six_known_dual_bounded'))
    covered=25000*two+500*four+50*sixsum+10*counts['seven_bounded']+counts['eight_bounded']+counts['seed_bounded']+counts['lp_remaining']
    require(counts['layouts']==12500 and counts['two_seen']==125000 and counts['four_seen']==50*(counts['two_seen']-two) and counts['six_seen']==10*(counts['four_seen']-four) and counts['seven_seen']==5*(counts['six_seen']-sixsum) and counts['eight_seen']==10*(counts['seven_seen']-counts['seven_bounded']),'Every independent prefix partition accounted')
    require(covered==62500000*50==3125000000 and len(remaining)==counts['lp_remaining'],'Complete original-domain ledger with all50 independent new label choices')
    require(counts['lp_remaining']==0 and not remaining,'Every original choice already has a complete exact upper')
    require(len(old_dual_used)==24 and seedchecks==165300 and verify_count==600,'All50 seed duals,24 original duals and600 independent affine endpoints')
    encoded=problem.codec.encode_dual_bank(bank,inequality_count=6354,equality_count=18)
    require(problem.codec.decode_dual_bank(encoded,inequality_count=6354,equality_count=18)==bank,'Lossless existing exact dual codec')
    scan={'counts':counts,'covered_containing_choices':covered,'original_choice_count':62500000,'new_independent_choices_per_original':50,'maximum_pruned_bounds':max_pruned,'all_branch_decisions_sha256':digest.hexdigest(),'maximizing_certificate_branch':worst_seed,'existing256_duals_rechecked':sorted(old_dual_used),'existing256_column_checks':3306*len(old_dual_used),'seed_column_checks':seedchecks,'independent_fractional_affine_checks':verify_count}
    return second.encode({'schema':'erdos7-j-face-second-cofactor-survival-heads-v1','source_sha256':pins,'geometry':s256['geometry'],'source_mass':F(1,4),'survivor_mass':F(3,20),'model':problem.specification,'retained_positive7_labels':[21,35,63,105,147,245,441,735],'new_original_labels':[441,735],'removed_original_positive7_caps':{'441':F(1,490),'735':F(2,1225)},'complete_positive7_tail':remainder,'affine_four_old_labels':[25,27,75,81],'complete_zero7_affine_remainder':j.REMAINDERS[4],'complete_zero7_joint_remainder':j.REMAINDERS[4]-pair.CAP135-pair.CAP125,'complete_AP13_upper':incumbent,'previous_complete_AP13_upper':F(oldrow['adopted_upper']),'improvement_over_previous':F(oldrow['adopted_upper'])-incumbent,'results':[{'name':'AP13','index':'AP13','coefficients':{4:F(1)},'at_one':F(0),'complete_head_upper':incumbent,'adopted_upper':incumbent,'previous_adopted_upper':F(oldrow['adopted_upper']),'improvement_over_previous':F(oldrow['adopted_upper'])-incumbent,'scan':scan}],'seed_records':seed_records,'encoded_rational_duals':encoded,'distinct_dual_count':len(bank),'seed_rational_column_checks':seedchecks,'existing256_rational_column_checks':3306*len(old_dual_used),'rational_column_checks':seedchecks+3306*len(old_dual_used),'transition_checks':transition_count,'independent_fractional_affine_checks':verify_count,'total_containing_choices':covered,'scope':'Complete original AP13 positive-part function on both entire actual saturated J faces. Independent original441/735 labels enlarge each of62500000 original choices to50 completions; all3125000000 choices, one actual raw source and survivor, the full shared late interval, and every old/positive-seven exponent tail remain. The unchanged3306-variable model supplies50 checked original-controller seed duals and24 rechecked256 source duals. Four-old-label integer-convex affine bounds and exact lower-envelope crossings cover all other branches. No actual attainment, off-face extension, complete52-cost comparison, Lean verification or unrestricted Erdos7 result is asserted.'})

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[1])
    parser.add_argument('--check',action='store_true')
    parser.add_argument('--proposal',type=Path)
    args=parser.parse_args()
    io=module('second_cofactor_io',args.base/'certificate_io.py')
    codec=module('second_cofactor_codec',args.base/'frontier/retained135_heavy_comparison.py')
    if args.proposal:
        require(not args.check,'Choose proposal publication or independent stored check')
        proposal=json.loads(io.read_artifact_bytes(args.proposal))
        rawbank=codec.decode_dual_bank(proposal['encoded_rational_duals'],inequality_count=6354,equality_count=18)
        row=next(r for r in proposal['results']if r['name']=='AP13')
        keys={r['dual_key']for r in row['branches']}
        bank={key:rawbank[key]for key in sorted(keys)}
        result=calculate(args.base,bank)
        io.write_certificate_text(args.base/CERTIFICATE,json.dumps(result,indent=2)+'\n')
    else:
        stored=json.loads(io.read_artifact_bytes(args.base/CERTIFICATE))
        bank=codec.decode_dual_bank(stored['encoded_rational_duals'],inequality_count=6354,equality_count=18)
        require(calculate(args.base,bank)==stored,'Every complete AP13 source field recomputes exactly')
    print('PASS: complete AP13;3125000000 original containing choices;50 seed and24 prior duals;244644 exact columns;600 independent affine endpoints;all tails.')

if __name__=='__main__':
    try:main()
    except (ValueError,ArithmeticError,OSError,KeyError,TypeError,json.JSONDecodeError) as error:
        print('FAIL: '+str(error),file=sys.stderr);raise SystemExit(1)
