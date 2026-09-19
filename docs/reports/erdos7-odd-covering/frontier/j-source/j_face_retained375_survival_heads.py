#!/usr/bin/env python3
"""Complete original J H4 with375 jointly retained and all eight seven projections."""
import argparse
import importlib.util
import json
import sys
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from math import lcm
from types import SimpleNamespace
from hashlib import sha256
sys.dont_write_bytecode=True
CERTIFICATE='certificates/source_norms/j-source/j_face_retained375_survival_heads.json'
PINS={'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232', 'frontier/j-source/j_face_coupled_seven_heads.py': '740d2656fc47a056c4f8ea2ca13e024784b96794ac364b21a91c89024cfc9587', 'frontier/j-source/j_face_joint_selected_heads.py': '4b244d4008d7cfe0025888192b8ed8a412a8f51509133d0b04208bcd6b47ad2c', 'frontier/j-source/j_face_retained135125_heads.py': '9af138e632fc8d9ec4f8be253e01fbbedd004ba378b1b89212bf2def557ea2f8', 'frontier/transport/second_depth_seven_comparison.py': 'e04a9cfb22cdb4c3f3ffda097b7975facc253c21840873ef527e5a601f028bfe', 'frontier/j-source/j_face_second_depth_retained_heads.py': '68aa156b9b1dae28a0f8e3fb728f67fd206b626db750429b7d97500aea7724c2', 'certificates/source_norms/j-source/j_face_joint_selected_heads.json': '434cd2865b3a61e19ecba395787420bc45d5c4b1da6a6831e93675109ef07a97', 'certificates/source_norms/j-source/j_face_retained135125_heads.json': '4a8eb666d29a6d56c8e33100d283e192d52dba526ecae4e5c631ce83e88bdd86', 'certificates/source_norms/j-source/j_face_second_depth_retained_heads.json': '6f8e8a51ba0a93a43e92d93ae78ed3bdc12130e45bf65ada8a42b961113365c3', 'frontier/j-source/j_face_second_cofactor_survival_heads.py': '08716687e87dec28abb26decabad8247a209f2163a78c2d1f537426295de23bb', 'certificates/source_norms/j-source/j_face_second_cofactor_survival_heads.json': '25ec9b985f8efe62f43651bf03f916ab4879874c244a1ff4a2b13281bd4c4e7b', 'profile-notes/j-source/280-second-depth-cofactors-sharpen-the-complete-j-survival-hinge.md': '0a436f77d9679c4b877782642ee808653668164a43f57a83f54922f8b52b5e75', 'frontier/j-source/j_face_triple_second_depth_heads.py': 'c6c1f5dc4a06a9a16bb6291abaea28e08a3c7fb776edfff55e226bb723954f3a', 'certificates/source_norms/j-source/j_face_triple_second_depth_heads.json': '28efda83f17bffed4a75f49448820c118ee300a4515f807aa4fd677bc3ea8743', 'profile-notes/j-source/264-seven-retained-states-and-two-seven-depths-control-complete-j-heads.md': '7eadaa5f36996f8afc2af013fba2d83d27b7e581ebf667507f67483d5169550a'}

def require(ok,message):
    if not ok:raise ValueError(message)

def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    require(spec is not None and spec.loader is not None,'Loadable original source')
    value=importlib.util.module_from_spec(spec);spec.loader.exec_module(value);return value

def complete_old_pruning(B,bank,fixed):
    pins=dict(PINS)
    def load(n):
     path=B/(n+'.py');require(sha256(path.read_bytes()).hexdigest()==PINS[n+'.py'],'Pinned original program '+n)
     sp=importlib.util.spec_from_file_location('cofactor_'+n.replace('/','_'),path);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m);return m
    io=load('certificate_io');j=load('frontier/j-source/j_face_coupled_seven_heads');core=load('frontier/j-source/j_face_joint_selected_heads');pair=load('frontier/j-source/j_face_retained135125_heads');depth=load('frontier/transport/second_depth_seven_comparison');second=load('frontier/j-source/j_face_second_depth_retained_heads')
    def read(n):
     path='certificates/source_norms/j-source/'+n+'.json';raw=io.read_artifact_bytes(B/path);require(sha256(raw).hexdigest()==PINS[path],'Pinned original certificate '+n)
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
    old_complete_bound=incumbent
    incumbent=fixed
    require(0<incumbent<old_complete_bound,'Fixed lower scheduling benchmark, not a proved source bound')
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
          counts['lp_remaining']+=1
          available=[scale*v,old_complete_bound]
          if (lay,pr,new)in seed_bounds:available.append(seed_bounds[lay,pr,new])
          remaining.append({'layout':lay,'projection':pr,'projection441_735':new,'affine_upper':scale*v,'strongest_available_old_upper':min(available),'maximizing_late_coordinate':at})
          digest.update(repr(('lp',lay,pr,new,scale*v)).encode())

    two=sum(counts[k]for k in ('two_old_bounded','two_enhanced_bounded'));four=sum(counts[k]for k in ('four_old_bounded','four_enhanced_bounded'));sixsum=sum(counts[k]for k in ('six_old_bounded','six_enhanced_bounded','six_known_dual_bounded'))
    covered=25000*two+500*four+50*sixsum+10*counts['seven_bounded']+counts['eight_bounded']+counts['seed_bounded']+counts['lp_remaining']
    require(counts['layouts']==12500 and counts['two_seen']==125000 and counts['four_seen']==50*(counts['two_seen']-two) and counts['six_seen']==10*(counts['four_seen']-four) and counts['seven_seen']==5*(counts['six_seen']-sixsum) and counts['eight_seen']==10*(counts['seven_seen']-counts['seven_bounded']),'Every independent prefix partition accounted')
    require(covered==62500000*50==3125000000 and len(remaining)==counts['lp_remaining'],'Complete original-domain ledger with all50 independent new label choices')
    require(seedchecks==165300 and verify_count==600,'All50 existing seed duals and600 independent affine endpoints rechecked')
    return second.encode({'schema':'erdos7-j-retained375-complete-old-prefix-ledger-v1','source_sha256':pins,
        'scope':'Complete inherited280 prefix bounds and exact available duals at a fixed375 seed upper. Every original choice lies in a bounded prefix or in a listed remaining eight-projection leaf. The latter are checked by the complete375 model before a final source bound is asserted.',
        'fixed_candidate_H4_benchmark':incumbent,'old_complete280_H4_upper':old_complete_bound,
        'geometry':s256['geometry'],'source_mass':F(1,4),'survivor_mass':F(3,20),'old_source_model':problem.specification,
        'counts':counts,'covered_containing_choices':covered,'total_original_choices':62500000,'new_independent_choices_per_original':50,
        'remaining_eight_projection_leaves':remaining,'maximum_pruned_bounds':max_pruned,
        'maximum_unresolved_affine_bound':max((r['affine_upper']for r in remaining),default=F(0)),
        'maximum_unresolved_old_available_bound':max((r['strongest_available_old_upper']for r in remaining),default=F(0)),
        'all_branch_decisions_sha256':digest.hexdigest(),'existing256_duals_rechecked':sorted(old_dual_used),
        'existing256_column_checks':3306*len(old_dual_used),'existing280_seed_column_checks':seedchecks,
        'independent_fractional_affine_checks':verify_count,'new_LP_solves':0})

def make_extended_model(B):
    def load(n):return module('retained375_'+n.replace('/','_'),B/(n+'.py'))
    io=load('certificate_io');triple=load('frontier/j-source/j_face_triple_second_depth_heads');core=load('frontier/j-source/j_face_joint_selected_heads')
    j=load('frontier/j-source/j_face_coupled_seven_heads');pair=load('frontier/j-source/j_face_retained135125_heads');depth=load('frontier/transport/second_depth_seven_comparison');codec=load('frontier/transport/retained135_heavy_comparison')
    read=lambda n:json.loads(io.read_artifact_bytes(B/'certificates/source_norms'/(n+'.json')),object_pairs_hook=core.unique)
    p244,p251,p256,p264=(read('j-source/j_face_joint_selected_heads'), read('j-source/j_face_retained135125_heads'), read('j-source/j_face_second_depth_retained_heads'), read('j-source/j_face_triple_second_depth_heads'))
    problem=triple.TripleSecondDepthJHead(B,j,core,pair,depth,p244,p251,p256);old=problem.lp
    require(problem.specification==p264['model']and old.nvars==6531 and len(old.rows)==11211 and len(old.equalities)==19,'Every original264 actual-source constraint remains')
    pre,absolute,desc,w=j.source_tables(j.LO);fw=[v for row in w for v in row];cap=F(1,375)
    U,V,L,N=6531,9731,12931,12941
    lp=SimpleNamespace(nvars=N,rows=[dict(row)for row in old.rows],rhs=list(old.rhs),equalities=[dict(row)for row in old.equalities],erhs=list(old.erhs),unit_rows=list(old.unit_rows))
    def add(row,rhs=F(0)):
     lp.rows.append({c:a for c,a in row.items()if a});lp.rhs.append(rhs)
    def combine(*parts):
     out={}
     for scale,part in parts:
      for col,a in part.items():out[col]=out.get(col,F(0))+scale*a
     return {col:a for col,a in out.items()if a}
    def original(state,k,raw):
     if state:return {(triple.U if raw else triple.V)+400*(state-1)+k:F(1)}
     return {**{(0 if raw else 425)+k:F(1)},**{(triple.U if raw else triple.V)+400*(st-1)+k:F(-1)for st in range(1,8)}}
    for state,k in product(range(8),range(400)):
     raw,sur=original(state,k,True),original(state,k,False);weight=fw[k//16];a={U+400*state+k:F(1)};b={V+400*state+k:F(1)}
     add(combine((1,a),(-1,raw)));add(combine((1,b),(-1,sur)))
     add(combine((1,b),(-weight,a)));add(combine((1,sur),(-1,b),(-weight,raw),(weight,a)))
    profile=tuple(range(L,N));lp.equalities.append({col:F(1)for col in profile});lp.erhs.append(F(1))
    for i in range(25):
     c,slot=divmod(i,5);row={U+400*state+16*i+mask:F(1)for state,mask in product(range(8),range(16))}
     row[L+5*j.ROOT[c]+slot]=-desc[c][slot]/125;add(row)
    add({V+400*state+k:F(1)for state,k in product(range(8),range(400))},cap)
    crt=[]
    for bit,label in enumerate((25,27,75,81)):
     row={U+400*state+16*i+mask:F(1)for state,i,mask in product(range(8),range(25),range(16))if mask>>bit&1}
     bound=F(1,lcm(375,label));add(row,bound);crt.append({'label':label,'lcm':lcm(375,label),'raw_upper':bound})
    for bit,label in enumerate((135,125,225)):
     row={U+400*state+k:F(1)for state,k in product(range(8),range(400))if state>>bit&1}
     bound=F(1,lcm(375,label));add(row,bound);crt.append({'label':label,'lcm':lcm(375,label),'raw_upper':bound})
    for col in range(6531,N):lp.unit_rows.append(len(lp.rows));add({col:F(1)},F(1))
    require(lp.rows[:11211]==old.rows and lp.rhs[:11211]==old.rhs and lp.equalities[:19]==old.equalities and lp.erhs[:19]==old.erhs,'Every264 original row, bound and equality preserved verbatim')
    require(len(lp.rows)==30454 and len(lp.equalities)==20 and len(lp.unit_rows)==N,'Exact extension dimension12941/30454/20')
    lp.columns=[[]for _ in range(N)];lp.eqcolumns=[[]for _ in range(N)]
    for row,record in enumerate(lp.rows):
     for col,a in record.items():lp.columns[col].append((row,a))
    for row,record in enumerate(lp.equalities):
     for col,a in record.items():lp.eqcolumns[col].append((row,a))
    lp.checker=codec.IntegerDualChecker(lp);lp.check_dual=lp.checker.check
    enc=triple.encode
    modelhash=sha256(json.dumps(enc([lp.rows,lp.rhs,lp.equalities,lp.erhs]),sort_keys=True,separators=(',',':')).encode()).hexdigest()
    specification={'variables':N,'inequalities':len(lp.rows),'equalities':len(lp.equalities),'rows_sha256':modelhash,
                   'preserved_original_rows':11211,'preserved_original_equalities':19,'new_raw_intersection_variables':3200,
                   'new_survivor_intersection_variables':3200,'independent_profile_coordinates':10}
    return {'lp':lp,'model':specification,'reference':problem,'j':j,'depth':depth,'triple':triple,'codec':codec,'io':io,'raw_CRT_caps':crt}


def complete_objective(data,lay,pr,new):
    problem,j,depth,triple=data['reference'],data['j'],data['depth'],data['triple']
    U,V,L,N=6531,9731,12931,12941
    hh=problem.head.bridge.head_load(lay);r,s,c63,r105,s105,r147,s245=pr;c441,r735,s735=new
    obj=[F(0)]*N
    for i,b in enumerate(hh):
        cellroot,slot=divmod(i,5)
        m=int(j.ROOT[cellroot]==r)+int(slot==s)+int(cellroot==c63)+int(j.ROOT[cellroot]==r105 and slot==s105)
        e=int(j.ROOT[cellroot]==r147)+int(slot==s245)+int(cellroot==c441)+int(j.ROOT[cellroot]==r735 and slot==s735)
        f=lambda v:depth.seven_increment(4,v,m,e)
        require(f(4)==f(5)==F(6,35)*(1+m)+F(6,245)*(1+e)+F(1,245)
                and all(f(v+1)>=f(v)for v in range(1,4)),
                'The raw kernel is nondecreasing at every transition and exactly constant for all v>=4')
        for mask in range(16):
            cell=16*i+mask;v=b+mask.bit_count();obj[cell]=f(v);obj[425+cell]=F(max(v-4,0))
            for state in range(1,8):
                n=state.bit_count();obj[triple.U+400*(state-1)+cell]=f(v+n)-f(v)
                obj[triple.V+400*(state-1)+cell]=F(max(v+n-4,0)-max(v-4,0))
            for state in range(8):
                vv=v+state.bit_count();obj[U+400*state+cell]=f(vv+1)-f(vv)
                obj[V+400*state+cell]=F(max(vv+1-4,0)-max(vv-4,0))
    require(min(obj)>=0 and all(v==0 for v in obj[L:]),'Exact actual raw/survivor375 objective and zero profile coefficients')
    return obj,F(5071,405000)+F(13,490)


def calculate(B,bank,seed):
    data=make_extended_model(B);io,codec,j=data['io'],data['codec'],data['j'];encode=data['triple'].encode
    oldpath='certificates/source_norms/j-source/j_face_second_cofactor_survival_heads.json'
    old=json.loads(io.read_artifact_bytes(B/oldpath))
    oldbank=codec.decode_dual_bank(old['encoded_rational_duals'],inequality_count=6354,equality_count=18)
    layouts=set(j.layouts());projections=set(product(range(2),range(5),range(5),range(2),range(5),range(2),range(5)));newlabels=set(product(range(5),range(2),range(5)))
    used=set()
    def evaluate(lay,pr,new):
        require(lay in layouts and pr in projections and new in newlabels,'Original independently chosen containing labels')
        obj,const=complete_objective(data,lay,pr,new)
        key=sha256(json.dumps([data['model']['rows_sha256'],encode(obj)],separators=(',',':')).encode()).hexdigest()
        require(key in bank,'An exact375 dual covers every unresolved original leaf')
        upper=data['lp'].checker.check(obj,bank[key])+const;used.add(key)
        return upper,key,const
    require(set(seed)=={'layout','projection','projection441_735'},'A single explicit original seed without an optimality assumption')
    candidate,seedkey,constant=evaluate(tuple(seed['layout']),tuple(seed['projection']),tuple(seed['projection441_735']))
    require(0<candidate<F(old['complete_AP13_upper']),'The fixed seed supplies a strict candidate for full-domain verification')
    ledger=complete_old_pruning(B,oldbank,candidate)
    require(F(ledger['old_complete280_H4_upper'])==F(old['complete_AP13_upper']),'Exact current complete280 baseline')
    rows=[]
    for leaf in ledger['remaining_eight_projection_leaves']:
        lay,pr,new=tuple(leaf['layout']),tuple(leaf['projection']),tuple(leaf['projection441_735'])
        upper,key,const=evaluate(lay,pr,new);prior=F(leaf['strongest_available_old_upper']);adopted=min(upper,prior)
        rows.append({'layout':lay,'projection':pr,'projection441_735':new,'complete375_upper':upper,
                     'previous_available_upper':prior,'adopted_upper':adopted,'complete_tail_constant':const,'dual_key':key})
    final=max([candidate]+[r['adopted_upper']for r in rows]);previous=F(old['complete_AP13_upper'])
    require(0<final<previous and used==set(bank),'Every retained dual is used and all original choices have a strict complete-source improvement')
    pins=dict(ledger['source_sha256'])
    for path,pin in PINS.items():
        require(path not in pins or pins[path]==pin,'Consistent mathematical source closure '+path);pins[path]=pin
    for path,pin in pins.items():require(sha256(io.read_artifact_bytes(B/path)).hexdigest()==pin,'Stable final mathematical source '+path)
    encoded=codec.encode_dual_bank({key:bank[key]for key in sorted(used)},inequality_count=30454,equality_count=20)
    require(codec.decode_dual_bank(encoded,inequality_count=30454,equality_count=20)==bank,'Canonical lossless exact dual bank')
    return encode({'schema':'erdos7-j-face-retained375-survival-heads-v1','source_sha256':pins,'geometry':old['geometry'],
        'source_mass':F(1,4),'survivor_mass':F(3,20),'original264_model':data['reference'].specification,'model':data['model'],
        'retained_old_labels':[25,27,75,81,135,125,225,375],'retained_positive7_labels':[21,35,63,105,147,245,441,735],
        'new_label':375,'new_label_survivor_cap':F(1,375),'raw_CRT_caps':data['raw_CRT_caps'],
        'complete_old_tail_before375':F(6151,405000),'complete_old_tail':F(5071,405000),
        'complete_positive7_tail':F(13,490),'complete_tail_constant':constant,'seed':seed,'seed_dual_key':seedkey,
        'fixed_pruning_benchmark':candidate,'prefix_ledger':ledger,'residual_leaf_results':rows,
        'residual_leaf_count':len(rows),'complete_AP13_upper':final,'previous_complete_AP13_upper':previous,
        'improvement_over_previous':previous-final,'maximizing_certificate_branch':max(rows,key=lambda r:r['adopted_upper']),
        'encoded_rational_duals':encoded,'distinct_dual_count':len(used),'rational_column_checks':12941*len(used),
        'total_containing_choices':ledger['covered_containing_choices'],
        'scope':'Complete original H4/AP13 bound on both entire actual saturated J faces. Every3.125 billion independent original containing choice lies in a complete280 prefix bound or an exactly checked residual375 leaf. The original264 rows and seven old states remain; the independent375 root-slot profile and raw/survivor intersections are added with both occupied and complement density constraints and every original LCM cap. The375 retained event removes exactly its own1/375 tail payment, leaving5071/405000 and the full13/490 positive-seven tail. The common late interval, every exponent/cofactor depth, marked deletions and actual measure are unchanged. The final bound is the maximum of the fixed seed threshold and each residual leaf minimum of a complete new and old bound. Relaxed certificate maxima are not actual source attainment. No off-face extension, global join, complete52-cost comparison, Lean verification or unrestricted Erdos7 conclusion.'})


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    modes=parser.add_mutually_exclusive_group();modes.add_argument('--write',action='store_true');modes.add_argument('--check',action='store_true')
    parser.add_argument('--proposal',type=Path);args=parser.parse_args()
    require(args.proposal is None or args.write,'Only the writer takes a rational proposal')
    require(not args.write or args.proposal is not None,'Writer requires full exact375 leaf certificates')
    io=module('retained375_read',args.base/'certificate_io.py');codec=module('retained375_codec',args.base/'frontier/transport/retained135_heavy_comparison.py')
    proposed=json.loads(io.read_artifact_bytes(args.proposal if args.write else args.base/CERTIFICATE))
    bank=codec.decode_dual_bank(proposed['encoded_rational_duals'],inequality_count=30454,equality_count=20)
    result=calculate(args.base,bank,proposed['seed'])
    if args.write:io.write_certificate_text(args.base/CERTIFICATE,json.dumps(result,indent=2)+'\n')
    else:require(result==proposed,'Every complete375 source field and original-domain prefix ledger recomputes exactly')
    print('PASS complete375 H4;3125000000 original choices;'+str(result['residual_leaf_count'])+' exact residual leaves;upper '+str(float(F(result['complete_AP13_upper']))),flush=True)

if __name__=='__main__':
    try:main()
    except(ValueError,ArithmeticError,OSError,KeyError,TypeError,json.JSONDecodeError)as e:
        print('FAIL: '+str(e),file=sys.stderr);raise SystemExit(1)
