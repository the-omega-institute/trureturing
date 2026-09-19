#!/usr/bin/env python3
"""Complete original AP11-0 source bound retaining independent375."""
import argparse,importlib.util,json,sys
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from pathlib import Path
sys.dont_write_bytecode=True
CERTIFICATE='certificates/source_norms/j-geometry/j_face_retained375_ap11_heads.json'
PINS = {'frontier/j-geometry/j_face_retained375_survival_heads.py': '4a873f67f2ea4040555873a2777dcb8780c35816e5168704eeca5ac8cce0748e', 'certificates/source_norms/j-geometry/j_face_retained375_survival_heads.json': 'e92c74eab962d2b58235c2de020222c135bc1844447791b96269ea9197f00e4f', 'profile-notes/257-320/288-retaining375-strengthens-the-complete-j-survival-hinge.md': 'acc7d5308c0d8e9bf513623b98e338ddc2cb5e4da4891602dc942b5db7e7701d', 'frontier/j-geometry/j_face_second_depth_survival_heads.py': 'b4cccdc886a094bbda8967343af8b28726ed6c1a004f5f7e43c46fdcd6c7a4c7', 'certificates/source_norms/j-geometry/j_face_second_depth_survival_heads.json': '2d3f18c0325b2518a8c56207341a092c9b79a4d9df0ad5fbd92734545bdb8a6b', 'profile-notes/257-320/266-two-original-ap11-blocks-use-the-complete-second-depth-interface.md': 'c4552881dbe56109092b7a721e512ef642dc68853cbc25456db176b3f853e00a'}

def require(ok,message):
    if not ok:raise ValueError(message)

def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    require(spec is not None and spec.loader is not None,'Loadable existing mathematical provider')
    value=importlib.util.module_from_spec(spec);spec.loader.exec_module(value);return value

def inputs(B):
    io=module('retained375_ap11_io',B/'certificate_io.py')
    core=module('retained375_ap11_core',B/'frontier/j-geometry/j_face_joint_selected_heads.py')
    read=lambda n:json.loads(io.read_artifact_bytes(io.named_artifact(B/'certificates/source_norms', n+'.json')),object_pairs_hook=core.unique)
    p288=read('j_face_retained375_survival_heads');p266=read('j_face_second_depth_survival_heads')
    pins=dict(PINS)
    for source in (p288,p266):
        for path,pin in source['source_sha256'].items():
            require(path not in pins or pins[path]==pin,'Consistent mathematical source closure '+path);pins[path]=pin
    for path,pin in pins.items():require(sha256(io.read_artifact_bytes(B/path)).hexdigest()==pin,'Pinned mathematical source '+path)
    provider=module('retained375_ap11_model288',B/'frontier/j-geometry/j_face_retained375_survival_heads.py')
    data=provider.make_extended_model(B);problem=data['reference']
    require(data['model']==p288['model'] and data['model']['variables']==12941
            and data['model']['inequalities']==30454 and data['model']['equalities']==20,
            'Exactly the complete288 extended375 model, preserving all264 rows')
    p264=read('j_face_triple_second_depth_heads')
    require(problem.specification==p264['model']==p288['original264_model']
            and p264['geometry']==p288['geometry']==p266['geometry']
            and all(F(s['source_mass'])==F(1,4) and F(s['survivor_mass'])==F(3,20)for s in(p264,p266,p288)),
            'One actual source and both entire saturated J faces')
    second=module('retained375_ap11_second',B/'frontier/j-geometry/j_face_second_depth_retained_heads.py')
    codec=data['codec'];bank266=codec.decode_dual_bank(p266['encoded_rational_duals'],inequality_count=6354,equality_count=18)
    for key,value in bank266.items():
        require(key not in problem.previous_depth.bank or value==problem.previous_depth.bank[key],'Consistent original266 source dual')
        problem.previous_depth.bank[key]=value
    data.update(p288=p288,p266=p266,p264=p264,second=second,pins=pins)
    return data

def calculate(B,bank):
    data=inputs(B)
    lp,problem,j,depth,triple,codec,io,second=(data[k]for k in('lp','reference','j','depth','triple','codec','io','second'))
    p264,p266,p288,pins=(data[k]for k in('p264','p266','p288','pins'))
    enc=triple.encode;N,U,V,L=12941,6531,9731,12931;index=0
    modelhash=data['model']['rows_sha256'];newtail=F(5071,405000);z8=F(13,490)
    require(F(p288['complete_old_tail'])==newtail and F(p288['complete_positive7_tail'])==z8
            and F(p288['new_label_survivor_cap'])==F(1,375),'The exact375 source and full complementary tails')
    src=next(r for r in p266['results']if r['block']==index)
    co={int(t):F(a)for t,a in src['scan']['coefficients'].items()};late=sum(co.values());prior_complete=F(src['adopted_upper'])
    require(F(src['at_one'])==0 and co=={int(t):F(a)for t,a in src['coefficients'].items()}
            and co=={1:F(1355,263538),2:F(20425,263538),3:F(25,363),5:F(28,33)} and late==1,
            'Exactly the original AP11-0 whole function, including H1 and its full late slope')
    head=problem.head;oldrecord=head.prepare(co);old=oldrecord;six=problem.prepare_six(old)
    scale=old['factor']/j.TOTAL;weights=sorted(set(head.w));pairs=list(product(range(5),range(5)))
    ints=old['primitive_coefficients']
    require(all(old['factor']*ints[t]==co[t]for t in co),'Exact primitive scaling of the unchanged original cost')

    # Shared scalar kernels preserve the complete function, including H1.
    hs={v:sum(a*max(v-t,0)for t,a in co.items())for v in range(1,15)}
    gs={(m,e):{v:sum(a*depth.seven_increment(t,v,m,e)for t,a in co.items())for v in range(1,15)}for m,e in pairs}
    transition_count=0
    for t,w,m,e in product(co,weights,range(5),range(5)):
     vals=[F(w,5)*max(v-t,0)+depth.seven_increment(t,v,m,e)for v in range(1,15)]
     diffs=[b-a for a,b in zip(vals,vals[1:])]
     require(min(diffs)>=0 and all(a<=b for a,b in zip(diffs,diffs[1:]))
             and all(a==F(w,5)for a in diffs[t-1:]),'All transitions and exact linear continuation of each original hinge')
     rawconst=F(6,35)*(1+m)+F(6,245)*(1+e)+F(1,245)
     require(depth.seven_increment(t,t,m,e)==depth.seven_increment(t,t+1,m,e)==rawconst,
             'Algebraic constant raw branch for every v>=t, no remaining-load cutoff')
     transition_count+=len(diffs)
    require(all(gs[p][1]==sum(co[t]*depth.seven_increment(t,1,*p)for t in co)for p in pairs),
            'No threshold coefficient dropped')
    def complete_objective(lay,pr,new):
     hh=head.bridge.head_load(lay);r,s,c63,r105,s105,r147,s245=pr;c441,r735,s735=new
     require(min(hh)>=1 and max(hh)<=6,'Original shallow load range, including exact H1 linearity')
     out=[F(0)]*N
     for i,b in enumerate(hh):
      c,slot=divmod(i,5)
      m=int(j.ROOT[c]==r)+int(slot==s)+int(c==c63)+int(j.ROOT[c]==r105 and slot==s105)
      e=int(j.ROOT[c]==r147)+int(slot==s245)+int(c==c441)+int(j.ROOT[c]==r735 and slot==s735)
      gg=gs[m,e]
      for mask in range(16):
       k=16*i+mask;v=b+mask.bit_count();out[k]=gg[v];out[425+k]=hs[v]
       for state in range(1,8):
        n=state.bit_count();out[triple.U+400*(state-1)+k]=gg[v+n]-gg[v]
        out[triple.V+400*(state-1)+k]=hs[v+n]-hs[v]
       for state in range(8):
        x=v+state.bit_count();out[U+400*state+k]=gg[x+1]-gg[x]
        out[V+400*state+k]=hs[x+1]-hs[x]
     require(min(out)>=0 and all(v==0 for v in out[L:]),'Nonnegative exact complete actual-source objective')
     return out,late*(newtail+z8)

    def direct_check(obj,dual,raw):
     prices={int(k):F(v)for k,v in dual['nonzero_inequality_duals'].items()}
     eq=list(map(F,dual['equality_duals']));acc=[-a for a in obj];direct=F(0)
     require(len(eq)==20 and all(0<=r<30454 and v>=0 for r,v in prices.items()),'Exact dual signs and dimensions')
     for row,value in prices.items():
      direct+=value*lp.rhs[row]
      for col,a in lp.rows[row].items():acc[col]+=value*a
     for row,rhs,value in zip(lp.equalities,lp.erhs,eq):
      direct+=value*rhs
      for col,a in row.items():acc[col]+=value*a
     require(min(acc)>=0 and direct==raw==F(dual['raw_objective_upper']),
             'Independent Fraction check of all12941 exact dual columns')

    seed=src['scan']['maximizing_certificate_branch']
    seed_layout=tuple(seed['layout']);seed_projection=tuple(seed['projection21_35_63_105_147_245'])
    layouts=set(j.layouts());projections=set(product(range(2),range(5),range(5),range(2),range(5),range(2),range(5)))
    newlabels=set(product(range(5),range(2),range(5)))
    require(seed_layout in layouts and seed_projection in projections,'The published266 original seed is a legal containing choice')
    used=set();checked={}
    def evaluate(lay,pr,new):
     require(lay in layouts and pr in projections and new in newlabels,'Every containing label remains independent and in its original domain')
     obj,const=complete_objective(lay,pr,new)
     key=sha256(json.dumps([modelhash,enc(obj)],separators=(',',':')).encode()).hexdigest()
     require(key in bank,'Exact375 dual supplied for the original AP11 objective')
     if key not in checked:
      checked[key]=lp.checker.check(obj,bank[key]);direct_check(obj,bank[key],checked[key])
     used.add(key)
     return checked[key]+const,key,const
    seed_bounds={};seedkeys=set();seed_rows=[]
    for new in product(range(5),range(2),range(5)):
     upper,key,const=evaluate(seed_layout,seed_projection,new)
     seed_bounds[seed_layout,seed_projection,new]=upper;seedkeys.add(key)
     seed_rows.append({'projection441_735':new,'complete375_upper':upper,'dual_key':key,'complete_tail_constant':const})
    incumbent=max(seed_bounds.values())
    require(len(seed_bounds)==len(seedkeys)==50 and 0<incumbent<prior_complete,
            'All50 completions define one fixed candidate before the full-domain scan, without assuming seed optimality')
    problem.bank=codec.decode_dual_bank(p264['encoded_rational_duals'],inequality_count=11211,equality_count=19)
    # The strengthened affine bound retains four original old labels for every
    # original hinge, with the exact same old CRT telescoping inequalities.
    raw={}
    for w,p in product(weights,pairs):
     raw[w,*p]=[0]+[j.integer(j.SCALE*sum(a*(F(w,5)*max(v-t,0)+depth.seven_increment(t,v,*p))for t,a in ints.items()))for v in range(1,11)]
     for v in range(1,7):
      inc=[raw[w,*p][v+k+1]-raw[w,*p][v+k]for k in range(4)]
      require(min(inc)>=0 and all(a<=b for a,b in zip(inc,inc[1:])),
              'Four-step integer-convex telescoping for the whole original AP11 function')
    def prepared(tail):
     tab={(w,p):[0]+[raw[w,*p][v]for v in range(1,7)]for w,p in product(weights,pairs)}
     inc={(i,k):{(w,p):[0]+[raw[w,*p][v+k+1]-raw[w,*p][v+k]for v in range(1,7)]for w,p in product(weights,pairs)}for i in range(1,5)for k in range(i)}
     const=j.integer(j.TOTAL*sum(ints.values())*(j.REMAINDERS[4]+tail))
     return {**old,'highest_selected_label':4,'head':tab,'increments':inc,'constants':(const,const)}
    records={'two':prepared(j.Z2),'four':prepared(j.Z4),'six':prepared(second.Z6),
             'seven':prepared(second.Z6-F(1,490)),'eight':prepared(z8)}
    require(second.Z6-F(1,490)-F(2,1225)==z8,'Only the441/735 assigned payments removed from the infinite positive-seven tail')
    def rational(lay,first,sec,tail,theta):
     BB=head.bridge.head_load(lay);p,caps,e,w=j.source_tables(theta);flatw=[v for row in w for v in row]
     def f(i,v):return sum(a*(flatw[i]*max(v-t,0)+depth.seven_increment(t,v,first[i],sec[i]))for t,a in co.items())
     z=[f(i,v)for i,v in enumerate(BB)];value=j.raw_source_lp(z,theta)
     def op(a,step):
      if step in (2,4):return max(sum(p[c][s]*a[5*c+s]for s in range(5))for c in range(5))/(27 if step==2 else 81)
      if step==1:return max(sum(e[c][s]*a[5*c+s]for c in range(5))for s in range(5))/25
      return max(sum(e[c][s]*a[5*c+s]for c in range(5)if j.ROOT[c]==rr)for rr,s in product(range(2),range(5)))/25
     for step in range(1,5):
      levels=[[f(i,v+k+1)-f(i,v+k)for i,v in enumerate(BB)]for k in range(step)]
      hi=levels[-1];choices=[op(hi,step)]
      if step in (2,3):
       lo=levels[-2];choices.append(op(lo,step)+max(h-l for h,l in zip(hi,lo))/675)
      if step==4:
       lo,mid=levels[1:3]
       choices.extend([op(lo,step)+max(max(2*(m-l),h-l)for l,m,h in zip(lo,mid,hi))/2025,
                       op(mid,step)+max(h-m for h,m in zip(hi,mid))/2025])
      value+=min(choices)
     HH=[sum(a*max(v-t,0)for t,a in co.items())for v in BB]
     return value-sum(j.deletion_correction(HH))+late*(j.REMAINDERS[4]+tail)
    verify_count=head.check_compiler(old)
    for lay,pr in [(seed_layout,seed_projection),((0,1,2,0,2,1,2),(0,1,2,1,3,0,4)),((1,3,2,1,2,3,2),(1,2,3,0,3,1,1))]:
     BB=head.bridge.head_load(lay);cor=head.correction(old,BB);r,s,c63,r105,s105,r147,s245=pr
     first=tuple(int(j.ROOT[c]==r)+int(k==s)+int(c==c63)+int(j.ROOT[c]==r105 and k==s105)for c,k in product(range(5),repeat=2))
     ex=tuple(int(j.ROOT[c]==r)+int(k==s)for c,k in product(range(5),repeat=2))
     sec=tuple(int(j.ROOT[c]==r147)+int(k==s245)for c,k in product(range(5),repeat=2))
     zero=(0,)*25
     for name,ff,ss,tail in [('two',ex,zero,j.Z2),('four',first,zero,j.Z4),('six',first,sec,second.Z6)]:
      aff=head.objective(records[name],BB,tuple(zip(ff,ss)),cor,True)
      for theta,x in ((j.LO,0),(j.HI,1)):
       require(scale*aff[x]==rational(lay,ff,ss,tail,theta),'Independent AP11 rational affine endpoint, stage'+name);verify_count+=1
     for c441,r735,s735 in product(range(5),range(2),range(5)):
      sec7=tuple(a+int(c==c441)for a,(c,k)in zip(sec,product(range(5),repeat=2)))
      sec8=tuple(a+int(j.ROOT[c]==r735 and k==s735)for a,(c,k)in zip(sec7,product(range(5),repeat=2)))
      for name,ss,tail in [('seven',sec7,second.Z6-F(1,490)),('eight',sec8,z8)]:
       aff=head.objective(records[name],BB,tuple(zip(first,ss)),cor,True)
       for theta,x in ((j.LO,0),(j.HI,1)):
        require(scale*aff[x]==rational(lay,first,ss,tail,theta),'Independent AP11 rational affine endpoint, stage'+name);verify_count+=1

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
        oo,cc=problem.objective(co,lay,pr);key=sha256(json.dumps([problem.specification['rows_sha256'],second.encode(oo)],separators=(',',':')).encode()).hexdigest()
        if key in problem.bank:
         ov,okey,oconst=problem.dual_upper(co,lay,pr);require(key==okey and cc==oconst,'Existing source objective identity');old_dual_used.add((264,key))
         if ov<=incumbent:mark('six_known_dual_bounded',(lay,pr),ov/scale);continue
        # Smaller source models retain their unchanged original objectives.
        prior_values=[]
        ov,okey=problem.prior_depth_upper(co,lay,pr)
        if ov is not None:old_dual_used.add((266,okey));prior_values.append(ov)
        ov,okey=problem.prior_upper(co,lay,prefix)
        if ov is not None:old_dual_used.add((251,okey));prior_values.append(ov)
        if prior_values and min(prior_values)<=incumbent:
         mark('six_known_dual_bounded',(lay,pr,'prior'),min(prior_values)/scale);continue
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
          available=[scale*v,prior_complete]
          if (lay,pr,new)in seed_bounds:available.append(seed_bounds[lay,pr,new])
          remaining.append({'layout':lay,'projection':pr,'projection441_735':new,'affine_upper':scale*v,'strongest_available_old_upper':min(available),'maximizing_late_coordinate':at})
          digest.update(repr(('lp',lay,pr,new,scale*v)).encode())


    two=sum(counts[k]for k in ('two_old_bounded','two_enhanced_bounded'))
    four=sum(counts[k]for k in ('four_old_bounded','four_enhanced_bounded'))
    sixsum=sum(counts[k]for k in ('six_old_bounded','six_enhanced_bounded','six_known_dual_bounded'))
    covered=25000*two+500*four+50*sixsum+10*counts['seven_bounded']+counts['eight_bounded']+counts['seed_bounded']+counts['lp_remaining']
    require(counts['layouts']==12500 and counts['two_seen']==125000
            and counts['four_seen']==50*(counts['two_seen']-two)
            and counts['six_seen']==10*(counts['four_seen']-four)
            and counts['seven_seen']==5*(counts['six_seen']-sixsum)
            and counts['eight_seen']==10*(counts['seven_seen']-counts['seven_bounded']),
            'Every independent prefix and all its child choices accounted')
    require(covered==3125000000 and len(remaining)==counts['lp_remaining'],
            'Complete original domain and its entire fixed-threshold residual leaf list')
    require(all(v<=incumbent for v in max_pruned.values()),'Every closed prefix certified at the same fixed exact threshold')
    checks={provider:sum(1 for p,key in old_dual_used if p==provider)for provider in (251,266,264)}
    ledger={'counts':counts,'covered_containing_choices':covered,'fixed_pruning_benchmark':incumbent,
     'remaining_eight_projection_leaves':remaining,'maximum_pruned_bounds':max_pruned,
     'all_branch_decisions_sha256':digest.hexdigest(),
     'existing_source_duals_rechecked':[{'source':p,'dual_key':key}for p,key in sorted(old_dual_used)],
     'existing_source_dual_counts':checks,'existing_source_column_checks':6531*checks[264]+3306*(checks[251]+checks[266]),
     'seed_column_checks':len(seedkeys)*N,'independent_direct_seed_column_checks':len(seedkeys)*N,
     'independent_fractional_affine_checks':verify_count,'infinite_bridge_transition_checks':transition_count}
    rows=[]
    for leaf in remaining:
     lay,pr,new=tuple(leaf['layout']),tuple(leaf['projection']),tuple(leaf['projection441_735'])
     upper,key,const=evaluate(lay,pr,new);prior=F(leaf['strongest_available_old_upper'])
     require(prior<=prior_complete,'The complete original266 upper remains available at every residual leaf')
     rows.append({'layout':lay,'projection':pr,'projection441_735':new,'complete375_upper':upper,
      'previous_available_upper':prior,'adopted_upper':min(upper,prior),'complete_tail_constant':const,'dual_key':key})
    final=max([incumbent]+[r['adopted_upper']for r in rows])
    require(0<final<prior_complete and len(rows)==counts['lp_remaining'] and used==set(bank),
            'All full-domain residual leaves are checked, every supplied dual is used, and the complete source improves strictly')
    for path,pin in pins.items():require(sha256(io.read_artifact_bytes(B/path)).hexdigest()==pin,'Stable final mathematical source '+path)
    encoded=codec.encode_dual_bank({key:bank[key]for key in sorted(used)},inequality_count=30454,equality_count=20)
    require(codec.decode_dual_bank(encoded,inequality_count=30454,equality_count=20)==bank,'Canonical lossless exact dual bank')
    return enc({'schema':'erdos7-j-face-retained375-ap11-heads-v1','source_sha256':pins,'geometry':p266['geometry'],
     'source_mass':F(1,4),'survivor_mass':F(3,20),'original264_model':problem.specification,'model':data['model'],
     'block':index,'name':'AP11-0','coefficients':co,'at_one':F(0),'complete_late_slope':late,
     'retained_old_labels':[25,27,75,81,135,125,225,375],'retained_positive7_labels':[21,35,63,105,147,245,441,735],
     'new_label':375,'new_label_survivor_cap':F(1,375),'raw_CRT_caps':data['raw_CRT_caps'],
     'complete_old_tail_before375':F(6151,405000),'complete_old_tail':newtail,'complete_positive7_tail':z8,
     'complete_tail_constant':late*(newtail+z8),'seed':{'layout':seed_layout,'projection':seed_projection},
     'seed_results':seed_rows,'fixed_pruning_benchmark':incumbent,'prefix_ledger':ledger,'residual_leaf_results':rows,
     'residual_leaf_count':len(rows),'complete_AP11_upper':final,'previous_complete_AP11_upper':prior_complete,
     'improvement_over_previous':prior_complete-final,'maximizing_residual_certificate_branch':max(rows,key=lambda r:r['adopted_upper'])if rows else None,
     'encoded_rational_duals':encoded,'distinct_dual_count':len(used),'rational_column_checks':N*len(used),
     'independent_direct_column_checks':N*len(used),'total_containing_choices':covered,
     'scope':'Complete original AP11-0 bound on both entire actual saturated J faces. Every3.125 billion independent original containing choice lies in the exact two/four/six/seven/eight prefix partition or an exactly checked residual375 leaf. The unchanged288 model keeps every original264 row, independent375 raw/survivor intersections and their complements, its original root-slot profile and all original CRT caps. The whole original positive hinge combination includes H1 exactly and retains late slope1. Only the assigned375 cap1/375 leaves the complete old tail;5071/405000 and13/490 remain. All50 original266 seed completions fix a pruning benchmark before any pruning; seed optimality is not assumed. The final bound is the maximum of this benchmark and every residual leaf minimum of a complete old and new bound. No statement about AP11-1, actual source attainment, off-face extension, global joining, complete52-cost comparison, Lean verification or unrestricted Erdos7 resolution is asserted.'})

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    modes=parser.add_mutually_exclusive_group();modes.add_argument('--write',action='store_true');modes.add_argument('--check',action='store_true')
    parser.add_argument('--proposal',type=Path);args=parser.parse_args()
    require(args.proposal is None or args.write,'Only the writer takes proposal data')
    require(not args.write or args.proposal is not None,'The writer requires all exact seed and residual certificates')
    io=module('retained375_ap11_read',args.base/'certificate_io.py');core=module('retained375_ap11_json',args.base/'frontier/j-geometry/j_face_joint_selected_heads.py')
    codec=module('retained375_ap11_codec',args.base/'frontier/retained-transport/retained135_heavy_comparison.py')
    proposed=json.loads(io.read_artifact_bytes(args.proposal if args.write else args.base/CERTIFICATE),object_pairs_hook=core.unique)
    bank=codec.decode_dual_bank(proposed['encoded_rational_duals'],inequality_count=30454,equality_count=20)
    result=calculate(args.base,bank)
    if args.write:io.write_certificate_text(args.base/CERTIFICATE,json.dumps(result,indent=2)+'\n')
    else:require(result==proposed,'Every complete375 AP11 field and full-domain prefix ledger recomputes exactly')
    print('PASS complete375 AP11-0;3125000000 original choices;'+str(result['residual_leaf_count'])+' residual leaves;upper '+str(float(F(result['complete_AP11_upper']))),flush=True)

if __name__=='__main__':
    try:main()
    except(ValueError,ArithmeticError,OSError,KeyError,TypeError,json.JSONDecodeError)as e:
        print('FAIL: '+str(e),file=sys.stderr);raise SystemExit(1)
