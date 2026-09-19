#!/usr/bin/env python3
"""Complete original heavy cost0 at543/100 with independent prefix reconstruction."""
import argparse
import importlib.util
import json
import sys
from pathlib import Path
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from time import perf_counter
sys.dont_write_bytecode=True
CERTIFICATE='certificates/source_norms/j-source/j_face_retained375_heavy_heads.json'


def require(ok,message):
    if not ok:raise ValueError(message)


def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    require(spec is not None and spec.loader is not None,'Loadable current source provider')
    value=importlib.util.module_from_spec(spec);spec.loader.exec_module(value);return value


def encode(value):
    if isinstance(value,F):return str(value)
    if isinstance(value,dict):return {str(k):encode(v)for k,v in value.items()}
    if isinstance(value,(tuple,list)):return [encode(v)for v in value]
    return value


def canonical_digest(value):
    return sha256(json.dumps(encode(value),sort_keys=True,separators=(',',':')).encode()).hexdigest()


def batches(rows,size=128):
    return [{'start':i,'stop':min(i+size,len(rows)),'rows':rows[i:i+size]}for i in range(0,len(rows),size)]


def unbatch(parts):
    result=[]
    for part in parts:
        require(set(part)=={'start','stop','rows'}and part['start']==len(result)
                and part['stop']-part['start']==len(part['rows'])and part['stop']>part['start'],
                'Contiguous nonempty complete evidence batches')
        result.extend(part['rows'])
    return result


def inputs(B):
    provider=module('heavy375_current288',B/'frontier/j-source/j_face_retained375_survival_heads.py')
    data=provider.make_extended_model(B);io=data['io'];pins=dict(provider.PINS)
    read=lambda n:json.loads(io.read_artifact_bytes(B/'certificates/source_norms'/(n+'.json')))
    p264=read('j-source/j_face_triple_second_depth_heads');p288=read('j-source/j_face_retained375_survival_heads')
    for doc in (p264,p288):
        for path,pin in doc['source_sha256'].items():
            require(path not in pins or pins[path]==pin,'Consistent actual-source closure '+path);pins[path]=pin
    for path in ('frontier/j-source/j_face_retained375_survival_heads.py','certificates/source_norms/j-source/j_face_retained375_survival_heads.json'):
        pins[path]=sha256(io.read_artifact_bytes(B/path)).hexdigest()
    for path,pin in pins.items():require(sha256(io.read_artifact_bytes(B/path)).hexdigest()==pin,'Pinned source '+path)
    require(data['model']==p288['model']and data['model']['rows_sha256']=='e591c59f8891f6647f0e21f303cd3be9ca661f1d5b48ebd0625c2de85cfa32d0'
            and data['reference'].specification==p264['model']==p288['original264_model'],
            'The whole current original375 model and every inherited264 constraint')
    require(p264['geometry']==p288['geometry']and all(F(d['source_mass'])==F(1,4)and F(d['survivor_mass'])==F(3,20)for d in(p264,p288)),
            'The same actual raw/survivor measures on both complete saturated J faces')
    second=module('heavy375_current_second',B/'frontier/j-source/j_face_second_depth_retained_heads.py')
    data.update(p264=p264,p288=p288,pins=pins,second=second);return data


def calculate(B,proof):
    data=inputs(B)
    lp,problem,j,depth,triple,codec,io,second=(data[k]for k in('lp','reference','j','depth','triple','codec','io','second'))
    p264,p288,pins=(data[k]for k in('p264','p288','pins'))
    enc=encode;N,U,V,L=12941,6531,9731,12931;index=0;started=perf_counter()
    modelhash=data['model']['rows_sha256'];newtail=F(5071,405000);z8=F(13,490)
    require(F(p288['complete_old_tail'])==newtail and F(p288['complete_positive7_tail'])==z8
            and F(p288['new_label_survivor_cap'])==F(1,375),'Only the original375 payment is removed from the full tail')
    src=next(r for r in p264['results']if r['index']==0)
    co={int(t):F(a)for t,a in src['scan']['coefficients'].items()};late=sum(co.values());prior_complete=F(src['adopted_upper'])
    require(F(src['at_one'])==0 and min(co.values())>0 and set(co)==set(range(1,9))and late==F(403,8),
            'The complete original heavy0 hinge function, including H1 and the full late slope')
    scopedrow=proof['prefix_seed'];incumbent=F(scopedrow['scoped_upper'])
    require(incumbent==F(15751281119445414267484319072612603681,2913167994208453627395750000000000000)
            and 0<incumbent<F(543,100)<prior_complete,'The unchanged original fixed threshold and new target are distinct')
    scopedbank=codec.decode_dual_bank(proof['encoded_prefix_seed_duals'],inequality_count=30454,equality_count=20)
    head=problem.head;oldrecord=head.prepare(co);old=oldrecord;six=problem.prepare_six(old)
    scale=old['factor']/j.TOTAL;weights=sorted(set(head.w));pairs=list(product(range(5),range(5)));ints=old['primitive_coefficients']
    require(all(old['factor']*ints[t]==co[t]for t in co),'Exact original primitive scaling')
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

    seed_layout=tuple(scopedrow['layout']);seed_projection=tuple(scopedrow['projection'])
    seed_bounds={};seedkeys=set()
    require(len(scopedrow['branches'])==50,'All50 independent327 projection completions')
    for row in scopedrow['branches']:
     new=tuple(row['new441_735_projection']);obj,const=complete_objective(seed_layout,seed_projection,new)
     key=sha256(json.dumps([modelhash,enc(obj)],separators=(',',':')).encode()).hexdigest()
     require(key==row['dual_key'] and key in scopedbank,'Byte-identical original327 full model and objective')
     raw=lp.checker.check(obj,scopedbank[key]);direct_check(obj,scopedbank[key],raw)
     upper=raw+const
     require(upper==F(row['complete_upper']) and const==F(row['complete_tail_constant']),
             'Every327 complete objective and infinite-tail constant replays exactly')
     seed_bounds[seed_layout,seed_projection,new]=upper;seedkeys.add(key)
    require(set(new for lay,pr,new in seed_bounds)==set(product(range(5),range(2),range(5)))
            and len(seedkeys)==50 and max(seed_bounds.values())==incumbent,'Complete50-case327 maximum is the fixed threshold')
    problem.bank=codec.decode_dual_bank(p264['encoded_rational_duals'],inequality_count=11211,equality_count=19)
    print('PREFIX298 seed certificates verified',flush=True)

    # The strengthened affine bound retains four original old labels for every
    # original hinge, with the exact same old CRT telescoping inequalities.
    raw={}
    for w,p in product(weights,pairs):
     raw[w,*p]=[0]+[j.integer(j.SCALE*sum(a*(F(w,5)*max(v-t,0)+depth.seven_increment(t,v,*p))for t,a in ints.items()))for v in range(1,11)]
     for v in range(1,7):
      inc=[raw[w,*p][v+k+1]-raw[w,*p][v+k]for k in range(4)]
      require(min(inc)>=0 and all(a<=b for a,b in zip(inc,inc[1:])),
              'Four-step integer-convex telescoping for the whole original heavy function')
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
       require(scale*aff[x]==rational(lay,ff,ss,tail,theta),'Independent heavy rational affine endpoint, stage'+name);verify_count+=1
     for c441,r735,s735 in product(range(5),range(2),range(5)):
      sec7=tuple(a+int(c==c441)for a,(c,k)in zip(sec,product(range(5),repeat=2)))
      sec8=tuple(a+int(j.ROOT[c]==r735 and k==s735)for a,(c,k)in zip(sec7,product(range(5),repeat=2)))
      for name,ss,tail in [('seven',sec7,second.Z6-F(1,490)),('eight',sec8,z8)]:
       aff=head.objective(records[name],BB,tuple(zip(first,ss)),cor,True)
       for theta,x in ((j.LO,0),(j.HI,1)):
        require(scale*aff[x]==rational(lay,first,ss,tail,theta),'Independent heavy rational affine endpoint, stage'+name);verify_count+=1
    print('AFFINE298',index,'exact independent endpoint checks',verify_count,'seconds',round(perf_counter()-started,2),flush=True)

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
        if ov is not None:old_dual_used.add((256,okey));prior_values.append(ov)
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
     if il%2500==0:print('PREFIX298',index,il,'eight_seen',counts['eight_seen'],'unresolved',counts['lp_remaining'],'seconds',round(perf_counter()-started,2),flush=True)


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

    covered_domain=covered;branch_digest=digest.hexdigest()
    expected=proof['independent_prefix_reconstruction']
    leaves=unbatch(expected['original_leaf_batches'])
    require(encode(remaining)==leaves and canonical_digest(leaves)==expected['canonical_original_leaf_array_sha256']
            and counts==expected['counts']and encode(max_pruned)==expected['maximum_pruned_bounds'],
            'Canonical API reconstruction agrees with the independently reconstructed complete residual ledger')
    require(len(leaves)==20429 and not expected['original5000_rule_passed'],
            'Original5000 rule stays failed; no nonexistent original-writer result is compared')
    zero=set();zero_rows=unbatch(proof['zero_induction_batches'])
    for witness in zero_rows:
        rows,rights=(lp.rows,lp.rhs)if witness['kind']=='inequality'else(lp.equalities,lp.erhs)
        require(witness['kind']in('inequality','equality')and witness['sign']in((1,)if witness['kind']=='inequality'else(1,-1)),
                'A valid oriented original row licenses each strong-zero step')
        row=rows[witness['row']];sgn=witness['sign']
        require(rights[witness['row']]==0 and witness['negative_antecedents']==sorted(c for c,a in row.items()if sgn*a<0)
                and set(witness['negative_antecedents'])<=zero
                and witness['new_zero_columns']==sorted(c for c,a in row.items()if sgn*a>0 and c not in zero),
                'Every negative antecedent has an earlier certificate; all new positive columns must vanish')
        zero.update(witness['new_zero_columns'])
    require(len(zero)==4634 and len(zero_rows)==2645 and canonical_digest(zero_rows)==proof['zero_induction_sha256'],
            'Exactly the original strong-zero induction, no additional eliminated coordinates')
    cell_specs=[];mass_columns=set()
    for cell in range(25):
        specs={}
        def put(spec,col):
            require(col not in mass_columns,'Each original physical objective column occurs once')
            mass_columns.add(col);specs.setdefault(spec,[]).append(col)
        for mask in range(16):
            k=16*cell+mask;q=mask.bit_count();put(('X',q,0),k);put(('Y',q,0),425+k)
            for state in range(1,8):
                n=state.bit_count();put(('OU',q,n),triple.U+400*(state-1)+k);put(('OV',q,n),triple.V+400*(state-1)+k)
            for state in range(8):
                n=state.bit_count();put(('NU',q,n),U+400*state+k);put(('NV',q,n),V+400*state+k)
        require(len(specs)==80,'Every fixed physical cardinality coefficient specification');cell_specs.append(specs)
    require(len(mass_columns)==12800 and N-len(mass_columns)==141,'Full objective column inventory')
    cache={}
    def scalar(spec,param):
        key=spec,tuple(param)
        if key in cache:return cache[key]
        b,m,e=param;kind,q,n=spec;v=b+q;gg=gs[m,e]
        value={'X':lambda:gg[v],'Y':lambda:hs[v],'OU':lambda:gg[v+n]-gg[v],
               'OV':lambda:hs[v+n]-hs[v],'NU':lambda:gg[v+n+1]-gg[v+n],
               'NV':lambda:hs[v+n+1]-hs[v+n]}[kind]()
        cache[key]=value;return value
    def parameters(leaf):
        hh=head.bridge.head_load(tuple(leaf['layout']));r,s,c63,r105,s105,r147,s245=leaf['projection'];c441,r735,s735=leaf['projection441_735']
        return [(b,int(j.ROOT[c]==r)+int(k==s)+int(c==c63)+int(j.ROOT[c]==r105 and k==s105),
                   int(j.ROOT[c]==r147)+int(k==s245)+int(c==c441)+int(j.ROOT[c]==r735 and k==s735))
                for b,(c,k)in zip(hh,product(range(5),repeat=2))]
    target=F(543,100);constant=late*(newtail+z8)
    require(constant==F(312316537,158760000),'Complete unchanged heavy0 tail')
    own={i for i,leaf in enumerate(leaves)if F(leaf['strongest_available_old_upper'])<=target}
    require(sorted(own)==proof['own_bound_leaf_indices']and len(own)==2768,'All and only own-old-bound closures')
    nodes=unbatch(proof['covering_node_batches'])
    bank=codec.decode_dual_bank(proof['encoded_covering_duals'],inequality_count=30454,equality_count=20)
    used=set();covered=set(own);kind_counts={};node_counts={};bounds_by_leaf={i:F(leaves[i]['strongest_available_old_upper'])for i in own}
    column_checks=0;maximum_comparisons=0;membership_checks=0;records=[]
    for number,node in enumerate(nodes):
        ids=node['original_leaf_indices'];kind=node['kind']
        require(kind in('prior70','stage1','stage2','stage3','final')and ids==sorted(set(ids))and ids
                and all(0<=i<len(leaves)and i not in covered for i in ids),'Disjoint nonempty original leaf cover')
        members=[leaves[i]for i in ids];params=[parameters(leaf)for leaf in members]
        if kind in('stage1','stage2','stage3'):
            require(all(leaf['layout']==members[0]['layout']and leaf['projection']==members[0]['projection']for leaf in members),
                    'The complete original layout and seven projection stay fixed')
            if kind in('stage2','stage3'):require(len({leaf['projection441_735'][0]for leaf in members})==1,'Original c441 fixed')
            if kind=='stage3':require(len({leaf['projection441_735'][1]for leaf in members})==1,'Original r735 fixed')
        attained=[sorted({param[cell]for param in params})for cell in range(25)];obj=[F(0)]*N
        for cell,specs in enumerate(cell_specs):
            for spec,cols in specs.items():
                values=[scalar(spec,p)for p in attained[cell]];value=max(values)
                require(value>=0 and all(v<=value for v in values),'Exact coordinatewise upper for every original member')
                for col in cols:
                    if col not in zero:obj[col]=value;maximum_comparisons+=len(values)
            for param in params:require(param[cell]in attained[cell],'Every original member included');membership_checks+=1
        dual=bank[node['dual_id']]
        require(sha256(json.dumps([modelhash,dual],sort_keys=True,separators=(',',':')).encode()).hexdigest()==node['dual_id'],
                'Dual identity includes exact prices, not merely the generating objective name')
        raw=lp.checker.check(obj,dual);direct_check(obj,dual,raw);upper=raw+constant
        require(upper==F(node['complete_upper'])<=target,'Complete exact envelope/direct certificate closes every member')
        used.add(node['dual_id']);covered.update(ids);column_checks+=N
        for i in ids:bounds_by_leaf[i]=min(upper,F(leaves[i]['strongest_available_old_upper']))
        kind_counts[kind]=kind_counts.get(kind,0)+len(ids);node_counts[kind]=node_counts.get(kind,0)+1
        records.append({'node':number,'kind':kind,'original_leaf_count':len(ids),'complete_upper':upper,'dual_id':node['dual_id']})
        if(number+1)%100==0:print('COVER298',number+1,'nodes,original leaves',len(covered),flush=True)
    require(kind_counts=={'prior70':305,'stage1':13569,'stage2':3611,'stage3':161,'final':15}
            and covered==set(range(20429))and used==set(bank),'Exact2768+305+13569+3611+161+15 full residual accounting and no unused covering dual')
    complete=max([target]+list(bounds_by_leaf.values()))
    require(complete==target and all(F(v)<=incumbent<target for v in max_pruned.values()),'Every original prefix and leaf closes the fixed new target')
    for path,pin in pins.items():require(sha256(io.read_artifact_bytes(B/path)).hexdigest()==pin,'Stable actual-source input '+path)
    checks={provider:sum(1 for p,key in old_dual_used if p==provider)for provider in(251,256,264)}
    prefix={'origin':'Independent complete reconstruction; no unavailable original-writer artifact is compared.',
            'counts':counts,'covered_containing_choices':covered_domain,'fixed_original_threshold':incumbent,
            'canonical_original_leaf_array_sha256':canonical_digest(leaves),'maximum_pruned_bounds':max_pruned,
            'all_branch_decisions_sha256':branch_digest,'original5000_rule_passed':False,
            'existing_source_duals_rechecked':[{'source':p,'dual_key':key}for p,key in sorted(old_dual_used)],
            'existing_source_dual_counts':checks,'seed_column_checks':50*N,
            'independent_fractional_affine_checks':verify_count,'infinite_bridge_transition_checks':transition_count}
    return encode({'schema':'erdos7-j-face-retained375-heavy-heads-v1','source_sha256':pins,
                   'geometry':p264['geometry'],'source_mass':F(1,4),'survivor_mass':F(3,20),
                   'index':0,'name':'cost0','original_coefficients':co,'at_one':F(0),'complete_late_slope':late,
                   'model':data['model'],'original264_model':problem.specification,
                   'retained_old_labels':[25,27,75,81,135,125,225,375],
                   'retained_positive7_labels':[21,35,63,105,147,245,441,735],
                   'complete_old_tail':newtail,'complete_positive7_tail':z8,'complete_tail_constant':constant,
                   'previous_complete_upper':prior_complete,'complete_upper':complete,'improvement':prior_complete-complete,
                   'target_closed':True,'total_containing_choices':3125000000,'original_residual_leaf_count':20429,
                   'prefix_ledger':prefix,'own_bound_closed_leaves':len(own),'covering_leaf_counts':kind_counts,
                   'covering_node_counts':node_counts,'distinct_covering_duals':len(bank),
                   'strong_zero_columns':len(zero),'strong_zero_induction_rows':len(zero_rows),
                   'rational_column_checks':column_checks,'independent_rational_column_checks':column_checks,
                   'physical_column_maximum_comparisons':maximum_comparisons,'original_member_cell_checks':membership_checks,
                   'verified_node_batches':batches(records),'proof_data':proof,
                   'scope':'Complete original heavy0 function on both saturated J faces with actual raw and survivor masses, all original independent labels, and every infinite tail. Original329 failed5000 rule is unchanged. Exact rational certificate, not actual attainment, off-face extension, Lean verification or unrestricted Erdos7.'})


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    parser.add_argument('--certificate',type=Path)
    parser.add_argument('--output',type=Path)
    parser.add_argument('--write',action='store_true')
    parser.add_argument('--check',action='store_true',help='Regenerate and check the complete certificate (the default)')
    args=parser.parse_args();B=args.base.resolve()
    require(not(args.write and args.check),'Choose writing or checking the complete source')
    io=module('heavy375_cli_io',B/'certificate_io.py')
    path=args.certificate or B/CERTIFICATE;old=json.loads(io.read_artifact_bytes(path))
    result=calculate(B,old['proof_data'])
    if args.write:io.write_certificate_text(args.output or B/CERTIFICATE,json.dumps(result,indent=2)+'\n')
    else:require(result==old,'Entire source certificate regenerates exactly')
    print('PASS298 complete heavy0 <= '+result['complete_upper']+'; all3125000000 original choices verified',flush=True)


if __name__=='__main__':main()
