#!/usr/bin/env python3
"""Six complete original quadratic observations on one actual aligned source.

Only final disjoint source covers and exactly checked rational duals are kept.
The standard-library checker rebuilds every whole-function prefix and tail.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product,combinations
from collections import defaultdict
from functools import lru_cache
from types import SimpleNamespace
from math import lcm
from hashlib import sha256
import importlib.util,json,sys,argparse,time
sys.dont_write_bytecode=True
CERTIFICATE='certificates/source_norms/j-source/j_aligned_quadratic_complete_heads.json'
NAMES=('square','factorial2','factorial3','factorial5','cost48','cost49')
def require(p,m):
 if not p:raise ValueError(m)
def mod(n,path):
 s=importlib.util.spec_from_file_location(n,path);require(s is not None and s.loader is not None,'Loadable mathematical input')
 m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
def encode(x):
 if isinstance(x,F):return str(x)
 if isinstance(x,dict):return {str(k):encode(v)for k,v in x.items()}
 if isinstance(x,(tuple,list)):return [encode(v)for v in x]
 return x
def context(B):
 p=mod('retained_quadratic_actual375',B/'frontier/j-source/j_aligned_quadratic_sharp_source.py');data=p.build(B);lp,io=data['lp'],data['io'];load=lambda path:json.loads(io.read_artifact_bytes(path),object_pairs_hook=io._unique)
 heavy=load(B/'certificates/source_norms/j-source/j_face_retained375_heavy_heads.json');zero=p.zero_induction(data,heavy)
 zero['new_explicit_E5_zero_columns']=sorted({850+5*c+s for c in range(5)for s in range(5)if s!=3}-set(zero['zero_columns']))
 aligned=mod('retained_quadratic_actual313',B/'frontier/j-source/j_aligned_joint_selected_heads.py');small=aligned.strengthen(aligned.build_source(B,'retained_quadratic_actual_coarse'));j=small['j']
 moment=mod('retained_quadratic_moment',B/'frontier/j-source/j_face_shared_square_factorial.py');mom=moment.JMomentHead(j)
 mom.descendant=tuple(F(2,27)if i==14 else v for i,v in enumerate(mom.descendant))
 coherent=mod('retained_quadratic_raw_caps',B/'frontier/j-source/j_face_coherent_positive7_pairs.py')
 orig=load(B/aligned.ORIGINAL);bases={r['name']:r for r in orig['basis']}
 retained=(25,27,75,81,135,125,225,375)
 def exponents(d):
  a=b=0
  while d%3==0:d//=3;a+=1
  while d%5==0:d//=5;b+=1
  p.require(d==1,'Original35 modulus');return a,b
 survc=(F(11,20),F(13,30),F(1,3),F(1,9))
 def surv(d):
  a,b=exponents(d)
  if b==0:return survc[0]/3**a
  if a<=2:return survc[a+1]/5**b
  return F(1,3**a*5**b)
 oo=[{'labels':(a,b),'lcm':lcm(a,b),'assigned_cap':surv(lcm(a,b))}for a,b in combinations(retained,2)]
 seven=((1,'all',F(1,5)),)+tuple((d,e,F(6,5*7**e))for e in(1,2)for d in(3,5,9,15))
 oz=[{'old':a,'positive7_cofactor':d,'depth':e,'old_lcm':lcm(a,d),'assigned_cap':weight*coherent.raw_cap(*exponents(lcm(a,d)))}for a in retained for d,e,weight in seven]
 poo,poz,pzz=F(111,800),F(121,720),F(3893,10800);oo_pay=sum(r['assigned_cap']for r in oo);oz_pay=sum(r['assigned_cap']for r in oz)
 p.require(len(oo)==28 and len(oz)==72 and poo>oo_pay and poz>oz_pay,'Disjoint assigned selected pair subseries and positive complete complements')
 pair_remaining=poo-oo_pay+poz-oz_pay+pzz
 OLD=(F(1,18),F(1,20),F(1,20),F(1,20),F(1,72));SEL=(F(1,27)+F(1,81),F(1,25)+F(1,125),F(1,25)+F(1,125),F(1,25),F(1,135));REM=tuple(a-b for a,b in zip(OLD,SEL));RAW=(F(1,245),)*4+(F(1,5),)
 p.require(min(REM)>0 and F(1,5)-F(6,35)-F(6,245)==F(1,245),'Every omitted zero7 and positive7 depth remains in assigned geometric series')
 expansions={'square':(F(1),{1:F(3)},F(2),2),'factorial2':(F(0),{},F(1),2),'factorial3':(F(0),{},F(1),3),'factorial5':(F(0),{},F(1),5),'cost48':(F(0),{3:F(5)},F(2),3),'cost49':(F(0),{2:F(31,16),3:F(17,16)},F(2),2)}

 raw314=load(B/'certificates/source_norms/j-source/j_aligned_raw_prime_path_moments.json')
 p.require((poo,poz,pzz)==tuple(F(raw314[key])for key in('complete_POO_upper','complete_POZ_upper','complete_PZZ_upper')),'Current independently checked314 raw interface')

 for name,(atone,co,fc,k)in expansions.items():
  phi=lambda n:F(max(n-k,0)*max(n-k+1,0),2)
  f=lambda n:atone+sum(a*max(n-t,0)for t,a in co.items())+fc*phi(n)
  p.require([f(n)for n in range(1,9)]==list(map(F,bases[name]['low_load_values'])),'Every original function finite transition')
  p.require([atone-sum(t*a for t,a in co.items())+fc*F(k*(k-1),2),sum(co.values())+fc*F(1-2*k,2),fc/2]==list(map(F,bases[name]['tail_polynomial'])),'Every original function entire infinite quadratic continuation')
  for b,r in product(range(1,7),range(9)):
   slope=max(b-k+1,0)+r-max(b+r-k+1,0)
   p.require(phi(b)+max(b-k+1,0)*r+F(r*(r-1),2)-phi(b+r)>=0 and slope==min(r,max(k-1-b,0))>=0,'Exact retained head gap and full selected-seven slope correction')
 return SimpleNamespace(**locals())

def prefix_functions(m):
 p,j,head,io=m.p,m.j,m.small['head'],m.io
 pre,_,desc,w=j.source_tables(j.LO);desc=[list(r)for r in desc];desc[2][4]=F(2,27)
 P=tuple(tuple(j.integer(20*v)for v in r)for r in pre);D=tuple(tuple(j.integer(54*v)for v in r)for r in desc);W=tuple(j.integer(5*v)for r in w for v in r)
 C=tuple(tuple(j.integer(3240*v)for r in j.source_tables(t)[1]for v in r)for t in(j.LO,j.HI))
 M=(((tuple(range(25)),)),tuple(tuple(5*c+s for c,s in product(range(5),repeat=2)if j.ROOT[c]==r)for r in range(2)),tuple(tuple(5*c+s for s in range(5))for c in range(5)),tuple(tuple(5*c+s for c in range(5))for s in range(5)),tuple(tuple(5*c+s for c in range(5)if j.ROOT[c]==r)for r,s in product(range(2),range(5))),tuple((i,)for i in range(25)))
 def rawN(z,ep):return sum(a*b for a,b in zip(z,C[ep]))-27*min(z[i]for i in j.SUPPORT)
 def oldN(z):
  a=3*max(sum(P[c][s]*z[5*c+s]for s in range(5))for c in range(5))
  a+=max(sum(D[c][s]*z[5*c+s]for c in range(5))for s in range(5))
  a+=max(sum(D[c][s]*z[5*c+s]for c in range(5)if j.ROOT[c]==r)for r,s in product(range(2),range(5)))
  a+=max(D[c][s]*z[5*c+s]for c,s in product(range(5),repeat=2))+15*max(z)
  return a
 def correctionN(f):
  return 36*(sum(j.integer(20*j.QSLOTS[s])*min(f[s],f[5+s])for s in range(5))+sum(j.integer(18*j.ETA[c])*(1+j.ROOT[c])*f[5*c+3]for c in range(5)))
 def correction(f):return F(correctionN(f),64800)
 def phi_lines(bb,k):
  f=tuple(max(v-k,0)*max(v-k+1,0)//2 for v in bb);h=tuple(max(v-k+1,0)for v in bb);z=tuple(a*b for a,b in zip(W,f));zh=tuple(a*b for a,b in zip(W,h));out=[]
  old=oldN(zh)+oldN(h);corr=correctionN(f)
  for ep in range(2):
   row=sum(max(rawN(tuple(h[i]if i in mask else 0 for i in range(25)),ep)for mask in family)for family in M)
   out.append(F(4*rawN(z,ep)+12*old+4*row-corr+3*14413,64800))
  return tuple(out)
 return SimpleNamespace(phi_lines=phi_lines,correction=correction)

def make_objective(m,conditional,name):
 p,data,lp,io,j=m.p,m.data,m.lp,m.io,m.j
 atone,co,fc,k=m.expansions[name];zero=set(m.zero['zero_columns'])
 cf,cs,ct=conditional['first'],conditional['second'],conditional['tail']
 phi=lambda v:F(max(v-k,0)*max(v-k+1,0),2)
 h=lambda v:F(max(v-k+1,0))
 hs={v:sum(a*max(v-t,0)for t,a in co.items())+fc*phi(v)for v in range(1,15)}
 gs={(n,e):{v:sum(a*data['seven_increment'](t,v,n,e)for t,a in co.items())+fc*h(v)*(F(1,5)+F(6,35)*n+F(6,245)*e)for v in range(1,15)}for n,e in product(range(5),repeat=2)}
 specs=[];physical=set()
 for cell in range(25):
  dd=defaultdict(list)
  def put(spec,col):physical.add(col);dd[spec].append(col)
  for mask in range(16):
   z=16*cell+mask;q=mask.bit_count();put(('X',q,0),z);put(('Y',q,0),425+z)
   for st in range(1,8):n=st.bit_count();put(('OU',q,n),876+400*(st-1)+z);put(('OV',q,n),3676+400*(st-1)+z)
   for st in range(8):n=st.bit_count();put(('NU',q,n),6531+400*st+z);put(('NV',q,n),9731+400*st+z)
  specs.append(dd)
 p.require(len(physical)==12800,'Every physical full-function source column retained')
 @lru_cache(None)
 def scalar(spec,param):
  kind,q,n=spec;b,first,second=param;v=b+q;g=gs[first,second]
  return {'X':lambda:g[v],'Y':lambda:hs[v],'OU':lambda:g[v+n]-g[v],'OV':lambda:hs[v+n]-hs[v],'NU':lambda:g[v+n+1]-g[v+n],'NV':lambda:hs[v+n+1]-hs[v+n]}[kind]()
 @lru_cache(None)
 def endpoints(lay):
  bb=m.small['head'].bridge.head_load(lay);hh=tuple(h(b)for b in bb);zz=tuple(w*v for w,v in zip(m.mom.w,hh));pp,ee=m.mom.pre,m.mom.descendant
  caps=(max(sum(pp[5*c+s]*zz[5*c+s]for s in range(5))for c in range(5)),max(sum(ee[5*c+s]*zz[5*c+s]for c in range(5))for s in range(5)),max(sum(ee[5*c+s]*zz[5*c+s]for c in range(5)if j.ROOT[c]==r)for r,s in product(range(2),range(5))),max(a*b for a,b in zip(ee,zz)),max(zz))
  p.require(sum(a*b for a,b in zip(caps,m.OLD))==m.mom.old_tail(zz),'Complete cross coefficients of this own head')
  return tuple(sum(a*b for a,b in zip(caps,m.REM))+m.mom.old_tail(hh)/5+sum(weight*max(m.mom.lp(tuple(a*b for a,b in zip(mask,hh)),theta)for mask in family)for family,weight in zip(m.mom.masks[1:],m.RAW))for theta in(j.LO,j.HI))
 def objective(lay,pr,seconds):
  bb=m.small['head'].bridge.head_load(lay);r,s,c63,rr,ss=pr;params=[]
  for cell,b in enumerate(bb):
   c,slot=divmod(cell,5);first=int(j.ROOT[c]==r)+int(slot==s)+int(c==c63)+int(j.ROOT[c]==rr and slot==ss)
   ee={int(j.ROOT[c]==r2)+int(slot==s2)+int(c==c2)+int(j.ROOT[c]==rr2 and slot==ss2)for r2,s2,c2,rr2,ss2 in seconds};params.append(tuple((b,first,e)for e in sorted(ee)))
  obj=[F(0)]*lp.nvars
  for cell,dd in enumerate(specs):
   for spec,cols in dd.items():
    vals=[scalar(spec,param)for param in params[cell]];v=max(vals);p.require(min(vals)>=0,'Nonnegative exact full-function state increments')
    for col in cols:
     if col not in zero:obj[col]=v
  cross=endpoints(lay);secmax=tuple(max(cs[sec][ep]for sec in seconds)for ep in range(2));zz=tuple(cf[pr][ep]+secmax[ep]+ct for ep in range(2))
  affine=tuple(fc*(m.pair_remaining-m.pzz+cross[ep]+zz[ep])+atone*F(413,2700)+sum(co.values())*(data['complete_zero7_tail']+data['complete_positive7_tail'])for ep in range(2))
  # Each physical coefficient is its member maximum. The constant+theta
  # block is majorized at both endpoints and hence throughout [0,1].
  p.require(all(cs[sec][ep]<=secmax[ep]for sec in seconds for ep in range(2)),'Same finite affine envelope for every independent second profile')
  obj[875]=affine[1]-affine[0]
  return obj,affine[0]
 return objective

def conditional_raw(m):
 p,j,head,io,B,raw=m.p,m.j,m.small['head'],m.io,m.B,m.raw314
 paths=mod('conditional_actual_paths',B/'frontier/j-source/j_face_raw_prime_path_pairs.py');moment=mod('conditional_actual_moment',B/'frontier/j-source/j_face_shared_square_factorial.py');mom=moment.JMomentHead(j)
 pre,_,e,_=j.source_tables(j.LO);c3=tuple(sum(row)for row in pre);c5=tuple(sum(row[s]for row in e)for s in range(5));omitted=raw['complete_raw_omitted_tail']
 weights=((F(6,35),F(1,70)),(F(6,245),F(1,70)));tables=[{},{}];digest=sha256();start=time.monotonic();n=0
 for il,lay in enumerate(j.layouts()):
  H=tuple(head.bridge.head_load(lay));cross=mom.old_tail(H);a3=tuple(sum(pre[c][s]*H[5*c+s]for s in range(5))for c in range(5));a5=tuple(sum(e[c][s]*H[5*c+s]for c in range(5))for s in range(5))
  changes={name:paths.path_bound(3,3,a3,c3,name=='square')['block_change']+paths.path_bound(5,2,a5,c5,name=='square')['block_change']for name in('pair','square')}
  r,c,s,rr,ss,cc,tt=lay;key=(r,s,c,rr,ss)
  for ep,theta in enumerate((j.LO,j.HI)):
   P=mom.lp(tuple(F(v*(v-1),2)for v in H),theta)+cross+F(omitted['raw_omitted_distinct_pairs'])+changes['pair'];Q=mom.lp(tuple(F(v*v)for v in H),theta)+2*cross+2*F(omitted['raw_omitted_distinct_pairs'])+F(omitted['raw_omitted_diagonal'])+changes['square']
   row={'layout':lay,'theta':theta,'complete_raw_old_cross':cross,'block_changes':changes,'complete_bounds':{'pair':P,'square':Q}}
   digest.update(json.dumps(p.encode(row),sort_keys=True,separators=(',',':')).encode());n+=1
   for table,(a,b)in zip(tables,weights):table[key+(ep,)]=max(table.get(key+(ep,),F(-1)),a*P+b*Q)
  if(il+1)%2500==0:print('Conditional actual314',il+1,'seconds',round(time.monotonic()-start,2),flush=True)
 p.require(n==25000 and digest.hexdigest()==raw['all_endpoint_bounds_sha256'],'Every exact existing314 raw endpoint replayed before conditioning')
 tail=F(raw['complete_raw_pair_upper'])/245+F(raw['complete_raw_square_upper'])/210
 first={key:tuple(tables[0][key+(ep,)]for ep in range(2))for key in product(range(2),range(5),range(5),range(2),range(5))}
 second={key:tuple(tables[1][key+(ep,)]for ep in range(2))for key in first}
 record={'source314_sha256':sha256(io.read_artifact_bytes(B/'certificates/source_norms/j-source/j_aligned_raw_prime_path_moments.json')).hexdigest(),'source314_endpoint_sha256':digest.hexdigest(),'weights':weights,'remaining_depth_weights':(F(1,245),F(1,210)),'complete_remaining_depth_upper':tail,'first_profile_count':len(first),'second_profile_count':len(second),'conditional_table_sha256':sha256(json.dumps(encode([list(first.items()),list(second.items())]),sort_keys=True,separators=(',',':')).encode()).hexdigest()}
 return {'first':first,'second':second,'tail':tail,'record':record}

def prefix_plan(m,pf,conditional,name,target):
 p,j,head=m.p,m.j,m.small['head'];atone,co,fc,k=m.expansions[name]
 first,second,tail=conditional['first'],conditional['second'],conditional['tail']
 maxsecond=tuple(max(v[ep]for v in second.values())for ep in range(2))
 pending=[];counts={'layouts':0,'pure_layout_bounded':0,'two':0,'two_bounded':0,'four':0,'four_bounded':0}
 maximum=F(-1);prepared=head.prepare(co)if co else None;digest=sha256()
 for lay in j.layouts():
  bb=head.bridge.head_load(lay);phi=pf.phi_lines(bb,k);lines=tuple(fc*x+atone*F(413,2700)for x in phi);counts['layouts']+=1
  if not co:
   if max(lines)<=target:
    counts['pure_layout_bounded']+=1;maximum=max(maximum,max(lines));digest.update(repr(('layout',lay,lines)).encode())
   else:pending.append((lay,None,(lines,)))
  else:
   hc=tuple(sum(v*max(b-t,0)for t,v in prepared['primitive_coefficients'].items())for b in bb);corr=j.integer(j.TOTAL*pf.correction(hc));scale=prepared['factor']/j.TOTAL
   for r,s,extra in head.extras:
    two=tuple(scale*v+a for v,a in zip(head.objective(prepared,bb,extra,corr,False),lines));counts['two']+=1
    if max(two)<=target:
     counts['two_bounded']+=1;maximum=max(maximum,max(two));digest.update(repr(('two',lay,r,s,two)).encode());continue
    for c,rr,ss,added in head.added:
     counts['four']+=1;pr=(r,s,c,rr,ss);full=tuple(a+b for a,b in zip(extra,added));four=tuple(scale*v+a for v,a in zip(head.objective(prepared,bb,full,corr,True),lines));upper,_,_=j.max_min_affines(two,four)
     if upper<=target:
      counts['four_bounded']+=1;maximum=max(maximum,upper);digest.update(repr(('four',lay,pr,two,four)).encode())
     else:pending.append((lay,pr,(two,four)))
 groups={};closed=0
 for lay,oldpr,lines in pending:
  for pr in(first if oldpr is None else(oldpr,)):
   def upper(sec):
    delta=tuple(fc*(first[pr][ep]+sec[ep]+tail-F(3893,10800))for ep in range(2));ls=tuple(tuple(a+b for a,b in zip(line,delta))for line in lines)
    return max(ls[0])if len(ls)==1 else j.max_min_affines(*ls)[0]
   u=upper(maxsecond)
   if u<=target:closed+=500;maximum=max(maximum,u);digest.update(repr(('conditional-all',lay,pr,u)).encode());continue
   remain=[]
   for sec,endpoints in second.items():
    u=upper(endpoints)
    if u<=target:closed+=1;maximum=max(maximum,u);digest.update(repr(('conditional',lay,pr,sec,u)).encode())
    else:remain.append(sec)
   if remain:groups[(tuple(lay),pr)]=remain
 residual=sum(map(len,groups.values()));coarse=counts['pure_layout_bounded']*250000+counts['two_bounded']*25000+counts['four_bounded']*500
 require(counts['layouts']==12500 and coarse+closed+residual==3125000000,'All original12500 heads times500 first times500 second choices accounted')
 require(maximum<=target,'Every closed prefix satisfies its own scheduling threshold')
 record={'original_choices':3125000000,'counts':counts,'coarse_choices_closed':coarse,'conditional_choices_closed':closed,'residual_choices':residual,'remaining_first_profiles':len(groups),'maximum_complete_prefix_upper':maximum,'closed_prefix_digest':digest.hexdigest(),'remaining_groups_sha256':sha256(json.dumps(encode(list(groups.items())),separators=(',',':')).encode()).hexdigest()}
 return groups,record

def source_pins(m):
 paths=('frontier/j-source/j_aligned_quadratic_complete_heads.py','frontier/j-source/j_aligned_quadratic_sharp_source.py','frontier/j-source/j_aligned_retained375_source.py','frontier/j-source/j_aligned_joint_selected_heads.py','frontier/j-source/j_face_shared_square_factorial.py','frontier/j-source/j_face_coherent_positive7_pairs.py','frontier/j-source/j_face_raw_prime_path_pairs.py','certificates/source_norms/j-source/j_aligned_raw_prime_path_moments.json','certificates/source_norms/j-source/j_aligned_retained375_heavy553_heads.json','certificates/source_norms/j-source/j_face_retained375_heavy_heads.json',m.aligned.ORIGINAL)
 pins={path:sha256(m.io.read_artifact_bytes(m.B/path)).hexdigest()for path in paths}
 for path in('certificates/source_norms/j-source/j_aligned_joint_selected_heads.json','certificates/source_norms/j-source/j_aligned_raw_prime_path_moments.json'):
  prior=m.load(m.B/path)
  for name,pin in prior['source_sha256'].items():
   require(name not in pins or pins[name]==pin,'Consistent actual-source dependency identity');pins[name]=pin
 for path,pin in pins.items():require(sha256(m.io.read_artifact_bytes(m.B/path)).hexdigest()==pin,'Current source closure '+path)
 return pins

def flatten_batches(batches):
 out=[]
 for batch in batches:
  require(batch['start']==len(out)and batch['stop']==len(out)+len(batch['rows']),'Complete ordered final-node batches');out.extend(batch['rows'])
 return out

def calculate(base,candidate):
 m=context(base);pf=prefix_functions(m);conditional=conditional_raw(m);lp=m.lp
 require(candidate['model']==encode(m.data['model']),'Same full sharp375 source matrix')
 source=source_pins(m);bank=m.data['codec'].decode_dual_bank(candidate['encoded_rational_duals'],inequality_count=len(lp.rows),equality_count=23)
 require(tuple(row['name']for row in candidate['results'])==NAMES,'All and only six original independent observation labels')
 seconds=tuple(conditional['second']);used=set();results=[];column_checks=0
 for given in candidate['results']:
  name=given['name'];target=F(given['target_scheduling_upper']);groups,plan=prefix_plan(m,pf,conditional,name,target);objective=make_objective(m,conditional,name)
  expected={key:set(value)for key,value in groups.items()};seen={key:set()for key in groups};rows=[];best=plan['maximum_complete_prefix_upper'];nodes=flatten_batches(given['closed_node_batches'])
  for node in nodes:
   lay,pr=tuple(node['layout']),tuple(node['projection']);group=(lay,pr);indices=node['second_indices']
   require(group in expected and indices and all(isinstance(i,int)and 0<=i<500 for i in indices)and len(set(indices))==len(indices),'Nonempty independent original second-profile subset')
   selected=[seconds[i]for i in indices];members=set(selected)
   require(members<=expected[group]and not(members&seen[group]),'Every final node covers a disjoint subset of the actual unresolved group')
   obj,const=objective(lay,pr,selected);key=sha256(json.dumps([m.data['model']['rows_sha256'],encode(obj)],separators=(',',':')).encode()).hexdigest()
   require(key==node['dual_key']and key in bank,'Exact source-bound final objective and supplied rational dual')
   raw=lp.checker.check(obj,bank[key]);upper=raw+const;used.add(key);column_checks+=lp.nvars
   require(upper==F(node['complete_upper']),'Every final upper uses its exact full-function constant')
   seen[group]|=members;best=max(best,upper);rows.append({'layout':lay,'projection':pr,'second_indices':indices,'dual_key':key,'complete_upper':upper})
  require(seen==expected,'Final closed nodes partition every remaining own original choice')
  require(best>=0,'A nonnegative complete original observation bound')
  results.append({'name':name,'target_scheduling_upper':target,'complete_uniform_upper':best,'expansion':{'at_one':m.expansions[name][0],'positive_hinges':m.expansions[name][1],'factorial_coefficient':m.expansions[name][2],'factorial_threshold':m.expansions[name][3]},'complete_prefix':plan,'closed_node_count':len(rows),'closed_node_batches':[{'start':i,'stop':min(i+50,len(rows)),'rows':rows[i:i+50]}for i in range(0,len(rows),50)]})
  print('PASS complete own',name,'<=',best,'=',float(best),'closed nodes',len(rows),flush=True)
 require(used==set(bank),'Only final used rational duals remain in the certificate')
 return encode({'schema':'erdos7-aligned-quadratic-complete-heads-v1','source_sha256':source,'model':m.data['model'],'actual_raw_mass':F(1,4),'actual_survivor_mass':F(413,2700),'raw_moment_interface':{'POO':m.poo,'POZ':m.poz,'PZZ':m.pzz},'retained_old_labels':m.retained,'old_old_assigned_payments':m.oo,'old_positive7_assigned_payments':m.oz,'remaining_pair_tail_before_conditional_PZZ':m.pair_remaining,'remaining_zero7_cross_weights':m.REM,'remaining_positive7_cross_weights':m.RAW,'conditional_positive7':conditional['record'],'zero_induction':{k:v for k,v in m.zero.items()if k!='zero_columns'},'results':results,'original_choices_per_observation':3125000000,'distinct_dual_count':len(used),'full_rational_column_checks':column_checks,'encoded_rational_duals':m.data['codec'].encode_dual_bank(bank,inequality_count=len(lp.rows),equality_count=23),'scope':'Six independent original whole quadratic observations on the actual aligned equality source. All original own heads and first/second positive-seven profiles, all retained135/125/225/375 states and every exponent/cofactor tail remain. Final source covers preserve each own load;their separate maxima need not share an optimizer. No source realization of LP maxima, neighborhood,403 comparison or unrestricted conclusion is claimed.'})

def proposal(base,directory):
 m=context(base);bank={};results=[];seconds=list(product(range(2),range(5),range(5),range(2),range(5)));index={s:i for i,s in enumerate(seconds)}
 for name in NAMES:
  stem='j-aligned-quadratic-'if name=='square'else'j-aligned-quadratic-budget-'
  old=m.load(directory/(stem+'retained375-cover-'+name+'.json'));prefix=m.load(directory/(stem+'conditional-prefix-'+name+'.json'))
  require(old['model']==encode(m.data['model']),'Proposal uses the exact same new source model')
  groups=flatten_batches(prefix['remaining_group_batches']);oldbank=m.data['codec'].decode_dual_bank(old['encoded_rational_duals'],inequality_count=len(m.lp.rows),equality_count=23);closed=[]
  for node in flatten_batches(old['cover_node_batches']):
   if not node['closes']:continue
   group=groups[node['group']];key=node['dual_key'];require(key not in bank or bank[key]==oldbank[key],'Identical reused exact final dual');bank[key]=oldbank[key]
   closed.append({'layout':group['layout'],'projection':group['projection'],'second_indices':[index[tuple(s)]for s in node['second_projections']],'dual_key':key,'complete_upper':node['complete_upper']})
  results.append({'name':name,'target_scheduling_upper':old['target_scheduling_upper'],'closed_node_batches':[{'start':i,'stop':min(i+50,len(closed)),'rows':closed[i:i+50]}for i in range(0,len(closed),50)]})
 return {'model':encode(m.data['model']),'results':results,'encoded_rational_duals':m.data['codec'].encode_dual_bank(bank,inequality_count=len(m.lp.rows),equality_count=23)}

def main():
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2]);parser.add_argument('--certificate',type=Path);parser.add_argument('--proposal-directory',type=Path)
 mode=parser.add_mutually_exclusive_group();mode.add_argument('--write',action='store_true');mode.add_argument('--check',action='store_true');args=parser.parse_args();base=args.base.resolve();path=args.certificate or base/CERTIFICATE
 io=mod('complete_quadratic_io',base/'certificate_io.py');require(args.write==(args.proposal_directory is not None),'Only writer accepts the explicit completed proposal directory')
 given=proposal(base,args.proposal_directory)if args.write else json.loads(io.read_artifact_bytes(path),object_pairs_hook=io._unique);result=calculate(base,given)
 if args.write:io.write_certificate_text(path,json.dumps(result,indent=2)+'\n')
 else:require(result==given,'Every complete final-only source certificate field reconstructs')
 print('PASS six complete own quadratic observations;',result['distinct_dual_count'],'final exact duals;',result['full_rational_column_checks'],'full column checks',flush=True)
if __name__=='__main__':main()
