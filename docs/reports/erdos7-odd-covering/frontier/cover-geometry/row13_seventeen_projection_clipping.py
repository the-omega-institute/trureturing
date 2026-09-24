#!/usr/bin/env python3
"""Exact four-corner consumer for fixed Report558 old query projections.
H5,H7 >= 4 vary independently. First11 inventory has fixed depth 4.
Only 17 specified old row13 projections are fixed; all other old
cofactors, phases and heights are arbitrary. Every full label occurs
at most twice. The full 125-projection class is a sharper special case.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import defaultdict,Counter
from itertools import product
import argparse,json,re,hashlib
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source',type=Path,default=Path(__file__).resolve().parents[2]/'profile-notes/arithmetic/558-first-eleven-inventory-and-an-actual-phase-counterexample.md')
parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=parser.parse_args()
SOURCE=args.source
rx=re.compile(r'^\|\s*\((\d+),(\d+)\)\s*\|\s*\((\d+),(\d+),(\d+)\)\s*\|\s*\((\d+),(\d+),(\d+)\)\s*\|$')
table=[]
for line in SOURCE.read_text(encoding='utf-8').splitlines():
 m=rx.match(line)
 if m:
  a,b,r5,r7,g,s5,s7,h=map(int,m.groups());table.append([a,b,[r5,r7,g],[s5,s7,h]])
checks={}
def ck(k,c):
 if not c or k in checks:raise ValueError(k)
 checks[k]=True
ck('literal25rows',len(table)==25 and {(a,b) for a,b,*r in table}==set(product(range(5),repeat=2)))
slots=[(a,b,*r) for a,b,*rows in table for r in rows]
queries=list(product(range(5),repeat=3))
# Each prefix record is computed literally; only the zero residue can
# see pure or mixed comb teeth above height four.
prefix={}
for p in (5,7):
 hist=Counter();ts=(4,14,14,14) if p==5 else (5,19,19,19);ds=(3,)*4 if p==5 else (6,)*4
 for z in range(p**4):
  if any(z%(p**e) in (p**(e-1),2*p**(e-1)) for e in range(1,5)):continue
  originalmask=sum(1<<i for i,(a,b,r5,r7,g) in enumerate(slots) if z%(p**(a if p==5 else b))==(r5 if p==5 else r7))
  t=sum(z%(p**e)==r for e,r in enumerate(ts,1));d=sum(z%(p**e)==r for e,r in enumerate(ds,1))
  mixed=any(z%(p**e) in tuple(c*p**(e-1) for c in ((3,) if p==5 else (3,4))) for e in range(1,5))
  hist[originalmask,t,d,mixed,z==0]+=1
 prefix[p]=hist
 ck('one_zero_'+str(p),sum(n for k,n in hist.items() if k[-1])==1)

def coordinate(p,u):
 ans=defaultdict(F);multiplicity=1 if p==5 else 2
 for (bits,t,d,mixed,zero),count in prefix[p].items():
  if not zero:ans[bits,t,d,mixed]+=F(count,p**4)
  else:
   tail=(1-p**4*u)/(p-1)
   ans[bits,t,d,True]+=F(count,p**4)*multiplicity*tail
   ans[bits,t,d,False]+=F(count,p**4)*(1-(2+multiplicity)*tail)
 ck('coordinate_mass_'+str(p)+'_'+str(u),sum(ans.values())==1-2*(1-u)/(p-1))
 return ans

# Auxiliary expectations computed from total mass, full mean and the
# below-threshold product convolution only; no high tail is discarded.
def law(p,total,cap):
 return total,total+cap/(p-1),{1:total-cap/p,2:cap*(p-1)/p**2,3:cap*(p-1)/p**3}
def mul(a,b):
 d=defaultdict(F)
 for i,u in a[2].items():
  for j,v in b[2].items():
   if i*j<4:d[i*j]+=u*v
 return a[0]*b[0],a[1]*b[1],d
def hinge(a,t):return a[1]-t*a[0]+sum(((t-i)*v for i,v in a[2].items() if i<t),F())
def pa(x,y):
 a=mul(law(5,x,F(1)),law(7,y,F(1)));mass=x*y-F(1,12);hs={}
 for p,t,c in ((11,2,F(5,3)),(13,2,F(3,2)),(17,4,F(2)),(19,4,F(9,5))):
  hs[p]=hinge(a,t);mass-=2*c/(p-1)*hs[p];a=mul(a,law(p,F(1),c))
 return mass,hinge(a,3),hs
T=F(257,51)
def payoff(x,y):
 a,phi,_=pa(x,y);return (T-2)*a-phi
base=payoff(F(1,2),F(2,3));kreq=-base/(T-2)
A5=2*(payoff(F(1),F(2,3))-base);A7=3*(payoff(F(1,2),F(1))-base)
A57=6*(payoff(F(1),F(1))-base-A5/2-A7/3)
cache={}
def getcoordinate(p,u):
 if (p,u) not in cache:cache[p,u]=coordinate(p,u)
 return cache[p,u]

def evaluate(u,v,tag):
 left=getcoordinate(5,u);right=getcoordinate(7,v)
 x=sum(left.values());y=sum(right.values());mixed5=sum(w for k,w in left.items() if k[-1]);mixed7=sum(w for k,w in right.items() if k[-1])
 mixed=mixed5*mixed7;profiles=defaultdict(F)
 for (b5,t5,d5,m5),w5 in left.items():
  for (b7,t7,d7,m7),w7 in right.items():
   if m5 and m7:continue
   color=0;active=b5&b7
   for i,(_,_,_,_,g) in enumerate(slots):
    if active>>i&1:color|=1<<g
   ckkey=(color,t5,d5,t7,d7)
   profiles[ckkey]+=w5*w7
 old=sum(profiles.values());new=F();clipped=F();hq=F();histL=defaultdict(F)
 for (colors,t5,d5,t7,d7),mass in profiles.items():
  if not (colors&(1<<3) and colors&(1<<6) and not colors&(1<<9)):
   raise ValueError('invalid actual pure/query color mask')
  allowed=11**4-colors.bit_count()*1464;density=min(F(5,3),F(11**4,allowed))
  for j in range(5):
   count=allowed-11**3 if j==0 else 10*11**(3-j) if j<4 else 1
   weight=mass*density*F(count,11**4)
   L=1+t5+d7+d5*d7+(1+t5+d7+d5*t7)*j
   new+=weight;hq+=weight*max(L-2,0);clipped+=weight*min(F(1),F(max(L-2,0),4));histL[L]+=weight
 _,phi,hs=pa(x,y)
 S11=hs[11]/3-(old-new)
 credit=(A5*(x-F(1,2))+A7*(y-F(2,3))+A57*(x-F(1,2))*(y-F(2,3)))/(T-2)+F(1,12)-mixed
 margin=credit+S11+hs[13]/4-clipped-kreq
 ck(tag+'_old_mass',old==x*y-mixed)
 ck(tag+'_current_mass',sum(histL.values())==new)
 return {'u':u,'v':v,'x':x,'y':y,'mixed':mixed,'oldmass':old,'lambda11':new,'Hquery':hq,'clip':clipped,'F11':hs[11],'F13':hs[13],'S11':S11,'credit':credit,'margin':margin,'histL':dict(histL)}
corners=[evaluate(u,v,'corner'+str(i)) for i,(u,v) in enumerate(product((F(0),F(1,625)),(F(0),F(1,2401))))]
minimum=min(r['margin'] for r in corners)
ck('four_corners_positive',minimum>0)
ck('minimum_at_zero_tail_parameters',corners[0]['margin']==minimum)
# Exact bilinear interpolation witness at the independently literal H5 input.
h5=evaluate(F(1,3125),F(1,16807),'H5')
# Exact reference values from the independent literal H5 audit.
expected={'old_pure5_mass': '1563/3125', 'old_pure7_mass': '11205/16807', 'old_mixed_mass': '4375162/52521875', 'old_mass': '13138253/52521875', 'lambda11_mass': '19543635187/92276732625', 'Delta11': '12640086692/329559759375', 'F11': '145566677/1260525000', 'S11': '7707153701/55366039575000', 'F13': '16293608641/83194650000', 'Hquery': '576284087437178357/3165052096247916875', 'credit': '60892116313456328416741/486392060746509978060000000', 'score': '1847116434978435817595109482171/498226465976533312336177860000000', 'kreq': '6168733163201163811/1650097635185615616000', 'failure_margin': '41215601048458182112451566919/1328603909270755499563140960000000'}
for key,ek in [('x','old_pure5_mass'),('y','old_pure7_mass'),('mixed','old_mixed_mass'),('oldmass','old_mass'),('lambda11','lambda11_mass'),('Hquery','Hquery'),('F11','F11'),('F13','F13'),('S11','S11'),('credit','credit')]:ck('H5_'+key,h5[key]==F(expected[ek]))
# Independently computed by full old-query incidence aggregation.
clipdata={'saturated_actual_loss_upper':'619281345463565717/14607932751913462500','unavoidable_above_target_margin':'1370588963644965884709218881427/442867969756918499854380320000000'}
ck('H5_clip_matches_independent_incidence',h5['clip']==F(clipdata['saturated_actual_loss_upper']))
ck('H5_margin_matches_independent_incidence',h5['margin']==F(clipdata['unavoidable_above_target_margin']))
for key in ['x','y','mixed','oldmass','lambda11','Hquery','clip','F11','F13','S11','credit','margin']:
 interp=sum(r[key]*(625*h5['u'] if r['u'] else 1-625*h5['u'])*(2401*h5['v'] if r['v'] else 1-2401*h5['v']) for r in corners)
 ck('bilinear_H5_'+key,interp==h5[key])
# Also retain coefficients in actual u,v; their signs show monotonicity.
f00,f01,f10,f11=[r['margin'] for r in corners]
coef={'constant':f00,'u':625*(f10-f00),'v':2401*(f01-f00),'uv':625*2401*(f11-f10-f01+f00)}
ck('nonnegative_margin_coefficients',all(t>=0 for t in coef.values()))
# lambda_final <= lambda11 <= max of its four corner values.
maxmass=max(r['lambda11'] for r in corners)
query_bound=T-(T-2)*minimum/maxmass
# Release all old row13 projections except the following 17 numerical labels.
# Pure13 labels (unit old cofactor) are already included in every query.
CORE=(5,7,11,25,35,49,55,77,121,125,175,245,275,343,385,539,605)
x4=F(313,625);y4=F(1601,2401)
def cylinder_cap(a,b,c):
 return (F(1,5**a) if a else x4)*(F(1,7**b) if b else y4)*(F(5,3*11**c) if c else F(1))
def crt(parts):
 residue=0;modulus=1
 for m,r in parts:
  if m==1:continue
  residue+=modulus*((r-residue)*pow(modulus,-1,m)%m);modulus*=m
 if not (0<=residue<modulus and all(residue%m==r%m for m,r in parts)):
  raise ValueError('invalid CRT reconstruction')
 return modulus,residue
core=[]
for a,b,c in product(range(5),repeat=3):
 d=5**a*7**b*11**c
 if d not in CORE:continue
 r5=(3 if b else (4 if a==1 else 14)) if a else 0
 r7=((5 if b==1 else 19) if a and c else 6) if b else 0
 parts=[(5**a,r5),(7**b,r7),(11**c,9 if c else 0)]
 modulus,residue=crt(parts)
 ck('core_crt_'+str(d),modulus==d and all(residue%m==r%m for m,r in parts))
 core.append({'label':d,'exponents':[a,b,c],'residue':residue,'components':parts,'cap_at_H4':cylinder_cap(a,b,c)})
core.sort(key=lambda x:x['label'])
ck('core17_labels_exact',tuple(r['label'] for r in core)==CORE)
# Complete tail identities include every higher cofactor exponent.
for p,cap in ((5,F(1)),(7,F(1)),(11,F(5,3))):
 for depth in (1,4,12):
  ck('full_cap_tail_'+str(p)+'_'+str(depth),
     sum((cap/F(p**e) for e in range(1,depth+1)),F())
     +cap/F((p-1)*p**depth)==cap/F(p-1))
full_product=(x4+F(1,4))*(y4+F(1,6))*F(7,6)
debit=(full_product-x4*y4-sum(r['cap_at_H4'] for r in core))/4
ck('core17_debit',debit==F(292154333,104587560000))
core_margin=minimum-debit
ck('core17_positive_uniform_margin',core_margin>0)
core_bound=T-(T-2)*core_margin/maxmass
ck('core17_strict_target',core_bound<T)
# A finite 70+200-original core, with arbitrary originals outside its windows.
# The 17 old13 projections are prescribed only through current height four.
def combined_offset(x,y):
 _,_,hh=pa(x,y)
 pure=(A5*(x-F(1,2))+A7*(y-F(2,3))+A57*(x-F(1,2))*(y-F(2,3)))/(T-2)
 return pure+F(1,12)-x*y+hh[11]/3+hh[13]/4
x5=h5['x'];y5=h5['y']
offsets={(x,y):combined_offset(x,y) for x,y in product((F(1,2),x5),(F(2,3),y5))}
for y in (F(2,3),y5):
 ck('finite_offset_decreases_x_'+str(y),offsets[x5,y]<=offsets[F(1,2),y])
for x in (F(1,2),x5):
 ck('finite_offset_decreases_y_'+str(x),offsets[x,y5]<=offsets[x,F(2,3)])
ck('finite_score_telescopes',combined_offset(x5,y5)+h5['lambda11']-h5['clip']-kreq==h5['margin'])
ap=x5+F(1,4);bp=y5+F(1,6)
t5=F(1,4*5**5);t7=F(1,6*7**5)
old_debit=2*(t5*bp+t7*ap-t5*t7)
old_box=(x5+sum((F(1,5**i) for i in range(1,6)),F()))*(y5+sum((F(1,7**i) for i in range(1,6)),F()))
ck('finite_complete_old_complement',old_debit==2*(ap*bp-old_box))
a11=F(1,4*5**4);b11=F(1,6*7**4);c11=F(1,10*11**4)
j11=2*((a11*bp+b11*ap-a11*b11)/10+(ap-a11)*(bp-b11)*c11)
box11=(ap-a11)*(bp-b11)*sum((F(1,11**e) for e in range(1,5)),F())
ck('finite_complete_first11_complement',j11==2*(ap*bp/10-box11))
corecap5=sum((F(1,5**a) if a else x5)*(F(1,7**b) if b else y5)*(F(5,3*11**c) if c else F(1)) for a,b,c in (r['exponents'] for r in core))
j13=(ap*bp*F(7,6)-x5*y5-corecap5)/4+corecap5/F(4*13**4)
finite_margin=h5['margin']-old_debit-F(5,3)*j11-j13
finite_bound=T-(T-2)*finite_margin/h5['lambda11']
ck('finite_old_debit',old_debit==F(93413,630262500))
ck('finite_first11_debit',j11==F(718178719,8388793875000))
ck('finite_row13_debit',j13==F(292309125085163,104549385540600000))
ck('finite_window_positive_margin',finite_margin>0)
ck('finite_window_strict_query_bound',finite_bound<T)
finite_window={'old_height5':5,'old_height7':5,'first11_box':[4,4,4],'constrained13_depth':4,'prescribed_old_originals':70,'prescribed_first11_originals':200,'constrained13_numerical_labels':68,'pure5_mass_ceiling':x5,'pure7_mass_ceiling':y5,'combined_offset_corners':[{'x':x,'y':y,'offset':z} for (x,y),z in offsets.items()],'old_complement_debit':old_debit,'first11_complement_original_cap':j11,'row13_complement_debit':j13,'margin':finite_margin,'max_lambda11':h5['lambda11'],'query_bound':finite_bound,'query_bound_decimal':float(finite_bound),'scope':'Exact70 old originals in0<=a,b<=5; exact200 first11 originals in0<=a,b<=4,1<=c<=4; the17 old13 projections fixed only at current13 exponents1..4, with no occurrence requirement; every other original and phase arbitrary in any finite two-copy Q-family.'}
result={'statement':__doc__,'table':table,'source_table_markdown_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
'corners':corners,'H5':h5,'margin_coefficients':coef,'uniform_margin':minimum,'max_lambda11':maxmass,'uniform_query_bound':query_bound,'uniform_query_bound_decimal':float(query_bound),
'finite_window':finite_window,'core17':core,'core17_complement_debit':debit,'core17_uniform_margin':core_margin,'core17_uniform_query_bound':core_bound,'core17_uniform_query_bound_decimal':float(core_bound),
'kreq':kreq,'checks':checks,'check_count':len(checks),'scope':'Independent H5,H7>=4; fixed literal first11 depth4 table; old13 projections fixed only at the listed17 cofactors; all other old13 cofactors and phases arbitrary at all finite heights; arbitrary 17/19 originals; at most two copies per full label; ordinary proof and exact arithmetic, not Lean or unrestricted NC4'}
def enc(x):
 if isinstance(x,F):return str(x)
 raise TypeError(type(x).__name__)
args.output.write_text(json.dumps(result,default=enc,indent=2)+'\n',encoding='utf-8')
for r in corners:print('corner',r['u'],r['v'],'margin',r['margin'],float(r['margin']),'clip',float(r['clip']))
print('coefficients',{k:str(v) for k,v in coef.items()})
print('query_bound',query_bound,float(query_bound),'checks',len(checks))

print('core17 debit',debit,float(debit),'margin',core_margin,float(core_margin),'R',core_bound,float(core_bound),'checks',len(checks))

print('finite_window margin',finite_margin,float(finite_margin),'R',finite_bound,float(finite_bound),'checks',len(checks))
