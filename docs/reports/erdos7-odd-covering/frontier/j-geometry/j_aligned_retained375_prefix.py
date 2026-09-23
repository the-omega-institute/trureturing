#!/usr/bin/env python3
"""Complete actual-source eight-projection prefix for one original own load.

Both writing and isolated checking recompute every source prefix using exact
standard-library arithmetic. No stored saturated numerical bound is reused.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product,combinations
from hashlib import sha256
import importlib.util,json,sys,time,argparse
sys.dont_write_bytecode=True
def module(n,f):
 s=importlib.util.spec_from_file_location(n,f);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
parser=argparse.ArgumentParser()
parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
parser.add_argument('--name',choices=['cost0','hinge4'],required=True)
parser.add_argument('--target',required=True)
parser.add_argument('--certificate',type=Path,required=True)
mode=parser.add_mutually_exclusive_group(required=True);mode.add_argument('--write',action='store_true');mode.add_argument('--check',action='store_true')
args=parser.parse_args();B=args.base.resolve()
p=module('aligned375_prefix_provider',Path(__file__).with_name('j_aligned_retained375_source.py'))
aligned=module('aligned375_prefix_actual',B/'frontier/j-geometry/j_aligned_joint_selected_heads.py')
d=aligned.strengthen(aligned.build_source(B,'aligned375_prefix'));j,head,io=d['j'],d['head'],d['io'];require=p.require
read=lambda f:json.loads(io.read_artifact_bytes(f),object_pairs_hook=io._unique)
depth=module('aligned375_prefix_two_depth',B/'frontier/comparison-bounds/second_depth_seven_comparison.py');trip=module('aligned375_prefix_affine_min',B/'frontier/j-geometry/j_face_triple_second_depth_heads.py')
co=p.coefficients(B,args.name)
old=head.prepare(co);scale=old['factor']/j.TOTAL;ints=old['primitive_coefficients'];pairs=list(product(range(5),repeat=2));weights=sorted(set(head.w));g=F(1,135)
tails={'two':j.Z2,'four':j.Z4,'six':F(37,1225)-8*g/245,'seven':F(37,1225)-8*g/245-F(1,490),'eight':F(13,490)-2*g/245}
require(tails['six']-F(1,490)-(F(1,15)-g)*F(6,245)==tails['eight'],'Entire adjusted441/735 tail partition')
raw={(t,w,m,e):[0]+[j.integer(j.SCALE*(F(w,5)*max(v-t,0)+depth.seven_increment(t,v,m,e)))for v in range(1,11)]for t,w,(m,e)in product(ints,weights,pairs)}
for arr in raw.values():
 dif=[b-a for a,b in zip(arr[1:],arr[2:])];require(min(dif)>=0 and all(a<=b for a,b in zip(dif,dif[1:])),'Whole finite bridge transitions; exact affine branch above highest threshold')
def prepared(tail,all_four):
 keep=lambda t,i:((4 if all_four else min(t-1,4))>=i)
 h={(w,(m,e)):[0]+[sum(a*raw[t,w,m,e][v]for t,a in ints.items())for v in range(1,7)]for w,(m,e)in product(weights,pairs)}
 inc={(i,k):{(w,(m,e)):[0]+[sum(a*(raw[t,w,m,e][v+k+1]-raw[t,w,m,e][v+k])for t,a in ints.items()if keep(t,i))for v in range(1,7)]for w,(m,e)in product(weights,pairs)}for i in range(1,5)for k in range(i)}
 const=j.integer(j.TOTAL*sum(a*(j.REMAINDERS[4 if all_four else min(t-1,4)]+tail)for t,a in ints.items()))
 return{**old,'highest_selected_label':4,'head':h,'increments':inc,'constants':(const,const)}
records={(name,all4):prepared(tail,all4)for name,tail in tails.items()for all4 in(False,True)}
def rational(lay,first,second,tail,all4,theta):
 load=head.bridge.head_load(lay);pre,caps,e,w=j.source_tables(theta);fw=[v for row in w for v in row]
 f=lambda t,i,v:fw[i]*max(v-t,0)+depth.seven_increment(t,v,first[i],second[i])
 z=[sum(a*f(t,i,b)for t,a in co.items())for i,b in enumerate(load)];val=j.raw_source_lp(z,theta)
 def op(arr,step):
  if step in(2,4):return max(sum(pre[c][s]*arr[5*c+s]for s in range(5))for c in range(5))/(27 if step==2 else 81)
  if step==1:return max(sum(e[c][s]*arr[5*c+s]for c in range(5))for s in range(5))/25
  return max(sum(e[c][s]*arr[5*c+s]for c in range(5)if j.ROOT[c]==r)for r,s in product(range(2),range(5)))/25
 for step in range(1,5):
  levels=[[sum(a*(f(t,i,b+k+1)-f(t,i,b+k))for t,a in co.items()if(4 if all4 else min(t-1,4))>=step)for i,b in enumerate(load)]for k in range(step)];hi=levels[-1];choices=[op(hi,step)]
  if step in(2,3):
   lo=levels[-2];choices.append(op(lo,step)+max(h-l for h,l in zip(hi,lo))/675)
  if step==4:
   lo,mid=levels[1:3];choices +=[op(lo,step)+max(max(2*(m-l),h-l)for l,m,h in zip(lo,mid,hi))/2025,op(mid,step)+max(h-m for h,m in zip(hi,mid))/2025]
  val+=min(choices)
 H=[sum(a*max(b-t,0)for t,a in co.items())for b in load]
 return val-sum(j.deletion_correction(H))+sum(a*(j.REMAINDERS[4 if all4 else min(t-1,4)]+tail)for t,a in co.items())
checks=0
for lay in((1,4,4,1,4,4,4),(0,1,2,0,2,1,2)):
 load=head.bridge.head_load(lay);cor=head.correction(old,load)
 for name,first,sec in[('two',tuple(int(j.ROOT[c]==1)+int(s==4)for c,s in product(range(5),repeat=2)),(0,)*25),('eight',tuple(int(j.ROOT[c]==1)+int(s==4)+int(c==3)+int(j.ROOT[c]==1 and s==2)for c,s in product(range(5),repeat=2)),tuple(int(j.ROOT[c]==0)+int(s==2)+int(c==4)+int(j.ROOT[c]==1 and s==4)for c,s in product(range(5),repeat=2)))]:
  for all4 in(False,True):
   vals=head.objective(records[name,all4],load,tuple(zip(first,sec)),cor,True)
   for theta,z in zip((j.LO,j.HI),vals):require(scale*z==rational(lay,first,sec,tails[name],all4,theta),'Independent new-prefix Fraction compiler check');checks+=1
TARGET=F(args.target);threshold=TARGET/scale;start=time.monotonic();counts={k:0 for k in('layouts','two_seen','two_closed','four_seen','four_closed','six_seen','six_closed','seven_seen','seven_closed','eight_seen','eight_closed','remaining')};remaining=[];max_pruned={};digest=sha256()
def bounded(lines):
 v,x,_=trip.max_min_affines(lines);return v<=threshold,v,x
def mark(kind,record,v):
 counts[kind+'_closed']+=1;max_pruned[kind]=max(max_pruned.get(kind,F(0)),scale*v);digest.update(repr((kind,record,v)).encode())
def lines(name,load,first,sec,cor):return tuple(head.objective(records[name,a],load,tuple(zip(first,sec)),cor,True)for a in(False,True))
zero=(0,)*25
for il,lay in enumerate(j.layouts()):
 counts['layouts']+=1;load=head.bridge.head_load(lay);cor=head.correction(old,load)
 for r,s,ex in head.extras:
  counts['two_seen']+=1;two=lines('two',load,ex,zero,cor);ok,v,x=bounded(two)
  if ok:mark('two',(lay,r,s),v);continue
  for c63,r105,s105,added in head.added:
   counts['four_seen']+=1;first=tuple(a+b for a,b in zip(ex,added));four=two+lines('four',load,first,zero,cor);ok,v,x=bounded(four);pr=(r,s,c63,r105,s105)
   if ok:mark('four',(lay,pr),v);continue
   for r147,s245,sec in head.extras:
    counts['six_seen']+=1;six=four+lines('six',load,first,sec,cor);ok,v,x=bounded(six);pr6=pr+(r147,s245)
    if ok:mark('six',(lay,pr6),v);continue
    for c441 in range(5):
     counts['seven_seen']+=1;sec7=tuple(a+int(c==c441)for a,(c,k)in zip(sec,product(range(5),repeat=2)));seven=six+lines('seven',load,first,sec7,cor);ok,v,x=bounded(seven)
     if ok:mark('seven',(lay,pr6,c441),v);continue
     for r735,s735 in product(range(2),range(5)):
      counts['eight_seen']+=1;sec8=tuple(a+int(j.ROOT[c]==r735 and k==s735)for a,(c,k)in zip(sec7,product(range(5),repeat=2)));eight=seven+lines('eight',load,first,sec8,cor);ok,v,x=bounded(eight);new=(c441,r735,s735)
      if ok:mark('eight',(lay,pr6,new),v);continue
      counts['remaining']+=1;remaining.append({'layout':lay,'projection':pr6,'projection441_735':new,'new_complete_affine_upper':scale*v,'maximizing_theta_coordinate':x});digest.update(repr(('remaining',lay,pr6,new,v)).encode())
 if il%2500==0:print('NEW375 PREFIX',il,'eight',counts['eight_seen'],'remaining',counts['remaining'],'seconds',round(time.monotonic()-start,2),flush=True)
require(counts['two_seen']==125000 and counts['four_seen']==50*(counts['two_seen']-counts['two_closed'])and counts['six_seen']==10*(counts['four_seen']-counts['four_closed'])and counts['seven_seen']==5*(counts['six_seen']-counts['six_closed'])and counts['eight_seen']==10*(counts['seven_seen']-counts['seven_closed']),'All independent child branches covered')
covered=25000*counts['two_closed']+500*counts['four_closed']+50*counts['six_closed']+10*counts['seven_closed']+counts['eight_closed']+counts['remaining'];require(covered==3125000000,'Complete original3.125b source domain')
out={'schema':'erdos7-aligned-retained375-prefix-v1','name':args.name,'target_scheduling_upper':TARGET,'coefficients':co,'counts':counts,'maximum_pruned_bounds':max_pruned,'covered_containing_choices':covered,'fractional_compiler_checks':checks,'complete_positive7_tails':tails,'source_theta':[j.LO,j.HI],'source_omission_support':j.SUPPORT,'remaining_leaf_batches':[{'start':i,'stop':min(i+100,len(remaining)),'rows':remaining[i:i+100]}for i in range(0,len(remaining),100)],'scan_sha256':digest.hexdigest(),'scope':'Every source branch covered by a newly recomputed complete affine bound <=target or a listed unresolved leaf. No old saturated numerical bound/dual consumed. A universal target needs every remaining leaf closed.'}
if args.write:io.write_certificate_text(args.certificate,json.dumps(p.encode(out),indent=2)+'\n')
else:require(p.encode(out)==read(args.certificate),'Complete new-source prefix independently regenerates')
print('PASS NEW375 PREFIX complete',covered,'remaining',len(remaining),'seconds',round(time.monotonic()-start,2),flush=True)
