"""Exact replay of all legal shallow45/75 phases and all ternary centres.

Run beside the report482 verifier and its fixed_anchor_two_fibre_certificate.json,
or supply --input-dir. Uses only the Python standard library and the existing
report482 pair/source routines. Every one of561*2025 literal configurations is
included; no orbit table or group-transport hypothesis is used in this replay.
The ordinary proof supplies the common-source and original-family transfer.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import prod,lcm
from pathlib import Path
import argparse,hashlib,importlib.util,json

BASE_SHA='4f55fb3cef56f46c3e65f20e62abb274db6a6077de33e0e815ac51a2f3a7083e'
PATCH_SHA='abad64d74d67c4e2e48104d2ac502c71a666bd5ce08182990dc65e89ec75a846'
BASIC=((3,0),(9,1),(27,4),(5,0),(25,1),(15,2))
CAPS=((7,F(3,2)),(11,F(5,3)),(13,F(3,2)),(17,F(2)),(19,F(9,5)))
M7=F(7235955529,450000000000)
TARGET=F(13530362084729802525722239237409731006113773442855176051085643442,
         841453987724678813030011126035327051417778569660355684928876953125)
ROOTKEYS=tuple((u,k) for u in range(2,13) for k in range(1,38//u+1))
D3=3**12;D5=5**19;W=D3*D5
CRT={(x,y):next(k for k in range(x,675,27) if k%25==y)
     for x in range(27) for y in range(25)}

def require(ok,message):
 if not ok:raise ValueError(message)

def load_previous(input_dir):
 path=input_dir/'fixed_anchor_two_fibre.py'
 spec=importlib.util.spec_from_file_location('fixed_anchor_two_fibre',path)
 previous=importlib.util.module_from_spec(spec);spec.loader.exec_module(previous)
 require(previous.CAPS==CAPS and previous.M7==M7 and previous.ROOTKEYS==ROOTKEYS,'previous source parameters')
 return previous

def read_checked(path,digest):
 raw=path.read_bytes();require(hashlib.sha256(raw).hexdigest()==digest,'file identity '+path.name)
 return json.loads(raw)

def patched_tree(certificate,patch):
 require(patch['base_certificate_sha256']==BASE_SHA,'patch source identity')
 tree=certificate['tree'];require(len(tree)==3501 and not certificate['pending'],'base tree shape')
 replacements=patch['replacements'];require(len(replacements)==2,'two patch roots')
 seen=set()
 for entry in replacements:
  i=entry['tree_node'];require(i not in seen,'duplicate patch root');seen.add(i)
  require(tree[i].get('leaf') and tree[i]['mask']==entry['mask'],'patch replaces matching old leaf')
  mask=int(entry['mask'],16);A=int(entry['branchA'],16);B=int(entry['branchB'],16)
  require(A and B and not(A&B) and not(mask&(A|B)),'valid patch split')
  left=len(tree);right=left+1
  tree[i]={'mask':hex(mask),'branchA':hex(A),'branchB':hex(B),'left':left,'right':right}
  tree.extend([{'mask':hex(mask|A),'leaf':True},{'mask':hex(mask|B),'leaf':True}])
 require(seen=={2245,2354} and len(tree)==3505,'expected patch positions')
 return certificate

def indices(mask):
 while mask:
  one=mask&-mask;yield one.bit_length()-1;mask-=one

def build_payoffs(certificate,previous):
 profiles=[(b,u,tuple(fs)) for b,u,fs in certificate['profiles']]
 require(len(profiles)==2282 and len(profiles)==len(set(profiles)),'profile count/uniqueness')
 lookup={p:1<<i for i,p in enumerate(profiles)};tree=certificate['tree'];seen=set();leaves=[]
 edges=0;minK=None
 def walk(i,mask):
  nonlocal edges,minK
  require(0<=i<len(tree) and i not in seen,'invalid child/cycle/reused node')
  seen.add(i);node=tree[i];require(int(node['mask'],16)==mask,'child support mask')
  if node.get('leaf'):leaves.append((i,mask));return
  A=int(node['branchA'],16);B=int(node['branchB'],16)
  require(A and B and not(A&B) and not(mask&(A|B)) and (A|B)>>len(profiles)==0,'valid support split')
  for a in indices(A):
   for b in indices(B):
    K=previous.pair_numerator(profiles[a],profiles[b]);require(K>=F(4,3),'branch edge threshold')
    minK=K if minK is None else min(minK,K);edges+=1
  walk(node['left'],mask|A);walk(node['right'],mask|B)
 walk(0,0)
 require(len(seen)==len(tree)==3505 and len(leaves)==1753 and not certificate['pending'],'complete tree')
 used=set()
 @lru_cache(None)
 def build(b,u,fs):
  load=u*prod(fs);stage=len(fs)-1
  if stage==5:
   if load<20:return ('safe',)
   key=(b,u,fs);require(key in lookup,'missing positive profile')
   used.add(key);return ('leaf',lookup[key])
  p,C=CAPS[stage];last=38//load
  return ('row',tuple((build(b,u,fs+(j,)),min(F(1),C*F(p-1,p**j)))
                      for j in range(1,last+1)),min(F(1),C*F(1,p**last)))
 roots=[[build(b,u,(k,)) for u,k in ROOTKEYS] for b in (0,1)]
 require(used==set(profiles),'complete positive profile universe')
 @lru_cache(None)
 def below(node):
  if node[0]=='safe':return 0
  if node[0]=='leaf':return node[1]
  mask=0
  for child,c in node[1]:mask|=below(child)
  return mask
 @lru_cache(None)
 def payoff(node,mask):
  if node[0]=='safe':return F()
  if node[0]=='leaf':return F(0 if mask else 1)
  row=[(payoff(ch,mask&below(ch)),c) for ch,c in node[1]]+[(F(1),node[2])]
  row.sort(reverse=True);remaining=F(1);value=F()
  for v,c in row:
   take=min(c,remaining);value+=take*v;remaining-=take
   if remaining==0:break
  require(remaining==0,'normalized conditional row')
  return value
 values=[tuple(payoff(node,mask&below(node)) for b in (0,1) for node in roots[b])
         for idx,mask in leaves]
 denominator=lcm(*(v.denominator for row in values for v in row))
 integers=[tuple(v.numerator*(denominator//v.denominator) for v in row) for row in values]
 return leaves,integers,denominator,edges,minK

def all_weight_classes(previous):
 legal45=[r for r in range(45) if r%3!=0 and r%9!=1 and r%5!=0 and r%15!=2]
 legal75=[r for r in range(75) if r%3!=0 and r%5!=0 and r%25!=1 and r%15!=2]
 require(len(legal45)==17 and len(legal75)==33,'all legal shallow phases')
 @lru_cache(None)
 def coordinate(p,height,ref,factor,tail=False):
  raw=previous.coordinate(p,height,ref,factor,tail);D=D3 if p==3 else D5
  require(all(D%v.denominator==0 for v in raw),'coordinate denominator')
  return tuple(v.numerator*(D//v.denominator) for v in raw)
 @lru_cache(None)
 def vector(T,z):
  weights=tuple(sum(a*b for a,b in zip(T[u-2],coordinate(5,2,z,k))) for u,k in ROOTKEYS)
  require(sum(T[-1])*D5%25==0,'ternary tail denominator')
  tail3=sum(T[-1])*D5//25
  tail5=sum(sum(a*b for a,b in zip(T[u-2],coordinate(5,2,z,38//u+1,True))) for u in range(2,13))
  return weights,tail3+tail5
 classes={};counts=[];first=[];phase_counts=[]
 for r45,r75 in product(legal45,legal75):
  anchors=BASIC+((45,r45),(75,r75))
  G=tuple(tuple(all(CRT[x,y]%m!=r for m,r in anchors) for y in range(25)) for x in range(27))
  branch={}
  for ref in (*range(2,27,3),*range(1,27,3)):
   T=tuple(tuple(sum(coordinate(3,3,ref,u,u==13)[x]
                     for x in range(27) if x%3==ref%3 and G[x][y])
                 for y in range(25)) for u in range(2,14))
   cells=sum(G[x][y] for x in range(27) for y in range(25) if x%3==ref%3)
   require(cells*W%675==0,'anchor mass denominator')
   expected=cells*W//675
   for z in range(25):
    v=vector(T,z);require(sum(v[0])+v[1]==expected,'initial partition conserves literal anchor mass')
    branch[ref,z]=v
  local=set()
  for a,b,z in product(range(2,27,3),range(1,27,3),range(25)):
   va,ta=branch[a,z];vb,tb=branch[b,z];v=(va+vb,ta+tb)
   if v not in classes:
    classes[v]=len(classes);counts.append(0);first.append([r45,r75,a,b,z])
   idx=classes[v];counts[idx]+=1;local.add(idx)
  phase_counts.append(len(local))
 require(sum(counts)==17*33*9*9*25==1136025,'all literal phase and centre configurations')
 require(len(classes)==912,'initial weight partition')
 return classes,counts,first,legal45,legal75,phase_counts

def verify(input_dir,patch_path):
 previous=load_previous(input_dir);identities=previous.source_inputs(input_dir)
 certificate=read_checked(input_dir/'fixed_anchor_two_fibre_certificate.json',BASE_SHA)
 patch=read_checked(patch_path,PATCH_SHA)
 certificate=patched_tree(certificate,patch)
 leaves,payoffs,L,edges,minK=build_payoffs(certificate,previous)
 classes,counts,first,legal45,legal75,phase_counts=all_weight_classes(previous)
 den=W*L;worst=F();worstrow=None;rows=[]
 for (weights,tail),idx in classes.items():
  # Each leaf is evaluated. Integer arithmetic is only exact denominator
  # clearing of the rational source weights and normalized row payoffs.
  values=[tail*L+sum(w*p for w,p in zip(weights,P)) for P in payoffs]
  top=max(values);j=values.index(top);upper=F(top,den)
  require(upper<=TARGET<M7,'uniform prescribed upper bound')
  row={'class':idx,'configurations':counts[idx],'first_configuration':first[idx],
       'maximum_upper':str(upper),'maximizing_tree_node':leaves[j][0]}
  rows.append(row)
  if upper>worst:worst=upper;worstrow=row
 require(worst==TARGET,'attained uniform target')
 gap=M7-worst;haar=gap*minK/F(16632)
 require(haar>F(1,80000000000),'prescribed positive original-family floor')
 return {'scope':'Fixed six basic anchor chart, every legal45/75 phase, all2025 opposite-root ternary and common quinary reference prefixes, arbitrary deeper reference digits, normalized full-history capped kernels, and all support-disjunction leaves. Other coarse source charts and original-family transport belong to the ordinary proof.',
  'verified':True,'base_certificate_sha256':BASE_SHA,'patch_sha256':PATCH_SHA,'source_inputs':identities,
  'legal45':legal45,'legal75':legal75,'phase_pairs':len(legal45)*len(legal75),'reference_prefixes_per_phase':2025,
  'literal_configurations':sum(counts),'weight_classes':len(classes),'profiles':len(certificate['profiles']),
  'certificate_nodes':len(certificate['tree']),'support_leaves':len(leaves),'checked_cross_edges':edges,
  'minimum_used_pair_numerator':str(minK),'exact_leaf_evaluations':len(classes)*len(leaves),
  'worst':worstrow,'worst_upper':str(worst),'worst_upper_float':float(worst),
  'm7':str(M7),'strict_gap':str(gap),'strict_gap_float':float(gap),
  'original_family_Haar_lower':str(haar),'original_family_Haar_lower_float':float(haar),
  'rows':rows,'boundary':'This exact arithmetic replay checks the stated finite support calculation. The common-source construction, arbitrary-depth reference transport, and transfer to an original family are ordinary proof premises; no new Lean kernel claim or unrestricted Erdos7 conclusion is made.'}

if __name__=='__main__':
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--input-dir',type=Path,default=Path(__file__).parent)
 parser.add_argument('--patch',type=Path,default=Path(__file__).with_name('all_ternary_two_fibre_patch.json'))
 parser.add_argument('--output',type=Path)
 args=parser.parse_args();result=verify(args.input_dir,args.patch)
 text=json.dumps(result,indent=2)+'\n'
 if args.output:args.output.write_text(text)
 else:
  retained=Path(__file__).with_name('all_ternary_two_fibre.json')
  require(json.loads(retained.read_text())==result,'retained result differs from exact replay')
  print(text,end='')
