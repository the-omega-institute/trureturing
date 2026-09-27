"""Verify arbitrary single-coordinate quinary choices with exact arithmetic.

Run from the repository root with --input-dir and --certificate overrides as needed.
The adjacent certificate and retained result are checked using the Python standard library only.
No SciPy, numerical LP solver, or other scratch helper is imported.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product,combinations
from math import prod
from pathlib import Path
import argparse,hashlib,json
CAPS=((7,F(3,2)),(11,F(5,3)),(13,F(3,2)),(17,F(2)),(19,F(9,5)))
M7=F(7235955529,450000000000)
REFS=(3,4)

def require(value,message):
 if not value:raise ValueError(message)

def valuation(n,p):
 require(n!=0,'valuation zero not finite')
 v=0
 while n%p==0:n//=p;v+=1
 return v

def shell(p,height,ref,residue,factor,tail=False):
 if residue==ref:
  if tail:return F(1,p**(factor-1)) if factor-1>=height else F(1,p**height)
  return F(p-1,p**factor) if factor-1>=height else F()
 v=valuation(residue-ref,p)
 if not(v+1>=factor if tail else v+1==factor):return F()
 w=F(1,p**height)
 return w

def allowed(x,y):
 return x%3!=0 and x%9!=1 and x!=4 and y%5!=0 and y!=1 and not(x%3==2 and y%5==2)

@lru_cache(None)
def anchor(branch,u,k,utail=False,ktail=False):
 ref=REFS[branch]
 return sum(shell(5,2,ref,y,u,utail)*shell(3,3,2,x,k,ktail) for x in range(27) for y in range(25) if y%5==ref%5 and allowed(x,y))

def other_roots_bad():
 from collections import defaultdict
 dist={1:F(1)}
 for p,c in CAPS:
  w={1:1-c/p,**{f:c*F(p-1,p**f) for f in range(2,20)},20:c/F(p**19)}
  require(all(v>=0 for v in w.values()) and sum(w.values())==1,'other-root local law')
  out=defaultdict(F)
  for a,wa in dist.items():
   for b,wb in w.items():out[min(20,a*b)]+=wa*wb
  require(sum(out.values())==1,'other-root convolution mass')
  dist=dict(out)
 payoff={k:sum(w for f,w in dist.items() if k*f>=20) for k in range(1,21)}
 require(all(payoff[k]<=payoff[k+1] for k in range(1,20)),'other-root monotonicity')
 weights={k:sum(shell(3,3,2,x,k,k==20)*F(1,25) for x in range(27) for y in range(25) if y%5 not in tuple(r%5 for r in REFS) and allowed(x,y)) for k in range(1,21)}
 require(sum(weights.values())==(F(3,25) if REFS==(3,4) else F(19,135)),'other-root initial mass')
 return sum(weights[k]*payoff[k] for k in weights)

def setup(qx, qy, N):
    require(min(qx,qy,N)>=0, 'nonnegative capacities')
    ax,ay,bx,by = min(22,qx),min(22,qy),min(28,qx),min(28,qy)
    A,B,G = min(N,ax+ay),min(N,bx+by),min(N,qx+qy)
    rectangle = (max(0,A-ay),min(ax,A),max(0,B-by),min(bx,B))
    def residuals(t,u):
        return F((22-t)*(28-u)), F((22-A+t)*(28-B+u))
    def entries(t,u):
        rx,ry = residuals(t,u)
        return F(0),rx-qx,ry-qy,rx+ry-G
    return A,B,G,rectangle,residuals,entries

def solve(qx,qy,N):
    A,B,G,(tl,th,ul,uh),residuals,entries = setup(qx,qy,N)
    points = {}
    edges = (((tl,ul),(th,ul)),((th,ul),(th,uh)),
             ((th,uh),(tl,uh)),((tl,uh),(tl,ul)))
    for p0,p1 in edges:
        left,right = entries(*p0),entries(*p1)
        parameters = {F(0),F(1)}
        for i,j in combinations(range(4),2):
            slope = (right[i]-left[i])-(right[j]-left[j])
            if slope:
                z = (left[j]-left[i])/slope
                if 0<=z<=1:
                    parameters.add(z)
        for z in parameters:
            t = F(p0[0])+z*(p1[0]-p0[0])
            u = F(p0[1])+z*(p1[1]-p0[1])
            points[t,u] = max(entries(t,u))
    require(len(points)<=28,'candidate count')
    K = min(points.values())
    old = max(F(0),min(sum(residuals(t,u))-G
                      for t,u in product((tl,th),(ul,uh))))
    corner = min(max(entries(t,u)) for t,u in product((tl,th),(ul,uh)))
    return dict(K=K,minimizers=sorted(p for p,v in points.items() if v==K),
                candidate_count=len(points),old_K=old,corner_K=corner)

@lru_cache(None)
def mixed_pair(qx,qy,n):
 if qx>qy:return mixed_pair(qy,qx,n)
 return solve(qx,qy,n)['K']

def pair_numerator(px,py):
 branchx,ux,fs=px;branchy,uy,gs=py
 require(branchx!=branchy,'pair must cross roots')
 qx=ux*prod(fs);qy=uy*prod(gs)
 n=qx+qy-min(ux-1,uy-1)*prod(min(f,g) for f,g in zip(fs,gs))
 return mixed_pair(qx,qy,n)


def source_inputs(input_dir):
 expected={
  'query_stoploss_completion.json':'44f871684942eb7dceb37c55880c9f9a49244d8bdd60134670ad80d10a3c587d',
  'common_law_mass_tail.json':'3781704377f2ca6234ed55f3eff1a37d2f8665a3810b02c694aebdc2fc063cb4'}
 data={}
 for name,digest in expected.items():
  raw=(input_dir/name).read_bytes();require(hashlib.sha256(raw).hexdigest()==digest,'source identity '+name);data[name]=json.loads(raw)
 prefix=data['query_stoploss_completion.json'];common=data['common_law_mass_tail.json']['common_seven_core_law']
 require(len(prefix['rows'])==32,'source vertex count')
 actual_min=min(F(row['cores']['7']['live_mass_lower_cell_units'])/135 for row in prefix['rows'])
 require(actual_min==M7==F(common['unnormalized_mass_lower']),'same source lower mass')
 require(tuple(F(x) for x in common['conditional_caps'])==tuple(c for p,c in CAPS),'source conditional caps')
 require(F(common['unnormalized_joint_density_cap'])==F(27,2),'source density cap')
 return expected

def verify(certificate,identities,recorded=True):
 profiles=[(b,u,tuple(fs)) for b,u,fs in certificate['profiles']]
 require(len(profiles)==len(set(profiles)),'duplicate profile')
 lookup={p:1<<i for i,p in enumerate(profiles)}
 tree=certificate['tree']
 tail3=sum(anchor(b,11,k,True,k==20) for b in (0,1) for k in range(1,21))
 tail5=sum(anchor(b,u,38//u+1,False,True) for b in (0,1) for u in range(2,11))
 extra=other_roots_bad()
 require(tail3==F(28,263671875) and tail5>0,'all exact positive initial tails retained')
 # Generate a fresh tree directly from prime valuation cylinders, without the LP.
 desc={}
 def descend(branch,u,fs,stage):
  key=(branch,u,fs);load=u*prod(fs)
  if stage==len(CAPS):
   node=('leaf',lookup[key]) if load>=20 else ('safe',)
  else:
   p,c=CAPS[stage];upto=38//load
   children=[]
   for f in range(1,upto+1):
    ch=descend(branch,u,fs+(f,),stage+1)
    children.append((ch,min(F(1),c*F(p-1,p**f))))
   tailcap=min(F(1),c*F(1,p**upto))
   node=('row',tuple(children),tailcap)
  i=len(desc);desc[i]=node;return i
 roots=[]
 for b in (0,1):
  for u in range(2,11):
   for k in range(1,38//u+1):
    w=anchor(b,u,k)
    if w:roots.append((descend(b,u,(k,),0),w))
 used={node[1] for node in desc.values() if node[0]=='leaf'}
 require(used==set(lookup.values()),'certificate profiles differ from generated leaves')
 masks={}
 def below(i):
  node=desc[i]
  if node[0]=='leaf':v=node[1]
  elif node[0]=='safe':v=0
  else:
   v=0
   for ch,c in node[1]:v|=below(ch)
  masks[i]=v;return v
 for i,w in roots:below(i)
 @lru_cache(None)
 def value(i,mask):
  node=desc[i]
  if node[0]=='leaf':return F(0 if mask else 1)
  if node[0]=='safe':return F()
  entries=[(value(ch,mask&masks[ch]),cap) for ch,cap in node[1]]+[(F(1),node[2])]
  require(sum(cap for v,cap in entries)>=1,'row capacities cannot normalize')
  entries.sort(reverse=True);rem=F(1);ans=F()
  for v,cap in entries:
   take=min(rem,cap);ans+=take*v;rem-=take
   if not rem:break
  require(rem==0,'row mass not allocated')
  return ans
 def upper(mask):return extra+tail3+tail5+sum(w*value(i,mask&masks[i]) for i,w in roots)
 def indices(mask):
  out=[]
  while mask:
   one=mask&-mask;out.append(one.bit_length()-1);mask-=one
  return out
 visited=set();leaves=[];edgechecks=0;mink=F(10000)
 def visit(i,mask):
  nonlocal edgechecks,mink
  require(i not in visited,'cycle or shared child');visited.add(i);node=tree[i]
  require(int(node['mask'],16)==mask,'child deletion mismatch')
  bound=upper(mask)
  if recorded:require(bound==F(node['upper']),'recorded bound mismatch')
  if node.get('leaf'):
   require(bound<M7,'leaf does not beat m7');leaves.append(bound);return
  aa=int(node['branchA'],16);bb=int(node['branchB'],16)
  require(aa and bb and not(aa&bb) and not(mask&(aa|bb)),'invalid branching groups')
  for a in indices(aa):
   for b in indices(bb):
    edgevalue=pair_numerator(profiles[a],profiles[b]);require(edgevalue>0,'uncertified branch edge');mink=min(mink,edgevalue);edgechecks+=1
  visit(node['left'],mask|aa);visit(node['right'],mask|bb)
 visit(0,0)
 require(visited==set(range(len(tree))),'unreachable certificate nodes')
 require(not certificate.get('pending'),'pending branches')
 require(mink>=F(4,3),'every used pair supports threshold1/924')
 worst=max(leaves);gap=M7-worst
 require(worst<F(16078324,1000000000)<M7,'readable upper gap')
 out={'scope':f'Only six shallow anchor exclusions; common3=2 mod27 and two5 prefixes{REFS} mod25; no deep pure3/5 subtraction; all normalized capped later kernels; other5-root BAD fully paid; BAD and absence of certified individual-mixed-budget pairs.',
      'verified':True,'certificate_nodes':len(tree),'accepted_leaves':len(leaves),'checked_cross_edges':edgechecks,'minimum_used_pair_numerator':str(mink),'profiles':len(profiles),'normalized_tree_rows':sum(node[0]=='row' for node in desc.values()),'worst_upper':str(worst),'worst_upper_float':float(worst),'m7':str(M7),'strict_gap':str(gap),'strict_gap_float':float(gap),'quinary_exceptional_tail_upper':str(tail3),'ternary_initial_high_load_mass':str(tail5),'other5_root_BAD_upper':str(extra),'other5_root_BAD_upper_float':float(extra),'inputs':identities,'original_family_Haar_lower':str(gap*mink/F(16632)),'original_family_Haar_lower_float':float(gap*mink/F(16632)),
      'boundary':'The ordinary proof supplies the stated restricted original-family consumer. This finite checker does not establish the source construction, quantify over all anchor layouts, rerun Lean, or solve unrestricted Erdos7.'}
 require(gap*mink/F(16632)>F(1,8000000000),'readable original-family Haar floor')
 return out

def later_bad_payoff():
 from collections import defaultdict
 dist={1:F(1)}
 for p,c in CAPS:
  law={1:1-c/p,**{f:c*F(p-1,p**f) for f in range(2,20)},20:c/F(p**19)}
  nxt=defaultdict(F)
  for a,w in dist.items():
   for b,v in law.items():nxt[min(20,a*b)]+=w*v
  require(sum(nxt.values())==1,'all later comparison mass retained');dist=dict(nxt)
 return {k:sum(w for f,w in dist.items() if k*f>=20) for k in range(1,21)}

def dist_on_cells(p,height,refs,cells):
 """All refs are distinct modulo p, or there is one reference."""
 require(len(refs)==1 or len({r%p for r in refs})==len(refs),'separated local refs')
 out=[F() for _ in range(21)]
 for x in cells:
  if x in refs:
   for f in range(height+1,20):out[f]+=F(p-1,p**f)
   out[20]+=F(1,p**19)
  else:
   f=1+max(valuation(x-r,p) for r in refs)
   require(f<20,'visible finite factor');out[f]+=F(1,p**height)
 require(sum(out)==F(len(cells),p**height),'local cells retain exact mass')
 return tuple(out)

def all_prefixes():
 from itertools import combinations
 payoff=later_bad_payoff()
 cells3=([x for x in range(27) if x%3==1 and x%9!=1 and x!=4],[x for x in range(27) if x%3==2])
 cells5=([y for y in range(25) if y%5!=0 and y!=1],[y for y in range(25) if y%5 not in (0,2) and y!=1])
 ds3={a:tuple(dist_on_cells(3,3,(a,),cells) for cells in cells3) for a in range(27)}
 pairs=[(a,b) for a,b in combinations(range(25),2) if a%5!=b%5]
 ds5={ab:tuple(dist_on_cells(5,2,ab,cells) for cells in cells5) for ab in pairs}
 cache={};safe_max=F();unsafe_count=0;counts={};representative_data={}
 for refs in ((3,4),(3,6)):
  a3=ds3[2];d3=tuple(a+b for a,b in zip(*a3))
  d5=tuple(dist_on_cells(5,2,(r,),[y for y in range(25) if y%5==r%5 and y!=1]) for r in refs)
  remaining=[y for y in range(25) if y%5 not in (0,refs[0]%5,refs[1]%5) and y!=1]
  nV=len(remaining);nW=sum(y%5!=2 for y in remaining)
  other=tuple((nV*a3[0][k]+nW*a3[1][k])/25 for k in range(21))
  representative_data[refs]=(d3,d5,other)
 for ref3,a3 in ds3.items():
  for ab,a5 in ds5.items():
   sig=(a3,a5)
   if sig not in cache:
    cache[sig]=sum(a3[r][i]*a5[r][j]*payoff[min(20,i*j)] for r in (0,1) for i in range(1,21) for j in range(1,21))
   upper=cache[sig]
   geometric_bad=(ref3%3==2 and all(a%5 in (1,3,4) and a!=1 for a in ab))
   require((upper>=M7)==geometric_bad,'exact scalar failure partition')
   if not geometric_bad:safe_max=max(safe_max,upper);continue
   unsafe_count+=1
   ordered=tuple(sorted(ab,key=lambda a:(a%5==1,a%5)))
   cls=(3,6) if any(a%5==1 for a in ab) else (3,4)
   d3=tuple(a+b for a,b in zip(*a3))
   d5=tuple(dist_on_cells(5,2,(r,),[y for y in range(25) if y%5==r%5 and y!=1]) for r in ordered)
   remaining=[y for y in range(25) if y%5 not in (0,ordered[0]%5,ordered[1]%5) and y!=1]
   nV=len(remaining);nW=sum(y%5!=2 for y in remaining)
   other=tuple((nV*a3[0][k]+nW*a3[1][k])/25 for k in range(21))
   require((d3,d5,other)==representative_data[cls],'all unsafe prefixes have one of two exact row-weight vectors')
   counts[cls]=counts.get(cls,0)+1
 require(len(pairs)==250 and 27*len(pairs)==6750,'all unordered different-first-digit prefixes')
 require(unsafe_count==585 and sum(counts.values())==585,'all scalar unsafe positions')
 require(safe_max<F(313,20000),'uniform scalar safe bound')
 return {'raw_prefix_configurations':6750,'scalar_signature_count':len(cache),'scalar_safe_configurations':6750-unsafe_count,'scalar_unsafe_configurations':unsafe_count,'unsafe_reference_weight_class_counts':{str(k):v for k,v in counts.items()},'scalar_safe_maximum':str(safe_max),'scalar_safe_maximum_float':float(safe_max),'scalar_safe_strict_upper':'313/20000','all_unsafe_matching_root_and_other_root_weights_checked':True}

def pure_comparisons(input_dir):
 from collections import defaultdict
 prefix=json.loads((input_dir/'query_stoploss_completion.json').read_bytes())
 groups=defaultdict(list)
 for row in prefix['rows']:groups[tuple(row['node'][:3])].append(F(row['cores']['7']['live_mass_lower_cell_units'])/135)
 require(len(groups)==8 and all(len(v)==4 for v in groups.values()),'eight source groups')
 other_min=min(min(v) for k,v in groups.items() if k!=(2,4,1))
 require(other_min==F(5891133457,225000000000),'nonworst mass minimum')
 eps=F(1,2*3**12)+F(1,4*5**8);bounds={}
 for first_agrees in (True,False):
  dist={1:F(1)}
  for p in (3,5,7,11,13,17,19):
   mass=F(1,2) if p==3 else F(3,4) if p==5 else F(1)
   if p==3:tail=lambda j:F(1,3**j)
   elif p==5:tail=lambda j:F(1,5) if first_agrees and j==1 else F(2,5**j)
   else:tail=lambda j,p=p:dict(CAPS)[p]/p**j
   tails={0:mass,**{j:min(mass,tail(j)) for j in range(1,20)}}
   law={f:tails[f-1]-tails[f] for f in range(1,20)};law[20]=tails[19]
   require(all(w>=0 for w in law.values()) and sum(law.values())==mass,'pure comparison mass')
   nxt=defaultdict(F)
   for a,w in dist.items():
    for b,v in law.items():nxt[min(20,a*b)]+=w*v
   dist=dict(nxt)
  require(sum(dist.values())==F(3,8),'pure product mass')
  upper=dist[20]+eps
  require(upper<(M7 if first_agrees else other_min),'finite-prefix upper comparison clears the unchanged completed source mass')
  bounds[str(first_agrees)]={'ideal_BAD_upper':str(dist[20]),'released_pure_tail_upper':str(eps),'finite_prefix_BAD_upper':str(upper),'finite_prefix_BAD_upper_float':float(upper),'source_mass_lower':str(M7 if first_agrees else other_min),'GOOD_gap':str((M7 if first_agrees else other_min)-upper)}
 return bounds

if __name__=='__main__':
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--certificate',type=Path,default=Path(__file__).with_name('all_quinary_two_fibre_certificate.json'))
 parser.add_argument('--input-dir',type=Path,default=Path(__file__).parent);parser.add_argument('--output',type=Path)
 parser.add_argument('--expected',type=Path,default=Path(__file__).with_suffix('.json'))
 args=parser.parse_args();identities=source_inputs(args.input_dir)
 cert=json.loads(args.certificate.read_text());cases={}
 for refs in ((3,4),(3,6)):
  REFS=refs;anchor.cache_clear();cases[str(refs)]=verify(cert,identities,refs==(3,4))
 prefix_result=all_prefixes();pure_result=pure_comparisons(args.input_dir)
 uniform_upper=F(16078324,1000000000);gap=M7-uniform_upper;haar=gap/F(12474)
 require(all(F(case['worst_upper'])<uniform_upper for case in cases.values()),'two joint certificates share one strict upper')
 require(F(prefix_result['scalar_safe_strict_upper'])<uniform_upper,'all scalar safe cases clear the uniform upper')
 require(all(F(v['GOOD_gap'])/F(27,2)/77>haar for v in pure_result.values()),'pure source cases have larger original Haar margin')
 require(haar>F(1,8000000000),'uniform original Haar margin')
 out={'scope':'Every single-coordinate quinary disagreement, with fixed independent choices per complete original later label; no original shallow-anchor assumption, using the attributed fixed completed source and its coarse normalization. All6750 different-root shallow references checked, including deleted-root references; same-root and nonworst cases release only deeper pure exclusions in their upper comparisons, with explicit tail allowance; no lower bound is transferred to a truncated source.',
      'pair_cases':cases,'all_prefixes':prefix_result,'pure_comparisons':pure_result,'uniform_worst_source_T_strict_upper':str(uniform_upper),'uniform_original_Haar_strict_lower':str(haar),'readable_original_Haar_strict_lower':'1/8000000000','input_identities':identities,'certificate_sha256':hashlib.sha256(args.certificate.read_bytes()).hexdigest(),'source_producers_rerun':False,'Lean_rerun':False,'unrestricted_erdos7_resolved':False}
 encoded=json.dumps(out,indent=2)+'\n'
 if args.output:args.output.write_text(encoded)
 else:
  require(json.loads(args.expected.read_text())==out,'retained exact result mismatch')
  print('verified:6750 different-root prefixes;707-node pair certificate;uniform original Haar>1/8000000000')
