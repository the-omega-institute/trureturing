"""Verify one-anchor normalized-kernel pair bound with exact arithmetic.

Report482. Run from the repository root. Source data and the support
certificate are checked using only the Python standard library. The ordinary
proof supplies the source construction and the original-family transfer.
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
REFS=(17,25)

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
 return x%3!=0 and x%9!=1 and x!=4 and y%5!=0 and y!=1 and not(x%3==2 and y%5==2) and not(x%9==4 and y%5==1) and not(x%3==1 and y==16)

ROOTKEYS=tuple((u,k) for u in range(2,13) for k in range(1,38//u+1))

@lru_cache(None)
def coordinate(p,height,ref,factor,tail=False):
 return tuple(shell(p,height,ref,r,factor,tail) for r in range(p**height))

@lru_cache(None)
def ternary_row(ref,u,tail=False):
 weights=coordinate(3,3,ref,u,tail)
 return tuple(sum(weights[x] for x in range(27) if x%3==ref%3 and allowed(x,y)) for y in range(25))

@lru_cache(None)
def anchor_at(ref,ref5,u,k,utail=False,ktail=False):
 return sum(a*b for a,b in zip(ternary_row(ref,u,utail),coordinate(5,2,ref5,k,ktail)))

def anchor(branch,u,k,utail=False,ktail=False):
 return anchor_at(REFS[branch],3,u,k,utail,ktail)

@lru_cache(None)
def initial_vector(ref,ref5):
 weights=tuple(anchor_at(ref,ref5,u,k) for u,k in ROOTKEYS)
 tail3=sum(ternary_row(ref,13,True),F())/25
 tail5=sum(anchor_at(ref,ref5,u,38//u+1,False,True) for u in range(2,13))
 expected=sum(allowed(x,y) for x in range(27) for y in range(25) if x%3==ref%3)/F(675)
 require(sum(weights,F())+tail3+tail5==expected,'initial valuation partition conserves mass')
 return weights,tail3+tail5

def anchor_identity_checks():
 original=((0,3),(1,9),(4,27),(0,5),(1,25),(2,15),(31,45),(16,75))
 count=0
 for n in range(675):
  ok=all(n%m!=a for a,m in original)
  require(ok==allowed(n%27,n%25),'literal original anchor membership')
  count+=ok
 require(count==210,'eight-anchor survivor count')
 return count

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

def verify(certificate,identities):
 profiles=[(b,u,tuple(fs)) for b,u,fs in certificate['profiles']]
 require(len(profiles)==len(set(profiles)),'duplicate profile')
 lookup={p:1<<i for i,p in enumerate(profiles)}
 tree=certificate['tree']
 tail3=sum(anchor(b,13,k,True,k==20) for b in (0,1) for k in range(1,21))
 tail5=sum(anchor(b,u,38//u+1,False,True) for b in (0,1) for u in range(2,13))
 require(tail3==F(32,13286025),'ternary tail')
 require(tail5==F(33008533907464,10136432647705078125),'quinary tail')
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
 roots=[];root_records=[]
 for b in (0,1):
  for u in range(2,13):
   for k in range(1,38//u+1):
    w=anchor(b,u,k)
    if w:
     node=descend(b,u,(k,),0);roots.append((node,w));root_records.append((b,u,k,node))
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
 def upper(mask):return tail3+tail5+sum(w*value(i,mask&masks[i]) for i,w in roots)
 def indices(mask):
  out=[]
  while mask:
   one=mask&-mask;out.append(one.bit_length()-1);mask-=one
  return out
 visited=set();leaves=[];leaf_masks=[];edgechecks=0;mink=F(10000)
 def visit(i,mask):
  nonlocal edgechecks,mink
  require(i not in visited,'cycle or shared child');visited.add(i);node=tree[i]
  require(int(node['mask'],16)==mask,'child deletion mismatch')
  bound=upper(mask)
  require(bound==F(node['upper']),'recorded bound mismatch')
  if node.get('leaf'):
   require(bound<M7,'leaf does not beat m7');leaves.append(bound);leaf_masks.append(mask);return
  aa=int(node['branchA'],16);bb=int(node['branchB'],16)
  require(aa and bb and not(aa&bb) and not(mask&(aa|bb)),'invalid branching groups')
  for a in indices(aa):
   for b in indices(bb):
    edgevalue=pair_numerator(profiles[a],profiles[b]);require(edgevalue>0,'uncertified branch edge');mink=min(mink,edgevalue);edgechecks+=1
  visit(node['left'],mask|aa);visit(node['right'],mask|bb)
 visit(0,0)
 require(visited==set(range(len(tree))),'unreachable certificate nodes')
 require(not certificate.get('pending'),'pending branches')
 worst=max(leaves)
 # The support disjunctions and conditional rows do not depend on the
 # references' shallow positions. Re-evaluate all terminal support cases
 # against every exact initial weight vector, keeping one common5 reference.
 require([(b,u,k) for b,u,k,i in root_records]==[(b,u,k) for b in (0,1) for u,k in ROOTKEYS],'all possible initial roots generated')
 payoffs=[[value(i,mask&masks[i]) for b,u,k,i in root_records] for mask in leaf_masks]
 signatures={};configurations=0
 for a in range(2,27,3):
  for b in range(1,27,3):
   for z in range(25):
    wa,ta=initial_vector(a,z);wb,tb=initial_vector(b,z)
    key=(wa+wb,ta+tb)
    if key not in signatures:signatures[key]=[0,(a,b,z)]
    signatures[key][0]+=1;configurations+=1
 require(configurations==2025 and len(signatures)==24,'complete reference-prefix partition')
 prefix_results=[]
 for (weights,free),(count,representative) in signatures.items():
  bound=max(free+sum(w*v for w,v in zip(weights,row)) for row in payoffs)
  require(bound<=worst,'same upper bound at every reference prefix')
  prefix_results.append({'representative':list(representative),'configuration_count':count,'worst_upper':str(bound)})
 anchor_count=anchor_identity_checks()
 gap=M7-worst
 require(worst<F(16079741,1000000000)<M7,'readable upper gap')
 out={'scope':'Eight fixed shallow original anchors; all2025 opposite surviving ternary-root reference prefixes with a common nonternary reference at actual old-cofactor precisions; no deep pure3/5 exclusion; normalized full-history capped kernels; support avoids the certificate-used pair edges.',
      'verified':True,'certificate_nodes':len(tree),'accepted_leaves':len(leaves),'checked_cross_edges':edgechecks,'minimum_used_pair_numerator':str(mink),'profiles':len(profiles),'normalized_tree_rows':sum(node[0]=='row' for node in desc.values()),'worst_upper':str(worst),'worst_upper_float':float(worst),'m7':str(M7),'strict_gap':str(gap),'strict_gap_float':float(gap),'ternary_free_upper':str(tail3),'quinary_initial_high_load_mass':str(tail5),'inputs':identities,'anchor_survivors_mod675':anchor_count,'center_prefix_configurations':configurations,'initial_weight_signatures':len(signatures),'exact_prefix_leaf_evaluations':len(signatures)*len(leaves),'prefix_results':prefix_results,'original_family_Haar_lower':str(gap*mink/F(16632)),'original_family_Haar_lower_float':float(gap*mink/F(16632)),
      'boundary':'The ordinary proof supplies the stated restricted original-family consumer. This finite checker does not establish the source construction, quantify over all anchor layouts or prove the cited same-root reduction, rerun Lean, or solve unrestricted Erdos7.'}
 require(mink==F(4,3),'minimum used edge numerator')
 require(gap*mink/F(16632)>F(1,80000000000),'strict original Haar floor')
 return out
if __name__=='__main__':
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--certificate',type=Path,default=Path(__file__).with_name('fixed_anchor_two_fibre_certificate.json'))
 parser.add_argument('--input-dir',type=Path,default=Path('docs/reports/erdos7-odd-covering/frontier/cover-geometry'))
 parser.add_argument('--output',type=Path)
 args=parser.parse_args();identities=source_inputs(args.input_dir)
 result=verify(json.loads(args.certificate.read_text()),identities)
 text=json.dumps(result,indent=2)+'\n'
 if args.output:
  args.output.write_text(text)
 else:
  retained=Path(__file__).with_name('fixed_anchor_two_fibre.json')
  require(json.loads(retained.read_text())==result,'retained result differs from exact replay')
  print(text,end='')
