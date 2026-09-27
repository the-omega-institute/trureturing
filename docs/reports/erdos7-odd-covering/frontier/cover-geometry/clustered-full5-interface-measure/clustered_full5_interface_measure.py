#!/usr/bin/env python3
"""Exact size and support measurements for the fixed109 all-five interface; no optimizer."""
from pathlib import Path
from fractions import Fraction as F
from itertools import product,combinations
from math import prod
from hashlib import sha256
import json,argparse
ap=argparse.ArgumentParser();ap.add_argument('--base',type=Path,default=Path(__file__).resolve().parent.parent);ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'));args=ap.parse_args()
checks=0
def ck(test):
 global checks
 checks+=1
 if not test:raise RuntimeError('check '+str(checks))
Q=(7,11,13,17,19)
fix=json.loads((args.base/'clustered_global_phase_fixture.json').read_text());higher=json.loads((args.base/'clustered_higher_pure_capacity_obstruction.json').read_text());originals=fix['actual_originals'];added=higher['first_tested_success']['added_higher_pure_originals']
ck(len({o['modulus'] for o in originals+added})==109)
fixture_digest=sha256((args.base/'clustered_global_phase_fixture.json').read_bytes()).hexdigest()
ck(fixture_digest=='4bc215b032c910224a3a23ed76edaf1e32dc8e243fe5ba474e129a1cee63e6b6')
ck(higher['input_sha256']['clustered_global_phase_fixture.json']==fixture_digest)
ck(higher['first_tested_success']['n']==4 and higher['first_tested_success']['original_count']==109)
ck(len(originals)==101 and len(added)==8)
ck({(o['modulus'],o['residue']) for o in added}=={(27,4),(81,13),(243,40),(729,121),(125,2),(625,27),(3125,152),(15625,777)})
actual_capacities=[]
for prime,weak,weight,reference,expected_cap,expected_gamma in ((3,4,F(1,9),F(2),F(41,729),F(81,82)),(5,2,F(1,25),F(4,3),F(469,15625),F(1875,1876))):
 pure=[(o['modulus'],o['residue']) for o in added if o['modulus']%prime==0]
 depth=max(mod for mod,res in pure)
 remaining=sum(all(x%mod!=res for mod,res in pure) for x in range(weak,depth,prime*prime))
 cap=F(remaining,depth);gamma=weight/(cap*reference)
 ck(cap==expected_cap and cap>0)
 ck(gamma==expected_gamma)
 ck(F(higher['first_tested_success']['gamma'+str(prime)])==gamma)
 declared=next(c for c in higher['first_tested_success']['capacities'] if c['prime']==prime)
 ck(F(declared['haar_capacity'])==cap and F(declared['gamma'])==gamma and F(declared['weight'])==weight and F(declared['reference_density'])==reference and declared['weak_leaf_residue']==weak)
 actual_capacities.append(dict(prime=prime,weak_leaf_residue=weak,haar_capacity=str(cap),gamma=str(gamma)))
local=[[] for q in Q]
for o in originals:
 c=o['modulus'];b=o['residue'];qs=[]
 for i,q in enumerate(Q):
  if c%q==0:
   power=1
   while c%q==0:c//=q;power*=q
   qs.append((i,power))
 if len(qs)==1 and c>1:
  i,d=qs[0];local[i].append((c,b%c,d,b%d))
 if len(qs)==2:ck(all(b%Q[i]==1 for i,d in qs))
for i,j in combinations(range(5),2):ck(any(o['modulus']==Q[i]*Q[j] and o['residue']==1 for o in originals))
I=(0,1,2,4,5);J=tuple(m for m in range(20) if m!=5);cells=tuple((l,m) for l,m in product(I,J) if not(l<3 and m<5));ck(len(cells)==80)
catroots={q:[(1,), (1,)]+[(r,) for r in range(2,min(9,q))]+([(r for r in range(9,q))] if q>9 else []) for q in Q}
# Materialize the grouped free-root iterator explicitly.
for q in Q:catroots[q]=[tuple(r) for r in catroots[q]]
catcounts={};variables=0;physical_atoms=0;source=F(0);cellrows=[]
for l,m in cells:
 c=next(x for x in range(l//3+3*(l%3),225,9) if x%25==m//5+5*(m%5))
 rows=[];cnt=[]
 for i,q in enumerate(Q):
  atoms=[z for z in range(q*q) if z%q and all(c%cm!=cr or z%qm!=qr for cm,cr,qm,qr in local[i])]
  counts=[int(1 in atoms),sum(z%q==1 and z!=1 for z in atoms)]+[sum(z%q in rr for z in atoms) for rr in catroots[q][2:]]
  full=[1,q-1]+[q*len(rr) for rr in catroots[q][2:]]
  ck(sum(counts)==len(atoms));ck(all(n in (0,d) for n,d in zip(counts,full)))
  rows.append(atoms);cnt.append(counts)
 catcounts[l,m]=cnt
 av=[sum(n>0 for n in row[:2]) for row in cnt];bv=[sum(n>0 for n in row[2:]) for row in cnt]
 aa=[sum(row[:2]) for row in cnt];bb=[sum(row[2:]) for row in cnt]
 nv=prod(bv)+sum(av[i]*prod(bv[j] for j in range(5) if i!=j) for i in range(5))
 na=prod(bb)+sum(aa[i]*prod(bb[j] for j in range(5) if i!=j) for i in range(5))
 variables+=nv;physical_atoms+=na
 w=F(1,9) if l==4 else F(2,9);v=F(1,25) if m==10 else F(4,75)
 source+=w*v*F(na,prod(q*(q-1) for q in Q))
 cellrows.append(dict(cell=[l,m],active_category_counts=[sum(n>0 for n in row) for row in cnt],root1_categories=av,other_categories=bv,active_joint_categories=nv,active_joint_square_atoms=na))
ck(source==F(305684996597,646498195200))
# Central selector supports; their coefficients retain actual gamma3/5 but support counting only needs positivity.
def axis(live,level,block):
 if level==0:return [(0,set(live))]
 if level==1:return [(r,{i for i in live if i//block==r}) for r in range((max(live)//block)+1)]
 return [(i,{i}) for i in live]
selectors=[];smode=[]
for mode in range(16):
 e3,e5=divmod(mode,4);rr=[]
 for (i,ls),(j,ms) in product(axis(I,e3,3),axis(J,e5,5)):
  mask=sum(1<<k for k,(l,m) in enumerate(cells) if l in ls and m in ms)
  rr.append(mask);selectors.append((mode,i,j,mask))
 smode.append(rr)
ck(len(selectors)==559)
# Per-coordinate menu: whole, root1, one root query per non-root1 category, special child deep.
menus=[]
for iq,q in enumerate(Q):
 cc=catroots[q];opts=[('whole',False,tuple(range(len(cc)))) ,('root1',True,(0,1))]
 opts += [('root'+str(rr[0]),False,(k,)) for k,rr in enumerate(cc) if k>=2]
 opts += [('special_deep',True,(0,))]
 items=[]
 for label,one,inds in opts:
  amask=sum(1<<k for k,c in enumerate(cells) if any(catcounts[c][iq][t] for t in inds if t<2))
  bmask=sum(1<<k for k,c in enumerate(cells) if any(catcounts[c][iq][t] for t in inds if t>=2))
  items.append((label,one,amask,bmask))
 menus.append(items)
ck([len(x)-1 for x in menus]==[7,10,10,10,10])
allmask=(1<<80)-1
raw=prod(map(len,menus));atmostone=0;nonzerooutside=0;rows_by_group=[0]*512;outside_by_support=[0]*32;root1zeros=0;supportzeros=0
for ix in product(*[range(len(menu)) for menu in menus]):
 opts=[menus[i][x] for i,x in enumerate(ix)]
 T=sum(1<<i for i,x in enumerate(ix) if x)
 if sum(t[1] for t in opts)>1:root1zeros+=1;continue
 atmostone+=1
 zero=allmask;one=0
 for op in opts:zero,one=zero & op[3],(one & op[3]) | (zero & op[2])
 mask=zero | one
 if not mask:supportzeros+=1;continue
 nonzerooutside+=1;outside_by_support[T]+=1
 for mode,ss in enumerate(smode):rows_by_group[32*mode+T]+=sum(bool(mask & sel) for sel in ss)
result=dict(schema='clustered-full5-interface-measure-v1',status='PASS',optimizer_used=False,new_lean_verification=False,program_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),inputs={n:sha256((args.base/n).read_bytes()).hexdigest() for n in ['clustered_global_phase_fixture.json','clustered_higher_pure_capacity_obstruction.json']},actual_original_count=109,actual_central_capacities=actual_capacities,central_cells=80,source_mass=str(source),categories_per_coordinate=[len(catroots[q]) for q in Q],naive_variable_addresses=80*prod(len(catroots[q]) for q in Q),active_category_variables=variables,zero_source_cells=[r["cell"] for r in cellrows if not r["active_joint_categories"]],cells_without_nonroot_at_some_coordinate=[r["cell"] for r in cellrows if min(r["other_categories"])==0],active_joint_square_atoms=physical_atoms,cell_counts=cellrows,central_selectors=len(selectors),nonempty_central_selectors=sum(bool(s[-1]) for s in selectors),query_counts_per_coordinate=[len(m)-1 for m in menus],raw_outside_query_tuples=raw,atmostone_root1_query_tuples=atmostone,nonzero_outside_query_tuples=nonzerooutside,root1_zero_tuples=root1zeros,other_zero_tuples=supportzeros,raw_complete_screen_count=raw*len(selectors),nonzero_complete_screen_count=sum(rows_by_group),nonzero_rows_by_group=rows_by_group,nonzero_outside_by_support=outside_by_support,checks=checks,scope='Exact category/address counts for fixed109 source with all five outside coordinates and actual fullmode8 source interface. No query matrix expansion, no optimizer, no new dual or gate bound. Category averaging uses source symmetry and global-query convex averaging; source support is actual at-most-one root1.')
# Analytic obstruction to uniformly mixing every queried outside root.
fee_path=args.base/'remaining33_global_root_exclusion_certificate.json'
ck(sha256(fee_path.read_bytes()).hexdigest()=='36e1be912a058df44a9ce3b13c89d97574620176b921e037568ceb96dd0f87d4')
C=list(map(F,json.loads(fee_path.read_text())['combined512_coefficients']));g=F(200163067,201247200)
for iq,q in enumerate(Q):
 if iq:C[256+(1<<iq)]+=g*F(1,q*(q-2))
ck(len(C)==512 and min(C)>=0)
left=[F(1),F(2,3),F(2,9),F(1)]
right=[F(1),F(4,15),F(4,75),F(4,5)]
mode_fees=[sum(C[32*m:32*m+32],F(0)) for m in range(16)]
live_weight=sum(((F(1,9) if r['cell'][0]==4 else F(2,9))*(F(1,25) if r['cell'][1]==10 else F(4,75)) for r in cellrows if r['active_joint_categories']),F(0))
ck(live_weight==F(547,675))
relaxed_debit=sum((mode_fees[m]*left[m//4]*right[m%4] for m in range(16)),F(0))
required_reward=g*live_weight
gap=required_reward-relaxed_debit
ck(gap>0)
ck(F(0)<F(81,82)<=1 and F(0)<F(1875,1876)<=1)
result['uniform_product_outside_root_mixing_obstruction']=dict(live_central_mass=str(live_weight),left_l1_bounds=list(map(str,left)),right_l1_bounds=list(map(str,right)),mode_fee_sums=list(map(str,mode_fees)),maximum_relaxed_integrated_debit=str(relaxed_debit),required_integrated_reward=str(required_reward),positive_gap=str(gap),scope='Refutes all pointwise dual covers whose outside query in each central-selector row is uniformly and independently mixed over every live first root at every queried coordinate. Does not refute nonuniform or correlated query mixtures, or assert a positive gate.')
result['inputs'][fee_path.name]=sha256(fee_path.read_bytes()).hexdigest()
result['checks']=checks
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['cell_counts','inputs','nonzero_rows_by_group','nonzero_outside_by_support']},indent=2))
