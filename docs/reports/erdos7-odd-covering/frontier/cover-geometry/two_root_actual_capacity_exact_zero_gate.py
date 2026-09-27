#!/usr/bin/env python3
"""Actual finite pure-source capacity fields can still have exact zero gate.
All arithmetic is rational. No numerical optimizer is executed or trusted.
This excludes the stated complete gate, not actual surviving configurations.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from math import prod
from hashlib import sha256
import argparse,json
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--source-certificate',type=Path,default=Path(__file__).with_name('remaining33_global_root_exclusion_certificate.json'))
ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=ap.parse_args();raw=args.source_certificate.read_bytes();base=json.loads(raw)
Q=(7,11,13,17,19);d=(2,1,1,1,1);A=[1-F(k,q-1)for k,q in zip(d,Q)]
g=F(base['constants']['g']);co=list(map(F,base['combined512_coefficients']));H=[prod(A[i]for i in range(5)if not T>>i&1)for T in range(32)]
fees=[sum((co[32*m+T]*H[T]for T in range(32)),F())for m in range(16)]
CHECKS={}
def ck(k,b):
 if not b:raise ArithmeticError(k)
 CHECKS[k]=True
ck('full512_costs',len(co)==512 and min(co)>=0)
ck('same_outside_source',H[0]==F(187,384)and min(A)>0)
def axis(n,block,w,mode,deep):
 if mode==0:return [dict(enumerate(w))]
 if mode==1:return [{i:x for i,x in enumerate(w)if i//block==j}for j in range(n//block)]
 return [{i:(w[i]if mode==2 else deep[i])}for i in range(n)if w[i]]
def actual_axis(p,null,weak):
 # Index leaves by root first, then second digit. The deleted root is p-1.
 leaf=lambda i:i//p+p*(i%p)
 nullres,weakres=leaf(null),leaf(weak)
 originals=[(p,p-1),(p*p,nullres)]+[(p**e,weakres+p**(e-1))for e in(3,4)]
 support=[x for x in range(p**4)if all(x%n!=a for n,a in originals)]
 cap0=F(2)if p==3 else F(4,3)
 C=[cap0*F(sum(x%(p*p)==leaf(i)for x in support),p**4)for i in range(p*(p-1))]
 strong=F(2,9)if p==3 else F(4,75);weakmass=F(1,9)if p==3 else F(3,75)
 weights=[F()if i==null else weakmass if i==weak else strong for i in range(p*(p-1))]
 ck(f'axis{p}_{weak}_mass',sum(weights)==1)
 ck(f'axis{p}_{weak}_capacity',all(a<=b for a,b in zip(weights,C)))
 expected=weakmass+F(1,p**4)if p==3 else weakmass+F(1,3*p**4)
 ck(f'axis{p}_{weak}_weakcap',C[weak]==expected)
 atom={x:weights[i]/F(sum(y%(p*p)==leaf(i)for y in support))for i in range(p*(p-1))if weights[i]for x in support if x%(p*p)==leaf(i)}
 ck(f'axis{p}_{weak}_actual_probability',sum(atom.values())==1)
 ck(f'axis{p}_{weak}_density_cap',max(atom.values())<=cap0/F(p**4))
 ck(f'axis{p}_{weak}_constant_surviving_leaves',all(len({v for x,v in atom.items()if x%(p*p)==leaf(i)})==1 for i in range(p*(p-1))if weights[i]))
 return weights,C,originals
WITNESSES=[{'corner': [3, 4, 5, 6], 'selectors': [{'label': [0, 0, 0, 0], 'weight': '1'}, {'label': [0, 1, 0, 2], 'weight': '9733/31250'}, {'label': [0, 1, 0, 3], 'weight': '21517/31250'}, {'label': [0, 2, 0, 6], 'weight': '345039/1000000'}, {'label': [0, 2, 0, 7], 'weight': '83237/1000000'}, {'label': [0, 2, 0, 8], 'weight': '142931/250000'}, {'label': [0, 3, 0, 5], 'weight': '328579/500000'}, {'label': [0, 3, 0, 6], 'weight': '171421/500000'}, {'label': [1, 0, 0, 0], 'weight': '1'}, {'label': [1, 1, 0, 3], 'weight': '1'}, {'label': [1, 2, 0, 7], 'weight': '98359/250000'}, {'label': [1, 2, 0, 10], 'weight': '151641/1000000'}, {'label': [1, 2, 0, 11], 'weight': '151641/1000000'}, {'label': [1, 2, 0, 12], 'weight': '151641/1000000'}, {'label': [1, 2, 0, 13], 'weight': '151641/1000000'}, {'label': [1, 3, 0, 5], 'weight': '144029/250000'}, {'label': [1, 3, 0, 6], 'weight': '11859/1000000'}, {'label': [1, 3, 0, 9], 'weight': '16481/40000'}, {'label': [2, 0, 4, 0], 'weight': '1'}, {'label': [2, 1, 0, 2], 'weight': '211897/1000000'}, {'label': [2, 1, 2, 2], 'weight': '79579/1000000'}, {'label': [2, 1, 4, 0], 'weight': '189481/500000'}, {'label': [2, 1, 4, 2], 'weight': '164781/500000'}, {'label': [2, 2, 0, 8], 'weight': '5943/25000'}, {'label': [2, 2, 2, 6], 'weight': '4751/500000'}, {'label': [2, 2, 2, 8], 'weight': '5943/25000'}, {'label': [2, 2, 4, 6], 'weight': '208771/1000000'}, {'label': [2, 2, 4, 7], 'weight': '306287/1000000'}, {'label': [2, 3, 1, 6], 'weight': '53871/100000'}, {'label': [2, 3, 1, 8], 'weight': '31381/1000000'}, {'label': [2, 3, 4, 5], 'weight': '429909/1000000'}, {'label': [3, 0, 3, 0], 'weight': '773847/1000000'}, {'label': [3, 0, 4, 0], 'weight': '226153/1000000'}, {'label': [3, 1, 1, 2], 'weight': '28287/100000'}, {'label': [3, 1, 2, 2], 'weight': '176637/1000000'}, {'label': [3, 1, 3, 0], 'weight': '99339/1000000'}, {'label': [3, 1, 3, 2], 'weight': '62703/1000000'}, {'label': [3, 1, 3, 3], 'weight': '18347/1000000'}, {'label': [3, 1, 4, 3], 'weight': '45013/125000'}, {'label': [3, 2, 0, 6], 'weight': '30927/100000'}, {'label': [3, 2, 1, 6], 'weight': '1453/31250'}, {'label': [3, 2, 2, 6], 'weight': '29671/100000'}, {'label': [3, 2, 3, 7], 'weight': '71601/1000000'}, {'label': [3, 2, 4, 8], 'weight': '275923/1000000'}, {'label': [3, 3, 1, 8], 'weight': '1'}], 'epsilon': '1/200'}, {'corner': [3, 4, 5, 0], 'selectors': [{'label': [0, 0, 0, 0], 'weight': '1'}, {'label': [0, 1, 0, 2], 'weight': '340219/1000000'}, {'label': [0, 1, 0, 3], 'weight': '659781/1000000'}, {'label': [0, 2, 0, 6], 'weight': '84701/500000'}, {'label': [0, 2, 0, 8], 'weight': '415299/500000'}, {'label': [0, 3, 0, 6], 'weight': '1'}, {'label': [1, 0, 0, 0], 'weight': '1'}, {'label': [1, 1, 0, 3], 'weight': '1'}, {'label': [1, 2, 0, 5], 'weight': '278861/1000000'}, {'label': [1, 2, 0, 7], 'weight': '408377/1000000'}, {'label': [1, 2, 0, 8], 'weight': '106889/500000'}, {'label': [1, 2, 0, 10], 'weight': '12373/500000'}, {'label': [1, 2, 0, 11], 'weight': '12373/500000'}, {'label': [1, 2, 0, 12], 'weight': '12373/500000'}, {'label': [1, 2, 0, 13], 'weight': '12373/500000'}, {'label': [1, 3, 0, 5], 'weight': '10997/31250'}, {'label': [1, 3, 0, 6], 'weight': '580857/1000000'}, {'label': [1, 3, 0, 9], 'weight': '67239/1000000'}, {'label': [2, 0, 4, 0], 'weight': '1'}, {'label': [2, 1, 0, 2], 'weight': '82417/250000'}, {'label': [2, 1, 1, 2], 'weight': '50307/1000000'}, {'label': [2, 1, 2, 2], 'weight': '329667/1000000'}, {'label': [2, 1, 4, 0], 'weight': '6149/1000000'}, {'label': [2, 1, 4, 2], 'weight': '284209/1000000'}, {'label': [2, 2, 4, 1], 'weight': '17417/500000'}, {'label': [2, 2, 4, 3], 'weight': '135889/500000'}, {'label': [2, 2, 4, 4], 'weight': '282907/1000000'}, {'label': [2, 2, 4, 6], 'weight': '24467/200000'}, {'label': [2, 2, 4, 7], 'weight': '144073/500000'}, {'label': [2, 3, 4, 1], 'weight': '4201/6250'}, {'label': [2, 3, 4, 5], 'weight': '2049/6250'}, {'label': [3, 0, 3, 0], 'weight': '329263/500000'}, {'label': [3, 0, 4, 0], 'weight': '170737/500000'}, {'label': [3, 1, 1, 2], 'weight': '372929/1000000'}, {'label': [3, 1, 3, 0], 'weight': '451/3125'}, {'label': [3, 1, 3, 2], 'weight': '1043/10000'}, {'label': [3, 1, 3, 3], 'weight': '6671/100000'}, {'label': [3, 1, 4, 3], 'weight': '311741/1000000'}, {'label': [3, 2, 3, 5], 'weight': '121747/1000000'}, {'label': [3, 2, 3, 7], 'weight': '121747/1000000'}, {'label': [3, 2, 4, 2], 'weight': '74781/200000'}, {'label': [3, 2, 4, 5], 'weight': '55229/250000'}, {'label': [3, 2, 4, 8], 'weight': '32337/200000'}, {'label': [3, 3, 4, 0], 'weight': '475393/500000'}, {'label': [3, 3, 4, 3], 'weight': '24607/500000'}], 'epsilon': '1/1000'}]
results=[]
for case in WITNESSES:
 z,w,zz,ww=case['corner'];tag='_'.join(map(str,case['corner']));U,C3,pure3=actual_axis(3,z,w);V,C5,pure5=actual_axis(5,zz,ww)
 cells=[(l,m)for l,m in product(range(6),range(20))if U[l]and V[m]and not(l<3 and m<5)]
 mass={cell:U[cell[0]]*V[cell[1]]for cell in cells};cost={cell:F()for cell in cells};sums=[F()]*16
 menus={}
 for e3,e5 in product(range(4),repeat=2):
  menus[e3,e5]=(axis(6,3,U,e3,[U[l]/C3[l]if C3[l]else F()for l in range(6)]),axis(20,5,V,e5,[F(4,5)*V[m]/C5[m]if C5[m]else F()for m in range(20)]))
 for k,sel in enumerate(case['selectors']):
  e3,e5,i,j=sel['label'];weight=F(sel['weight']);left,right=menus[e3,e5];mo=4*e3+e5
  ck(tag+'_legal_selector_'+str(k),weight>=0 and 0<=i<len(left)and 0<=j<len(right))
  sums[mo]+=weight
  for l,m in cells:cost[l,m]+=fees[mo]*weight*left[i].get(l,F())*right[j].get(m,F())
 ck(tag+'_all16_convex',sums==[F(1)]*16)
 epsilon=F(case['epsilon']);residual={cell:cost[cell]-g*H[0]*mass[cell]for cell in cells}
 for cell in cells:ck(tag+'_strict_coefficient_'+str(cell),residual[cell]>=epsilon*mass[cell])
 ck(tag+'_positive_epsilon',epsilon>0)
 # For every theta>=0, each screen dominates its convex selector mixture.
 # Hence G(theta)<=-epsilon*sum(wv theta)<=0. Theta0 attains0.
 results.append({'corner':case['corner'],'actual_pure3_originals':pure3,'actual_pure5_originals':pure5,'central15_original':[15,0],'C3':list(map(str,C3)),'C5':list(map(str,C5)),'epsilon':str(epsilon),'min_exact_residual_over_cell_mass':str(min(residual[c]/mass[c]for c in cells)),'unmasked_live_cells':len(cells),'nonzero_selector_count':len(case['selectors']),'selectors':case['selectors']})
out={'schema':'two-root-actual-capacity-exact-zero-gate-v1','status':'EXACT_ZERO_OPTIMUM','scope':'Two literal finite actual pure families through height4, budget21111 and unchanged640 full512 fees. Capacity-sensitive direct query fields and all120cell thinnings of either specified fixed actual rho. Convex query mixtures prove gate <= -epsilon times central mass for every nonzero admissible theta. Theta0 attains0. This is a limitation of the specified fixed-rho query envelope; it makes no claim about every other rho on the same family, nonexistence of survivors, or an actual covering example. Ordinary rational certificate, no new Lean.','budget':d,'outside_factors':list(map(str,A)),'all32_H':list(map(str,H)),'folded16_fees':list(map(str,fees)),'results':results,'checks':len(CHECKS),'source_certificate_sha256':sha256(raw).hexdigest(),'producer_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'new_lean_verification':False}
args.output.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k]for k in('status','scope','checks')},indent=2))
for r in results:print(r['corner'],r['epsilon'],r['min_exact_residual_over_cell_mass'])
