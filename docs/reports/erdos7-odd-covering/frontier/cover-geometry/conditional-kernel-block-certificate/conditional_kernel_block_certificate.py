#!/usr/bin/env python3
"""Independent rational reconstruction of conditional-kernel boundary rows."""
from fractions import Fraction as F
from itertools import combinations
from functools import reduce
from pathlib import Path
import argparse
import json
import sys

if not __debug__:
    raise SystemExit('Run without -O: assertions are certificate checks.')
if sys.version_info < (3,10):
    raise SystemExit('Python 3.10 or newer is required.')
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args()

P0=(5,7,11,13,17,19,23,29)
BUDGET=F(187,384)
EXCEPTIONS={(5,7,11,13),(5,7,11,17)}
def fee(q):
 return {5:F(7,24),7:F(1,8),11:F(1,24),13:F(1,48)}.get(q,F(1,2**((q-1)//2)))
def caps(primes,e):
 return tuple(1/(F(3)-F(6,5)*e) if q==5 else 1/(q-2-2*e) for q in primes)
def esp(bs):
 out=[F(1)]+[F(0)]*len(bs)
 for b in bs:
  for k in range(len(bs),0,-1):out[k]+=b*out[k-1]
 return out
def polyZ(bs,t):
 es=esp(bs);cs=(1,-t,t*t-t-1,-t**3+3*t*t+2*t-1,t**4-6*t**3+t*t+9*t+2)
 return sum(a*b for a,b in zip(es,cs))
def polyL(bs,t):
 es=esp(bs);cs=(0,1,1-2*t,3*t*t-6*t-2,-4*t**3+18*t*t-2*t-9)
 return sum(a*b for a,b in zip(es,cs))

def partitions(items):
 if not items:
  yield ()
  return
 first,*rest=items
 for pp in partitions(rest):
  yield ((first,),)+pp
  for i in range(len(pp)):
   yield pp[:i]+((first,)+pp[i],)+pp[i+1:]
def allfamilies(n):
 out=[]
 for k in range(n+1):
  for union in combinations(range(n),k):
   for pp in partitions(list(union)):
    out.append(tuple(sum(1<<i for i in block) for block in pp))
 return out
FAMILY=allfamilies(4)
assert len(FAMILY)==52 and len(set(FAMILY))==52

def literalZ(bs,t):
 total=F(0)
 for fam in allfamilies(len(bs)):
  value=F((-1)**len(fam))
  for support in fam:
   value*=t+(support.bit_count()>1)
   value*=reduce(lambda a,i:a*bs[i],(i for i in range(len(bs)) if support>>i&1),F(1))
  total+=value
 return total

def residual_check(bs,t):
 values=[]
 for mask in range(1,16):
  sub=tuple(bs[i] for i in range(4) if mask>>i&1)
  z=polyZ(sub,t)
  assert z==literalZ(sub,t)
  values.append(z)
 return values

rows=[];partition_counts={};max_t=0;worst=None
for j in range(1,5):
 count=0;success=0;exceptions=0
 for small in combinations(P0,j):
  pp=small+(31,33,35)[:4-j]
  C=sum(map(fee,small),F(0));E=BUDGET-C;b=caps(pp,E)
  assert all(x>0 for x in b)
  count+=1
  if pp in EXCEPTIONS:
   exceptions+=1;continue
  selected=None
  for t in range(1,8):
   r=residual_check(b,t)
   if min(r)<=0:break
   Z=polyZ(b,t);L=polyL(b,t)
   # Independent literal derivative sum over complete supports.
   L2=sum(reduce(lambda a,i:a*b[i],(i for i in range(4) if s>>i&1),F(1))*polyZ(tuple(b[i] for i in range(4) if not s>>i&1),t) for s in range(1,16))
   assert L==L2
   K=L/(2*3**t*Z)
   if K<C:
    selected={'small_count':j,'proxy_tuple':pp,'charge':str(C),'expense':str(E),'caps':list(map(str,b)),'cutoff':t,'residuals':list(map(str,r)),'min_residual':str(min(r)),'Z':str(Z),'L':str(L),'kernel':str(K),'margin':str(C-K),'ratio':str(K/C)}
    break
  assert selected is not None,pp
  rows.append(selected);success+=1;max_t=max(max_t,selected['cutoff'])
  if worst is None or F(selected['ratio'])>F(worst['ratio']):worst=selected
 partition_counts[j]={'rows':count,'kernel_successes':success,'KR_inputs':exceptions}
assert len(rows)==160 and sum(x['rows'] for x in partition_counts.values())==162
assert max_t==7
assert F(worst['ratio'])==F(65157018363904,65378462038225)

orientations=[]
for pp in sorted(EXCEPTIONS):
 C=sum(map(fee,pp),F(0));E=BUDGET-C;b=caps(pp,E);r=residual_check(b,1);assert min(r)>0
 K=polyL(b,1)/(6*polyZ(b,1));assert K<1
 pmin=next(p for p in (5,7,11,13,17,19) if p not in pp)
 # These tuples contain 5,7,11, and have parent p>=13 or17.
 assert pmin>=13 and C>F(1,3) and F(3,pmin)*K<C
 orientations.append({'children':pp,'charge':str(C),'min_non3_parent':pmin,'K3_t1':str(K),'normalized_parent_kernel_at_min_parent':str(F(3,pmin)*K),'margin':str(C-F(3,pmin)*K)})

# Both coupled KR inputs reduce analytically to four vertices.
# For H(y)=a*Z(w+y)+c*Z(w+b-y), the support derivative is bounded
# above by -a*Z_out(w+b)+c*Z_out(w). Strict negative upper bounds
# force that support to the first root. The two remaining singleton
# allocations are multi-affine and attain their minimum at corners.
KR_inputs=[]
for pp,a,c,denominator,target in (
    ((5,7,11,13),32,13,96,F(15,32)),
    ((5,7,11,17),256,99,768,F(355,768)),
):
    C=sum(map(fee,pp),F(0)); E=BUDGET-C; b=caps(pp,E)
    rr=residual_check(b,1)
    assert min(rr)>0 and target<=C
    D=reduce(lambda acc,x:acc*x.denominator,b,1)
    bs=[F(0)]+[
        reduce(lambda acc,i:acc*b[i],(i for i in range(4) if s>>i&1),F(1))
        for s in range(1,16)
    ]
    coefficients=[]
    for family in FAMILY:
        value=F((-1)**len(family))*reduce(lambda acc,s:acc*bs[s],family,F(1))*D
        assert value.denominator==1
        coefficients.append(int(value))
    def numerator(mask,side):
        total=0
        for family,coefficient in zip(FAMILY,coefficients):
            value=coefficient
            for support in family:
                bit=(mask>>(support-1))&1
                value*=int(support.bit_count()>1)+(bit if side==0 else 1-bit)
            total+=value
        return total
    derivative_margins={}
    free=[]
    for support in range(1,16):
        sub=tuple(b[i] for i in range(4) if not support>>i&1)
        margin=a*polyZ(sub,1)-c*polyZ(sub,0)
        if margin>0:
            derivative_margins[str(support)]=str(margin)
        else:
            free.append(support)
    assert free==[4,8] and len(derivative_margins)==13
    forced_mask=sum(1<<(support-1) for support in range(1,16) if support not in free)
    L0=polyL(b,0)
    cases=[]
    for corner in range(4):
        mask=forced_mask+sum(1<<(support-1) for i,support in enumerate(free) if corner>>i&1)
        first=F(numerator(mask,0),D)
        second=F(numerator(mask,1),D)
        gap=(a*first+c*second)/denominator-L0/6
        assert gap>0
        cases.append({'vertex':mask,'Z_first':str(first),'Z_second':str(second),'fee_gap':str(gap)})
    KR_inputs.append({
        'children':pp,'fee_sum':str(C),'target_fee':str(target),'expense':str(E),
        'caps':list(map(str,b)),'residuals_w_plus_b':list(map(str,rr)),
        'weight_numerators':[a,c],'weight_denominator':denominator,
        'L0':str(L0),'forced_derivative_margins':derivative_margins,
        'free_support_masks':free,'verified_corners':cases,
        'minimum_fee_gap':str(min(F(row['fee_gap']) for row in cases)),
    })
assert F(KR_inputs[1]['minimum_fee_gap'])==F(831018050567443,54763668484928256)

out={'scope':'Exact finite certificate for conditional-kernel block fees. The probability kernel, monotonicity, recursive induction and unbounded-block theorem require their ordinary mathematical proofs. No unrestricted noncoverage or Lean certification is asserted.',
'partition':partition_counts,'kernel_rows':160,'max_selected_cutoff':max_t,'worst_row':worst,'exceptional_non3_orientations':orientations,'coupled_KR_inputs':KR_inputs,'rows':rows}
args.output.write_text(json.dumps(out,indent=2)+'\n')
print('PASS: 160 kernel rows, 2 four-corner KR inputs, all finite orientation checks.')
print('Worst kernel/charge:', worst['ratio'])
