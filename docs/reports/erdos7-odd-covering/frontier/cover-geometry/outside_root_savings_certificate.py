#!/usr/bin/env python3
"""Exact outside-root fee and assigned-descendant certificates.

Python 3.10+, standard library only. Certifies six fixed root-3 core rows
under the ordinary-proved same-family budget and conditional-kernel
premises; does not certify unrestricted odd-cover noncoverage.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import prod,lcm
import argparse, json, sys
from pathlib import Path

@lru_cache(None)
def fam(A):
 if not A:return ((),)
 i=A&-A;rest=A^i;out=list(fam(rest));s=rest
 while True:
  block=s|i;out.extend((block,)+p for p in fam(A^block))
  if s==0:break
  s=(s-1)&rest
 return tuple(out)

def residual(v):
 return [sum(((-1)**len(f)*prod((v[s] for s in f),start=F(1)) for f in fam(A)),F(0)) for A in range(32)]

def kr_caps(bs,M):
 b=[F(0)]+[prod((bs[i] for i in range(5) if s>>i&1),start=F(1)) for s in range(1,32)]
 w=[b[s] if s.bit_count()>1 else F(0) for s in range(32)]
 low=residual(w);hi=residual([a+c for a,c in zip(w,b)])
 assert min(hi)>0 and F(1,3)<M<F(2,3)
 margins={s:F(1,3)*hi[31^s]-(M-F(1,3))*low[31^s] for s in range(1,32)}
 forced=tuple(s for s in margins if margins[s]>0);free=tuple(s for s in margins if margins[s]<=0)
 den=prod(x.denominator for x in bs);wt=lcm(3,M.denominator)
 a=wt//3;c=M.numerator*(wt//M.denominator)-a
 terms=[]
 for f in fam(31):
  raw=(-1)**len(f)*prod((b[s] for s in f),start=F(1))*den
  assert raw.denominator==1;terms.append((f,int(raw)))
 best=None;arg=None
 forcedbits=sum(1<<(s-1) for s in forced)
 for corner in range(1<<len(free)):
  bits=forcedbits+sum(1<<(s-1) for i,s in enumerate(free) if corner>>i&1)
  z1=z2=0
  for f,val in terms:
   n1=n2=val
   for s in f:
    yes=(bits>>(s-1))&1;old=int(s.bit_count()>1)
    n1*=old+yes;n2*=old+1-yes
   z1+=n1;z2+=n2
  total=a*z1+c*z2
  if best is None or total<best:best=total;arg=bits
 L=sum((b[s]*low[31^s] for s in range(1,32)),F(0))
 y=[b[s]*((arg>>(s-1))&1) if s else F(0) for s in range(32)]
 minpair=(residual([w[s]+y[s] for s in range(32)])[31],
          residual([w[s]+b[s]-y[s] for s in range(32)])[31])
 assert F(best,den*wt)==minpair[0]/3+(M-F(1,3))*minpair[1]
 gap=F(best,den*wt)-L/6
 return {'caps':list(map(str,bs)),'target':str(M),'gap':str(gap),'L':str(L),'low_residuals':list(map(str,low)),'high_residuals':list(map(str,hi)),'derivative_margins':{str(s):str(margins[s]) for s in margins},'forced':forced,'free':free,'corners':1<<len(free),'minimizing_vertex':arg,'minimizing_residuals':list(map(str,minpair)),'minimum_G':str(F(best,den*wt))}

def caps(J,expenses):
 return tuple(1/(3-F(6,5)*e) if q==5 else 1/(q-2-2*e) for q,e in zip(J,expenses))


FSTAR=F(1493,3072)
SPECS=(
 ((5,7,11,17,23),(13,19,29,31,37),7),
 ((5,7,11,19,23),(13,17,29,31,37),7),
 ((5,7,13,17,19),(11,23,29,31,37),6),
 ((5,7,13,17,23),(11,19,29,31,37),6),
 ((5,7,13,19,23),(11,17,29,31,37),6),
 ((5,7,11,13,37),(17,19,23,29,31),9),
)

def fee(q):
 return {5:F(7,24),7:F(1,8),11:F(1,24),13:F(1,48)}.get(q,F(1,2**((q-1)//2)))

def zrec(v):
 out=[F(1)]*32
 for A in range(1,32):
  bit=A&-A;rest=A^bit;out[A]=out[rest];part=rest
  while True:
   support=part|bit;out[A]-=v[support]*out[A^support]
   if part==0:break
   part=(part-1)&rest
 return out

def outer(proxy,E,t):
 bs=caps(proxy,[E]*5)
 b=[F(0)]+[prod((bs[i] for i in range(5) if S>>i&1),start=F(1)) for S in range(1,32)]
 v=[(t+int(S.bit_count()>1))*b[S] for S in range(32)]
 zs=residual(v)
 assert zs==zrec(v) and min(zs)>0
 L=sum((b[S]*zs[31^S] for S in range(1,32)),F(0))
 K=L/(2*3**t*zs[31]);p=proxy[0];save=fee(p)-K
 assert save>0
 return K,save,{'proxy_children':proxy,'expense':str(E),'cutoff':t,'caps':list(map(str,bs)),
  'residuals':list(map(str,zs)),'Z':str(zs[31]),'L':str(L),'K':str(K),'saving':str(save)}

def main():
 if sys.version_info < (3,10):
  raise SystemExit('Python 3.10 or later is required.')
 if not __debug__:
  raise SystemExit('Assertions are required; do not use Python -O.')
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--output',type=Path,required=True)
 args=parser.parse_args()
 rows=[]
 lower_bounds=(F(1,3000),F(1,200),F(1,250),F(3,250),F(1,60))
 for index,(J,proxy,t) in enumerate(SPECS):
  C=sum(map(fee,J),F(0));E=FSTAR-C;M=F(1,2)-E;p=proxy[0];fp=fee(p)
  assert p not in J and all(q not in J for q in proxy)
  K,save,ext=outer(proxy,E,t)
  row={'children':J,'charge':str(C),'E':str(E),'M':str(M),
       'missing_prime':p,'missing_fee':str(fp),'outer':ext}
  if J!=SPECS[-1][0]:
   cert=kr_caps(caps(J,[E]*5),M+save)
   assert F(cert['gap'])>lower_bounds[index]
   row['uniform_root_certificate']=cert
  else:
   assert p==17 and fp==F(1,256)
   nonowner=kr_caps(caps(J,[E-fp]*5),M+save)
   assert F(nonowner['gap'])>0
   row['missing_prime_not_in_core_descendants']=nonowner
   row['assigned_descendant_certificates']=[]
   for owner in J:
    stack=[(fp,E,0)];segments=[]
    while stack:
     lo,hi,depth=stack.pop();es=[hi if q==owner else hi-fp for q in J]
     cert=kr_caps(caps(J,es),M+lo)
     if F(cert['gap'])>0:
      segments.append({'lo':str(lo),'hi':str(hi),'expenses':list(map(str,es)),
                       'certificate':cert})
      continue
     assert depth<12,(J,owner,lo,hi)
     mid=(lo+hi)/2;stack.extend([(mid,hi,depth+1),(lo,mid,depth+1)])
    assert all(F(r['certificate']['gap'])>F(1,25000) for r in segments)
    segments.sort(key=lambda r:F(r['lo']))
    assert F(segments[0]['lo'])==fp and F(segments[-1]['hi'])==E
    assert all(a['hi']==b['lo'] for a,b in zip(segments,segments[1:]))
    row['assigned_descendant_certificates'].append({'owner':owner,'segments':segments})
  rows.append(row)
 inherited=tuple([(5,7,11,13,q) for q in (17,19,23,29,31,37)]+
  [(5,7,11,17,q) for q in (19,23)]+[(5,7,11,19,23)]+
  [(5,7,13,17,q) for q in (19,23)]+[(5,7,13,19,23)])
 certified=tuple(r['children'] for r in rows)
 remaining=tuple(sorted(set(inherited)-set(certified)))
 assert len(set(inherited))==12 and len(set(certified))==6
 assert set(certified)<=set(inherited)
 assert remaining==tuple([(5,7,11,13,q) for q in (17,19,23,29,31)]+[(5,7,11,17,19)])
 result={'schema':'outside-root-savings-v1',
  'scope':'Six specified exceptional root-3 cores; graph blocks have at most six vertices; arbitrary finite original heights and residues.',
  'premises':'Chapter 23 actual child domains and conditional kernel; Chapter 25 unique core; same-family root budget and assigned descendant partition.',
  'Fstar':str(FSTAR),'certified_additional_cores':len(rows),
  'inherited_remaining_cores':inherited,'remaining_cores':remaining,'rows':rows}
 args.output.write_text(json.dumps(result,indent=2)+'\n')
 print(f"Certified {len(rows)} additional core rows, including 10 assigned-descendant intervals.")

if __name__=='__main__':
 main()
