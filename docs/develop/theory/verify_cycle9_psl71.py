#!/usr/bin/env python3
"""Exact nonnormal index-72 [4,9,3] action certificate.
Standard library only; all arithmetic is modulo 71. Projective matrices are
identified up to sign.
"""
Q=71
I=(1,0,0,1)
def mm(A,B):
 a,b,c,d=A; e,f,g,h=B
 return ((a*e+b*g)%Q,(a*f+b*h)%Q,(c*e+d*g)%Q,(c*f+d*h)%Q)
def pw(A,n):
 R=I
 while n:
  if n&1:R=mm(R,A)
  A=mm(A,A); n>>=1
 return R
def neg(A): return tuple((-x)%Q for x in A)
def peq(A,B): return A==B or A==neg(B)
def det(A):
 a,b,c,d=A; return (a*d-b*c)%Q
def tr(A): return (A[0]+A[3])%Q
def pcanon(A): return min(A,neg(A))
def subgroup(gens):
 S={pcanon(I)}; todo=[I]
 while todo:
  A=todo.pop()
  for G in gens:
   k=pcanon(mm(A,G))
   if k not in S:S.add(k);todo.append(mm(A,G))
 return S
def act(A,p):
 a,b,c,d=A
 if p is None:return None if c==0 else a*pow(c,-1,Q)%Q
 den=(c*p+d)%Q
 return None if den==0 else (a*p+b)*pow(den,-1,Q)%Q
def cycles(A):
 points=[None]+list(range(Q)); seen=set(); out=[]
 for p in points:
  if p in seen:continue
  j=p; n=0
  while j not in seen:seen.add(j);n+=1;j=act(A,j)
  out.append(n)
 return sorted(out)
def fixed_points(A):
 points=[None]+list(range(Q))
 return [p for p in points if act(A,p)==p]
X=(2,7,23,10);Y=(0,70,1,30);Z=(47,66,35,25)
U=mm(X,Y);V=mm(Y,Z);T=mm(U,Z)
P=neg(mm(mm(X,Z),pw(Y,6)))
assert all(det(A)==1 for A in (X,Y,Z,U,V,T,P))
assert peq(pw(X,4),I) and pw(X,2)!=I
assert peq(pw(Y,9),I) and all(not peq(pw(Y,n),I) for n in range(1,9))
assert peq(pw(Z,3),I) and pw(Z,1)!=I
assert peq(pw(U,2),I) and peq(pw(V,2),I) and peq(pw(T,2),I)
assert peq(mm(mm(V,X),V),pw(X,3))  # [V][X][V]=[X]^-1 in PSL2(F71)
assert peq(mm(mm(U,Z),U),pw(Z,2))  # [U][Z][U]=[Z]^-1 in PSL2(F71)
assert P!=I and tr(P)==2 and peq(pw(P,Q),I)
D8=subgroup([X,V]); S3=subgroup([U,Z]); C9=subgroup([Y])
assert len(D8)==8
assert len(S3)==6
assert len(C9)==9
for name,H in (("D8",D8),("S3",S3),("C9",C9)):
 for A in H:
  if A != pcanon(I):
   assert fixed_points(A)==[], (name,A,fixed_points(A))
gens=[X,Y,Z,pw(X,3),pw(Y,8),pw(Z,2)]
seen,todo={0},[0]
while todo:
 p=todo.pop()
 for G in gens:
  q=act(G,p)
  if q not in seen:seen.add(q);todo.append(q)
assert len(seen)==72
assert cycles(X)==[4]*18
assert cycles(Y)==[9]*8
assert cycles(Z)==[3]*24
assert cycles(U)==[2]*36
assert cycles(V)==[2]*36
assert cycles(T)==[2]*36
print("PASS: PSL2(F71) nonnormal index-72 action")
print("projective subgroup orders: D8=8, S3=6, C9=9")
print("cycle structures: X=4^18, Y=9^8, Z=3^24, XY=YZ=XYZ=2^36")
print("fixed-point-free finite images: D8=7, S3=5, C9=8 nonidentity elements")
print("transitive orbit size: 72; six-sector tetrahedra: 144/6=24")
