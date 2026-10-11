---
slug: kulhandjian-hanzo-2026-flagship-distance-conjecture-25
bibkey: kulhandjian2026singer
doi: 10.48550/arXiv.2610.02392
url: https://arxiv.org/abs/2610.02392v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/SingerQuadricQuditDistanceBound.result
---

# Kulhandjian–Hanzo Conjecture 25: the odd-prime distance bound

## Problem

Kulhandjian and Hanzo, arXiv:2610.02392v1, Section VII, Conjecture 25
(“Flagship distance, original”), state: “For prime $p$ odd,
$d_{\min}(\mathcal Q(p,2))\le p+1$.” Issue
[#13799](https://github.com/the-omega-institute/trureturing/issues/13799)
records the complete statement and its literature checks.

For every odd prime $p$, take a primitive $\alpha\in\mathbb F_{p^3}$ and
$n=p^2+p+1$. The source's literal trace definitions are
$\tau_H(i)=[\operatorname{Tr}(\alpha^i)=0]$ and
$\tau_Q(i)=[\operatorname{Tr}(\alpha^{2i})=0]$.
Set $A=\operatorname{circ}(\tau_H)$,
$M_Q=\operatorname{circ}(\tau_Q)$, and $H=(A\mid M_QA)$ over
$\mathbb F_p$, using entries $v_{i-j}$ for circulants. Stabilizers are
$\operatorname{rowspan}(H)$. The centralizer consists of pairs with zero
signed symplectic pairing against every stabilizer, and Pauli weight counts
positions where either component is nonzero. The result constructs a
centralizer vector outside the stabilizers of weight at most $p+1$.
It quantifies over every primitive $\alpha$.

## Motivation

The bound supplies a nontrivial logical operator of controlled weight in
every odd-prime flagship code. The motivation GID proves this assertion
uniformly in $p$, rather than only for the examples in the source.

## Gap

The preregistration classifies this as Tier 1, an explicitly numbered
published conjecture. Its recorded source, reference, MathDB and repository
checks found no settlement in the searched scope. The classical line
indicators cited by the source do not alone establish that a quantum
centralizer vector is outside the stabilizer row space. Worldwide novelty
and priority are not certified by a bounded search.

A GPL-3.0-only Lean proof of Singer's theorem exists upstream in
`d0d1/singer-theorem-lean`. It was not used, for licence reasons.
The supporting module supplies an independent proof from pinned Mathlib;
its theorem is attributed to Singer (1938), with the citation in
[the Singer note](../Library/FiniteGeometry/singer1938projective.md).

## Route

Write $D=\operatorname{supp}(\tau_H)$, $Q=\operatorname{supp}(\tau_Q)$,
$k=p+1$. Singer's theorem gives $|D|=|Q|=k$ and nonzero difference
multiplicity one for $D$. The supporting result also proves the difference
property for $Q$ and the index-doubling correspondence.

For $t\in\mathbb Z/n$, put $s_t=1_{t-D}$. Then $As_t=\mathbf1$ and
$M_Q\mathbf1=\mathbf1$, so $(s_t,s_t)$ centralizes every row of $H$.
The vector $y=(\tau_Q,-e_0)$ is in the ordinary right kernel of $H$;
every stabilizer therefore has zero dot product with $y$.
Set $m_t=|(t-D)\cap Q|$ and $\delta_t=1_D(t)$. The pairing is
$m_t-\delta_t$ modulo $p$. The exact moment identities are
$\sum_t m_t=k^2$ and $\sum_t m_t^2=k^2+p^2+p$.
If all pairings vanished, $m_t\equiv\delta_t\pmod p$ with
$0\le m_t\le p+1$ would force
$\sum_t m_t^2\ge p^2(p+1)+(p+1)$. This exceeds the second moment by
$p(p-2)(p+1)>0$. Some translated line therefore gives a non-stabilizer
logical operator of Pauli weight $p+1$.

## Falsifier

A counterexample would be an odd prime and primitive element for which
every centralizer element outside the stabilizers has weight greater than
$p+1$. Failure of the route would require a false Singer difference count,
a failed centralizer or right-kernel identity, or a failed exact moment
identity. The worked-example inconsistency below concerns the printed
vectors rather than these defining trace formulas.

## Evidence

The supporting module is
`D5/S3/Geometry/FiniteGeometry/SingerTracePlane.lean`; the settling module is
`D5/S3/Quantum/Information/SingerQuadricQuditDistanceBound.lean`.
The supporting public theorems are `no_proper_invariant_subspace`,
`trace_plane_intersection`, and `result`; the settling public theorem is
`result : claim`. The axiom closure is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.
The settling Scribe records an `OpenProblemResolutionClaim` with resolution
`Proved` for this slug. Information-escape registration is paused under
CLAUDE.md §3.9.

## Triage

Resolution: **proved**. Admission is `open-problem-resolution` for the
settling module and `escape-witness` for the supporting module. Both have
utility `none`: these universal proofs supply no delivered computational
checker, enumeration or certified instance.

### What the settlement shows

- **Proved:** $d_{\min}(\mathcal Q(p,2))\le p+1$ for every odd prime,
  with every primitive element and the source's defining trace expressions.
  The decisive mechanism is the two-moment obstruction to all translated
  logical candidates belonging to the row space.
- **Proved upper bound / open independent lower-bound certification:** at
  $p=7$ the theorem gives $d_{\min}\le8$. Together with the source's
  reported exhaustive $d_{\min}\ge8$, this yields $d_{\min}=8$.
  The source's lower-bound computation is not reproduced or kernel-certified
  in this delivery; the equality retains that explicit condition.
- **Open:** the general lower bound $d_{\min}\ge p+1$ for odd primes
  $p\ge5$. The source's exceptional $p=3$ has distance 3, as the finite
  computation below verifies, so equality $p+1$ for all odd primes is false.
- **Open:** the analogous uniform upper bound for odd prime powers
  $q=p^t$ with $t>1$, and for dimensions $d>2$. The abstract translated-line
  argument in the proof is private; its required difference-set and
  cardinality hypotheses for other source families are not discharged here.
- **Computed:** exact field, matrix, centralizer, separator and moment checks
  at $p=3,5,7,11$, with the finite scopes in the table below. The checks
  validate weight-$p+1$ candidates; they do not establish equality of the
  minimum distance. The source's $p=5$ equality and $p=11$ lower bound
  remain source-reported; the conjectured $p=11$ value 12 remains open.
- **Computed:** the Appendix A example using $X^3+2X^2+X+1$ and $\alpha=X$
  has $\operatorname{ord}(\alpha)=26$,
  $D=\{0,7,8,11\}$ and $Q=\{0,4,10,12\}$. The corrected indicator vectors,
  in order $i=0,\ldots,12$, are
  $\tau_H=(1,0,0,0,0,0,0,1,1,0,0,1,0)$ and
  $\tau_Q=(1,0,0,0,1,0,0,0,0,0,1,0,1)$.
  The printed $D=\{2,3,6,8\}$, $Q=\{0,7,8,11\}$ fail the source's
  trace definitions and inverse-doubling relation. The proof uses the
  defining expressions.
- **Proved effect on source status:** the numbered upper-bound assertion in
  Conjecture 25 is settled. The source's small-prime lower bounds and exact
  distances remain separate assertions. Results requiring the upper bound
  may use it for every odd prime; assertions requiring equality or general
  prime powers still require their own lower bounds or extensions.

### Reproducible finite computations

Create `/tmp/op-kh25` and `/tmp/op-kh25-stage-b`, and save the three
complete scripts below at their named paths. They use only the Python standard
library. Each SHA-256 is over the exact UTF-8 code block, including its final
newline.

| computation | command | exit | script SHA-256 | tested scope |
| --- | --- | --- | --- | --- |
| field/matrix checks | `python3 /tmp/op-kh25/check.py` | 0 | `1a4e9285f5ec5cb27d6b2e22dde6fe19e36447f88bb39bcd76d6b3bbc119d9b3` | p = 3,5,7,11; d = 2 |
| Appendix A | `python3 /tmp/op-kh25/source-example-check.py` | 0 | `8880c752555b80e453efcfb588dd9a8ccb020d99a39d88e018e2dab34936a904` | p = 3; stated polynomial and alpha |
| minimum distance | `python3 /tmp/op-kh25-stage-b/p3-distance-runner.py` | 0 | `1cda8981743526ad1d1954f0449b25fd484f5416030d76c4d69b1b868d2537b8` | p = 3; all 13 weight-1 and 78 weight-2 supports; weight-3 witness |

| p | n | rank H | first moment | second moment | candidate weight |
| --- | --- | --- | --- | --- | --- |
| 3 | 13 | 7 | 16 | 28 | 4 |
| 5 | 31 | 16 | 36 | 66 | 6 |
| 7 | 57 | 29 | 64 | 120 | 8 |
| 11 | 133 | 67 | 144 | 276 | 12 |

The minimum-distance computation finds the weight-3 logical supported on
$\{0,1,4\}$ with $Z$ coefficients $(2,2,2)$ and $X$ coefficients $(1,1,1)$;
all centralizer kernels supported on one or two positions lie in the
stabilizer space. These are finite arithmetic results, not new Lean
statements. No larger-prime lower-bound enumeration is delivered.

`/tmp/op-kh25/check.py`

```python
import itertools,json,time
from collections import Counter

class F3:
 def __init__(self,p,f): self.p=p; self.f=f; self.one=(1,0,0); self.zero=(0,0,0)
 def add(self,a,b): return tuple((x+y)%self.p for x,y in zip(a,b))
 def mul(self,a,b):
  c=[0]*5
  for i in range(3):
   for j in range(3): c[i+j]=(c[i+j]+a[i]*b[j])%self.p
  for i in [4,3]:
   for j in range(3): c[i-3+j]=(c[i-3+j]-c[i]*self.f[j])%self.p
  return tuple(c[:3])
 def pow(self,a,n):
  b=self.one
  while n:
   if n%2:b=self.mul(b,a)
   a=self.mul(a,a);n//=2
  return b
 def tr(self,a): return self.add(self.add(a,self.pow(a,self.p)),self.pow(a,self.p*self.p))

def factors(n):
 out=[];d=2
 while d*d<=n:
  if n%d==0:
   out.append(d)
   while n%d==0:n//=d
  d+=1
 if n>1:out.append(n)
 return out

def find_field(p):
 for f in itertools.product(range(p),repeat=3):
  if f[0]==0 or any((r**3+f[2]*r*r+f[1]*r+f[0])%p==0 for r in range(p)):continue
  ff=F3(p,f);a=(0,1,0);N=p**3-1
  if all(ff.pow(a,N//r)!=ff.one for r in factors(N)):
   assert ff.pow(a,N)==ff.one
   return ff,a
 raise Exception('no primitive polynomial')

def matmul(a,b,p):
 bt=list(zip(*b))
 return [[sum(x*y for x,y in zip(row,col))%p for col in bt] for row in a]
def matvec(a,v,p):return [sum(x*y for x,y in zip(row,v))%p for row in a]

def rref(a,p):
 a=[list(r) for r in a];piv=[];j=0
 for c in range(len(a[0])):
  rr=next((r for r in range(j,len(a)) if a[r][c]),None)
  if rr is None:continue
  a[rr],a[j]=a[j],a[rr];d=pow(a[j][c],-1,p);a[j]=[x*d%p for x in a[j]]
  for r in range(len(a)):
   if r!=j and a[r][c]:
    d=a[r][c];a[r]=[(x-d*y)%p for x,y in zip(a[r],a[j])]
  piv.append(c);j+=1
  if j==len(a):break
 return a[:j],piv

def run(p):
 start=time.monotonic();ff,alpha=find_field(p);n=p*p+p+1;k=p+1
 assert ff.pow(alpha,n)[1:]==(0,0) and ff.pow(alpha,n)[0]
 tr=[ff.tr(ff.pow(alpha,i)) for i in range(p**3-1)]
 assert all(x[1:]==(0,0) for x in tr)
 assert all((tr[i]==ff.zero)==(tr[(i+n)%(p**3-1)]==ff.zero) for i in range(p**3-1))
 D={i for i in range(n) if tr[i]==ff.zero}
 Q={i for i in range(n) if tr[2*i]==ff.zero}
 assert len(D)==len(Q)==k and Q=={pow(2,-1,n)*d%n for d in D}
 cd=Counter((d-e)%n for d in D for e in D);cq=Counter((d-e)%n for d in Q for e in Q)
 assert cd[0]==cq[0]==k and all(cd[i]==cq[i]==1 for i in range(1,n))
 A=[[int((i-j)%n in D) for j in range(n)] for i in range(n)]
 M=[[int((i-j)%n in Q) for j in range(n)] for i in range(n)]
 B=matmul(M,A,p);assert B==matmul(A,M,p)
 H=[a+b for a,b in zip(A,B)];hred,piv=rref(H,p)
 # Isotropy is checked with the source's signed symplectic form.
 ABt=matmul(A,list(zip(*B)),p);BAt=matmul(B,list(zip(*A)),p);assert ABt==BAt
 y=[int(i in Q) for i in range(n)]+[(-int(i==0))%p for i in range(n)]
 assert matvec(H,y,p)==[0]*n
 moments=[];witnesses=[]
 for t in range(n):
  S={(t-d)%n for d in D};s=[int(i in S) for i in range(n)];v=s+s
  assert matvec(A,s,p)==[1]*n and matvec(M,[1]*n,p)==[1]*n
  assert matvec(B,s,p)==[1]*n
  m=len(S & Q);delta=int(t in D);dot=sum(x*y for x,y in zip(v,y))%p
  assert dot==(m-delta)%p
  rem=v[:]
  for row,c in zip(hred,piv):
   d=rem[c];rem=[(x-d*z)%p for x,z in zip(rem,row)]
  nonstab=any(rem)
  if dot:
   assert nonstab and len(S)==k
   witnesses.append({'t':t,'support':sorted(S),'m':m,'delta':delta,'separator_dot':dot})
  moments.append(m)
 assert sum(moments)==k*k and sum(x*x for x in moments)==k*k+n-1
 out={'p':p,'n':n,'primitive_polynomial_coeffs_low_to_high':list(ff.f)+[1],
      'primitive_element':[0,1,0],'alpha_to_n':ff.pow(alpha,n),'D':sorted(D),'Q':sorted(Q),
      'rank_H':len(piv),'rank_A':len(rref(A,p)[1]),'H_symplectic_isotropic':True,
      'all_line_vectors_centralize':True,'kernel_separator_exact':True,
      'moments':[sum(moments),sum(x*x for x in moments)],'m_histogram':dict(Counter(moments)),
      'nonzero_separator_count':len(witnesses),'witness':witnesses[0],
      'witness_weight':k,'seconds':time.monotonic()-start,
      'source_reported_dmin':{3:3,5:6,7:'>=8',11:'>=5; conjectured 12'}[p]}
 return out

if __name__=='__main__':
 results=[run(p) for p in [3,5,7,11]]
 print(json.dumps({'checks':results,'arithmetic':'exact integer operations modulo p; cubic irreducibility certified by no roots; multiplicative primitivity by prime-factor order test'},indent=2))

def nullspace(a,p):
 rr,piv=rref(a,p);nf=len(a[0]);free=[c for c in range(nf) if c not in piv];out=[]
 for c in free:
  x=[0]*nf;x[c]=1
  for row,j in zip(rr,piv): x[j]=-row[c]%p
  out.append(x)
 return out

def small_distance(p,maxw):
 ff,alpha=find_field(p);n=p*p+p+1
 D={i for i in range(n) if ff.tr(ff.pow(alpha,i))==ff.zero}
 Q={i for i in range(n) if ff.tr(ff.pow(alpha,2*i))==ff.zero}
 A=[[int((i-j)%n in D) for j in range(n)] for i in range(n)]
 M=[[int((i-j)%n in Q) for j in range(n)] for i in range(n)]
 B=matmul(M,A,p);H=[a+b for a,b in zip(A,B)];rr,piv=rref(H,p)
 cent=[b+[(-x)%p for x in a] for a,b in zip(A,B)]
 searched=[]
 for w in range(1,maxw+1):
  count=0
  for supp in itertools.combinations(range(n),w):
   count+=1;cols=list(supp)+[x+n for x in supp]
   for small in nullspace([[row[c] for c in cols] for row in cent],p):
    v=[0]*(2*n)
    for c,x in zip(cols,small):v[c]=x
    rem=v[:]
    for row,c in zip(rr,piv):
     d=rem[c];rem=[(x-d*y)%p for x,y in zip(rem,row)]
    if any(rem):
     assert matvec(cent,v,p)==[0]*n
     return {'p':p,'dmin':w,'support':list(supp),'z':[v[x] for x in supp],'x':[v[x+n] for x in supp],'completed_lower_weights':searched,'supports_checked_at_witness_weight':count}
  searched.append({'weight':w,'supports_checked':count,'all_centralizer_kernels_contained_in_stabilizer':True})
 return {'p':p,'dmin_lower':maxw+1,'completed_lower_weights':searched}
```

`/tmp/op-kh25/source-example-check.py`

```python
import sys,json
sys.path.insert(0,'/tmp/op-kh25')
from check import F3,factors
p=3;ff=F3(p,(1,1,2));alpha=(0,1,0);n=13
order=next(i for i in range(1,27) if ff.pow(alpha,i)==ff.one)
D=[i for i in range(n) if ff.tr(ff.pow(alpha,i))==ff.zero]
Q=[i for i in range(n) if ff.tr(ff.pow(alpha,2*i))==ff.zero]
print(json.dumps({'p':p,'polynomial':[1,1,2,1],'order_alpha':order,'trace_one':ff.tr(ff.one),'D_by_definition':D,'Q_by_definition':Q,'appendix_D_printed':[2,3,6,8],'appendix_Q_printed':[0,7,8,11],'appendix_Q_equals_inverse_doubling_D':set([0,7,8,11])=={pow(2,-1,n)*i%n for i in [2,3,6,8]},'severity':'source worked-example inconsistency, not target/route counterexample'},indent=2))
```

`/tmp/op-kh25-stage-b/p3-distance-runner.py`

```python
import sys, json
sys.path.insert(0, "/tmp/op-kh25")
from check import small_distance
print(json.dumps(small_distance(3, 3), indent=2))
```

## ASSUMED-UNVERIFIED

The preregistration literature readings are orchestrator-reported. Bounded
search does not establish exhaustive novelty or priority. Source-reported
lower bounds at $p=5,7,11$ are not reproduced by the finite candidate checks.
The prime-power, higher-dimensional and general lower-bound extensions
remain open.
