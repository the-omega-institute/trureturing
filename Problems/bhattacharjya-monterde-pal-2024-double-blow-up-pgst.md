---
slug: bhattacharjya-monterde-pal-2024-double-blow-up-pgst
bibkey: bhattacharjyamonterdepal2024blowup
doi: 10.1088/1751-8121/ad6653
url: https://arxiv.org/abs/2308.13887v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/PathDoubleBlowUpPGSTRefutation.result
---

# Pretty good state transfer in double blow-ups of paths

## Problem

Bhattacharjya, Monterde and Pal, *Quantum walks on blow-up graphs*,
arXiv:2308.13887v2, J. Phys. A 57 (2024) 335303, Section 8, Conjecture 1:

> Let n = 2^t r − 1, where t ≥ 2 and r is an odd prime number. If u is a multiple of 2^{t−1}, then PGST does not occur between (0, u) and (1, u) in the double blow-up of P_n.

Section 12 asks whether this conjecture is true and, if not, for which
parameters pretty good state transfer occurs. The source uses
$U(s)=\exp(isA)$. PGST means the existence of a sequence of real times
whose transition-entry moduli converge to one. Source vertex $u=j+1$
is represented by $j:\mathrm{Fin}(n)$; the blow-up carrier is
$\mathrm{Fin}(2)\times\mathrm{Fin}(n)$ and adjacency ignores the copy coordinate.
Issue [#14649](https://github.com/the-omega-institute/trureturing/issues/14649)
preregisters BMP-1, the literal definitions, the tier-1 classification,
the witness and the literature readings.

## Motivation

The frozen declaration
`D5/S3/Quantum/Dynamics/PathDoubleBlowUpPGSTRefutation.result`
proves the negation of the conjecture without extra hypotheses.
The witness is $t=2$, $r=3$, $n=11$ and source vertex $u=4$,
represented by index $3:\mathrm{Fin}(11)$. It establishes PGST between
the twins $(0,4)$ and $(1,4)$ in the 22-vertex double blow-up.

## Gap

The preregistration attributes the candidate and proposed classification to
codex-cli quick-track search seat `s7999-codex-search-a-r15`. The Claude Code
orchestrator's recorded source and literature checks cover arXiv:2308.13887v2,
MathDB p/359672 (zero listed solutions), arXiv:2504.11585,
arXiv:2510.05306 and arXiv:2505.07982; no settlement was found in that scope.
These are attributed literature readings, not an exhaustive priority claim.
The journal text's agreement with the arXiv conjecture is seat-reported.

## Route

The settling module's private helpers apply the idempotent power identity
and Kronecker monoid homomorphism, then sum the exponential series.
Its `twin_amplitude` gives

$U_B(s)_{(0,u),(1,u)}=(U_A(2s)_{u,u}-1)/2$.

The settling module uses the imported
`TopEigenspace.sine_mode_eigenvector` and
`EnergyEigenstateStationarity.exp_mulVec_of_eigenvector` to obtain the
sine expansion of the path propagator. At source vertex 4, the support is

$\{\pm(\sqrt6+\sqrt2)/2,\ \pm\sqrt3,\ \pm1,\ \pm(\sqrt6-\sqrt2)/2\}$,

with weight $1/8$ on each eigenvalue. The general supporting module
`BiquadraticKroneckerTimes.biquadratic_independent` supplies the required
four-coefficient independence; its `dense_circle_sequence` applies the
imported frozen `TorusOrbitClosure.result`. The resulting twin-transfer
times are $\tau_k=\pi/2+\pi m_k$. The original-path diagonal entry is
evaluated at $2\tau_k$, where all four cosines tend to $-1$; the twin entry
therefore tends to $-1$ and its modulus tends to one.

## Falsifier

The refutation would fail if the source definitions were mistranscribed,
if the sine weights or rational independence failed, or if the named
conjecture had an earlier published settlement. The delivered `claim`
retains all source quantifiers, primality, oddness and divisibility;
`result : ¬ claim` uses the admissible witness without additional assumptions.
A finite time-grid maximum alone cannot establish PGST or its absence.

## Evidence

The Lean axiom closure of every public declaration is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.
The supporting module admits through `escape-witness`, with named
content theorem `biquadratic_independent`.
The settling module admits through `open-problem-resolution` (#14649;
Refuted) and carries the certified instance refuting its literal `claim`.
Information-escape registration is paused under CLAUDE.md §3.9.

## Triage

### What the settlement shows

1. **Mechanism — proved in Lean, with a source-criterion argument.**
   The private `sine_weights` proves zero sine weight at modes 3, 6 and 9;
   `spectral_weights` gives the eight supported eigenvalues above, each
   with weight $1/8$. The source's relation
   $\theta_5-\theta_9+\theta_{11}=0$ needs
   $\theta_9=-\sqrt2$, absent at source vertex 4 because
   $\sin(3\pi)=0$. The private `sqrt_two_three_six_independent` and
   `frequency_character_independent` prove the independence used by
   `approximation_times`. The four positive supported frequencies are
   rationally independent: a relation among them expands to a relation
   on $1,\sqrt2,\sqrt3,\sqrt6$, whose coefficients vanish. Thus an integral
   zero relation on their positive and negative pairs has equal
   coefficients in each pair, and its total coefficient sum is even.
   This last implication is a paper argument applying source Theorem 3;
   the Lean proof constructs the PGST sequence directly.
2. **Corrected classification — computed in the stated finite scope.**
   For every eligible source vertex in $t\in\{2,3\}$ and
   $p\in\{3,5,7\}$, the exact integer-relation parity test agrees with
   $2^t\mid u$. There are 54 tested vertices. The computation constructs
   the cyclotomic coefficient matrix and checks a unimodular Smith
   decomposition, then tests every basis vector of the saturated integer
   relation lattice. Source Theorem 3 turns the computed parity predicate
   into the PGST criterion. This computation is not Lean-verified.
3. **Uniform corrected classification — open.**
   The search seat reports a proof of the proposed statement: for all
   $t\ge2$, odd primes $p$ and $2^{t-1}\mid u$, twin PGST occurs iff
   $2^t\mid u$. That general proof is not supplied by the delivered Lean
   declarations or by the finite computation. The complete parameter
   classification requested in Section 12 remains open here.
4. **Vertices 2, 6 and 10 of $P_{11}$ — proved in the source.**
   Section 8's odd-sum relation applies at these vertices: all three
   modes 5, 9 and 11 have nonzero sine weight, including $-\sqrt2$.
   The coefficient sum $1-1+1=1$ violates Theorem 3's parity condition.
   The exact finite computation below independently returns no PGST
   for source vertices 2, 6 and 10; this obstruction is not a new
   theorem in the settling module.
5. **Phase $-1$ recurrence — proved inside the Lean construction.**
   The local `hdiag` in `pgst_twins_vertex_four` proves
   $U_A(2\tau_k)_{4,4}\longrightarrow-1$, and its local `hamp` proves
   $U_B(\tau_k)_{(0,4),(1,4)}\longrightarrow-1$.
   These are sequence limits in the elaborated proof, without a new
   public recurrence declaration.
6. **Exact sedentariness and nonzero-time periodicity classification — open.**
   No computed or standalone formal classification of these properties
   is delivered. The phase limits above do not supply an asserted
   classification of every time or parameter.
7. **Consequences for the source — proved by a paper argument.**
   Theorem 3's support-sensitive criterion survives and agrees with the
   witness. Section 8's claim excluding every even vertex of $P_{11}$,
   and any use of that assertion in Remark 1, must be restricted to
   vertices whose support contains the obstruction. Conjecture 1 is
   false; this refutation does not negate unrelated source theorems.

### Numerical witness check

Command: `OPENBLAS_NUM_THREADS=1 python3 /tmp/op-bmp/check.py`; exit 0.
The SHA-256 of the complete script below is `b16ee2d101e206069409a46acd3258439ca525d785d47ce7db632cdfa9862d92`.
NumPy 2.4.2 gives the support
$\pm1.931852,\pm1.732051,\pm1,\pm0.517638$, each with weight 0.125.
On the half-open grid $[0,2000000)$ with step 0.05 (40000000 points),
the maximum sampled twin-entry modulus is 0.9998956621518383 at
$s=948055.7000000001$. The script uses the conjugate time convention,
which preserves the modulus for this real adjacency matrix. Its vertex-2
support includes $\pm\sqrt2$. These are numerical readings, not the
proof of PGST.

```python
import numpy as np
n=11
A=np.zeros((n,n))
for i in range(n-1): A[i,i+1]=A[i+1,i]=1
w,V=np.linalg.eigh(A)
u=3  # vertex 4 (1-indexed)
wt=V[u,:]**2
supp=[(round(w[k],6),round(wt[k],6)) for k in range(n) if wt[k]>1e-12]
print("support",supp)
# double blow-up A⊗J; amplitude between twins (0,u),(1,u) = (<e_u,exp(-2itA)e_u> - 1)/2
def amp(t): return (np.sum(wt*np.exp(-2j*t*w))-1)/2
best=0;bt=0
ts=np.arange(0,2e6,0.05)
for chunk in np.array_split(ts,400):
    a=np.abs((np.exp(-2j*np.outer(chunk,w))@wt-1)/2)
    k=a.argmax()
    if a[k]>best: best=a[k];bt=chunk[k]
print("max |amp| on [0,2e6] step .05:",best,"at t=",bt)
# u=2 (vertex 2, multiple of h/2 but not h): expected no PGST, bounded away
u2=1; wt2=V[u2,:]**2
print("support u=2",[(round(w[k],4),round(wt2[k],4)) for k in range(n) if wt2[k]>1e-12])
```

### Exact finite classification and time-grid readings

Command: `OPENBLAS_NUM_THREADS=1 python3 /tmp/op-bmp/probe-r1/triage.py`;
exit 0. SHA-256: `2b6e35f24a9cf0194eb1a7b3606dd503b8f84076824d6fe362c2532d7abbd42f`. Dependencies: SymPy 1.14.0 and NumPy 2.4.2.
To reproduce, save the complete source below at that path and create its
output directory `/tmp/op-bmp/probe-r1`. The JSON output contains all
54 vertices, support modes, saturated integer-kernel basis parities,
and an odd relation for each rejected vertex. The independent amplitude
grid is $[0,20000]$ with step 0.1 (200001 points); its maxima carry no
infinite-time conclusion.

| $t$ | $p$ | $n$ | eligible vertices | parity criterion true | parity criterion false |
| --- | --- | --- | --- | --- | --- |
| 2 | 3 | 11 | 5 | 4, 8 | 2, 6, 10 |
| 2 | 5 | 19 | 9 | 4, 8, 12, 16 | 2, 6, 10, 14, 18 |
| 2 | 7 | 27 | 13 | 4, 8, 12, 16, 20, 24 | 2, 6, 10, 14, 18, 22, 26 |
| 3 | 3 | 23 | 5 | 8, 16 | 4, 12, 20 |
| 3 | 5 | 39 | 9 | 8, 16, 24, 32 | 4, 12, 20, 28, 36 |
| 3 | 7 | 55 | 13 | 8, 16, 24, 32, 40, 48 | 4, 12, 20, 28, 36, 44, 52 |

```python
import json,time,hashlib,pathlib
import numpy as np
import sympy as sp
from sympy.polys.matrices import DomainMatrix
from sympy.polys.matrices.normalforms import smith_normal_decomp
base=pathlib.Path('/tmp/op-bmp/probe-r1')
x=sp.Symbol('x')
start=time.monotonic()
rows=[]
for t in (2,3):
 for p in (3,5,7):
  N=2**t*p
  order=2*N
  f=sp.Poly(sp.cyclotomic_poly(order,x),x,domain=sp.ZZ)
  degree=f.degree()
  eligible=list(range(2**(t-1),N,2**(t-1)))
  cols=[]
  for k in range(1,N):
   r=sp.Poly(x**k+x**(order-k),x,domain=sp.ZZ).rem(f)
   cols.append(sp.Matrix([r.nth(j) for j in range(degree)]))
  for u in eligible:
   support=[k for k in range(1,N) if k*u%N != 0]
   M=sp.Matrix.hstack(*(cols[k-1] for k in support))
   dm=DomainMatrix.from_Matrix(M).convert_to(sp.ZZ)
   D,S,T=smith_normal_decomp(dm)
   assert D == S*dm*T
   Sm,Tm,Dm=S.to_Matrix(),T.to_Matrix(),D.to_Matrix()
   assert abs(Sm.det())==1 and abs(Tm.det())==1
   rank=sum(Dm[i,i]!=0 for i in range(min(Dm.shape)))
   basis=[Tm[:,j] for j in range(rank,Tm.cols)]
   assert all(M*v == sp.zeros(degree,1) for v in basis)
   odd=[v for v in basis if int(sum(v))%2]
   pgst=(len(odd)==0)
   assert pgst==(u%2**t==0),(t,p,u)
   rows.append({'t':t,'p':p,'n':N-1,'vertex':u,'support_modes':support,'support_size':len(support),'rational_rank':rank,'integer_kernel_rank':len(basis),'kernel_basis_sum_parities':[int(sum(v))%2 for v in basis],'odd_relation':None if not odd else [int(a) for a in odd[0]],'computed_character_criterion':pgst,'divisible_by_2_to_t':u%2**t==0})
  # Deterministic finite continuous-time grid; entries are real by bipartite symmetry.
  ks=np.arange(1,N//2)
  theta=2*np.cos(np.pi*ks/N)
  weights=4/N*np.sin(np.pi*np.outer(ks,np.array(eligible))/N)**2
  assert np.max(np.abs(weights.sum(axis=0)-1))<1e-12
  best=np.zeros(len(eligible));best_t=np.zeros(len(eligible))
  for first in range(0,200001,10000):
   times=np.arange(first,min(first+10000,200001))*0.1
   amps=(1-np.cos(2*np.outer(times,theta))@weights)/2
   imax=amps.argmax(axis=0);vals=amps[imax,np.arange(len(eligible))]
   improve=vals>best
   best_t[improve]=times[imax[improve]];best[improve]=vals[improve]
  for row in rows[-len(eligible):]:
   j=eligible.index(row['vertex'])
   row['finite_grid_max_amplitude']=float(best[j]);row['finite_grid_argmax_time']=float(best_t[j])
summary=[]
for t in (2,3):
 for p in (3,5,7):
  group=[r for r in rows if r['t']==t and r['p']==p]
  summary.append({'t':t,'p':p,'n':2**t*p-1,'eligible_vertices':len(group),'computed_yes':[r['vertex'] for r in group if r['computed_character_criterion']],'computed_no':[r['vertex'] for r in group if not r['computed_character_criterion']],'finite_grid_yes_range':[min(r['finite_grid_max_amplitude'] for r in group if r['computed_character_criterion']),max(r['finite_grid_max_amplitude'] for r in group if r['computed_character_criterion'])],'finite_grid_no_range':[min(r['finite_grid_max_amplitude'] for r in group if not r['computed_character_criterion']),max(r['finite_grid_max_amplitude'] for r in group if not r['computed_character_criterion'])]})
result={'status':'computed; not Lean-verified','method':'Exact cyclotomic integer coefficient matrix for eigenvalues 2 cos(k pi/N); support is N not dividing k*u. Unimodular Smith decomposition gives the saturated integer relation lattice. Theorem 3 parity criterion evaluated on every integer-kernel basis column. Independently sample the twin amplitude on a finite time grid.','grid':{'range':[0,20000],'step':0.1,'points':200001},'scope':'All 54 source-numbered vertices u with 2^(t-1) dividing u, for t=2,3 and p=3,5,7.','limitations':['Finite amplitude maxima do not prove PGST or its absence.','The symbolic parity computation and general use of source Theorem 3 are not formalized in Lean.','No conclusion for other t or p is established by this triage.'],'versions':{'sympy':sp.__version__,'numpy':np.__version__},'program_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),'wall_seconds':time.monotonic()-start,'summary':summary,'vertices':rows}
(base/'triage.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'summary':summary,'wall_seconds':result['wall_seconds'],'readings':str(base/'triage.json')},indent=2))
```

## ASSUMED-UNVERIFIED

The journal version's identical conjecture and the search seat's uniform
classification proof are seat-reported. Literature priority is limited to
the searches recorded in #14649. Neither the floating-point grids nor the
finite Smith-lattice computation is kernel-verified. No uniform extension
beyond the stated finite scope, exact sedentariness classification or
nonzero-time periodicity classification is claimed.
