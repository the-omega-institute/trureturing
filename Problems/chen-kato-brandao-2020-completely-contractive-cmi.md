---
slug: chen-kato-brandao-2020-completely-contractive-cmi
bibkey: chen2020mpdoparent
doi: null
url: https://arxiv.org/abs/2010.14682v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/ChenKatoBrandaoCMIRefutation.result
---

# Chen–Kato–Brandão completely contractive CMI data processing

## Problem

Chi-Fang Chen, Kohtaro Kato and Fernando G. S. L. Brandão,
*Matrix Product Density Operators: when do they have a local parent Hamiltonian?*,
arXiv:2010.14682v3, Section III.C, Conjecture III.1:

> For any channel $\mathcal E:C\rightarrow C'$ with trivial correctable algebra
> $\mathcal A(\mathcal E)=\mathbb C I$, there exists a constant $\eta<1$ such that
> for any tripartite system $ABC$ and any state $\rho_{ABC}$, it holds that
> $I(A:C'|B)_{\mathcal E(\rho)}\le\eta I(A:C|B)_\rho$.

Equation (22) defines the whole-space algebra as
$\mathcal A(\mathcal E)=\mathrm{Alg}\{O:[O,K_i^\dagger K_j]=0\ \forall i,j\}$.
Equation (1) defines
$I(A:C|B)=S(AB)+S(BC)-S(B)-S(ABC)$, with von Neumann entropy in bits.
The Lean expression uses the same eigenvalue entropy in nats; all terms are
multiplied by the common positive factor $\log 2$. Singular density matrices
are part of the source's domain.

## Motivation

The frozen `result : ¬ claim` refutes the source's universal statement.
Its channel has only scalar correctable observables on the whole input
space, yet preserves a bit encoded in two selected preparations. Global
correctability and recoverability on a chosen support impose different
requirements.

## Gap

[Preregistration #13891](https://github.com/the-omega-institute/trureturing/issues/13891)
records the verbatim conjecture, its complete quantifiers, Tier 1 status,
literature checks, the refutation route and the fixed Lean conventions.
The recorded search scope is arXiv v3, MathDB, the follow-up
arXiv:2608.27171v1 and the repository. MathDB reports zero solutions;
no settlement was found in that searched scope. The follow-up's §7.2
correlation-decay result assumes a full-rank Choi matrix for each channel;
it does not settle the scalar whole-space correctable-algebra conjecture.
This is a paper result, not a Lean result here. These bounded checks do
not establish exhaustive priority.

## Route

For $n>0$ and $0<p<1$, use
$K_{j,0}=\sqrt{1-p}\,|j\rangle\langle j|$ and
$K_{j,1}=\sqrt p\,|j+1\bmod n\rangle\langle j|$.
The diagonal Kraus products force every commuting observable to be
diagonal. Adjacent cross-products force consecutive diagonal entries to
agree, and cyclic induction makes the observable scalar.

The settling witness has $n=n'=4$, $p=1/2$, $d_A=2$, $d_B=1$.
Its input is diagonal with weights $1/2$ at $((0,0),0)$ and $((1,0),2)$.
Its output has weights $1/4$ at $((0,0),0)$, $((0,0),1)$,
$((1,0),2)$ and $((1,0),3)$.
The literal four-term CMI is $\log 2>0$ on both matrices.
The asserted inequality would give $\log 2\le\eta\log 2$, which contradicts
$\eta<1$.

The public surface is `correctable`, `entropy`, `cmi`, `claim`, and `result`.
The theorem's conservative `proof_shape` is `bind-only`; its
`escape_witness` is none and its admission basis is `open-problem-resolution`.
Every bind-only private helper is consumed on the settling proof's live
path. Utility is `certified-instance` with a typed `refutes` edge to `claim`.

## Falsifier

A mismatch with the source's whole-input-space algebra, exclusion of
singular states, a failure of Kraus normalization or density positivity,
or unequal CMIs at the witness would invalidate the refutation.
The kernel-checked proof uses the literal source algebra, a positive
trace-one input, normalized Kraus matrices, the actual local Kraus action
and literal partial traces. There is no additional rank, support or state
restriction in `claim`.

## Evidence

`D5/S3/Quantum/Information/ChenKatoBrandaoCMIRefutation.result` proves
`¬ claim` with axiom closure contained in
`{propext, Classical.choice, Quot.sound}`. Its Scribe carries a `Refuted`
`OpenProblemResolutionClaim` on that declaration. `spectralEntropy` is
reused at its original frozen owner with its mathematical expression intact.

Information-escape registration is paused under CLAUDE.md §3.9.

## Triage

Tier 1; external named conjecture; settlement Refuted. No atom or coverage
step applies to this settlement.

### What the settlement shows

- **Proved in this module — whole-space correctability.** For every
  $n>0$ and $0<p<1$, `family_correctable` proves that the family above has
  scalar whole-input-space correctable algebra. `family_normal` proves
  its Kraus normalization for $0\le p\le1$. Both are private consumed
  helpers of `result`.
- **Proved in this module — selected preparations.** At $n=4$,
  $p=q=1/2$ and trivial $B$, `witness_action`, `witness_cmi` and
  `output_cmi` give equal positive CMIs. The selected inputs have disjoint
  output supports, so their classical bit survives even though the
  whole-space algebra is scalar. This also supplies an equality case
  against the strict inequality printed as Proposition III.3; that
  proposition is not an additional public Lean theorem here.
- **Proved on paper — general-family equality (not a Lean result here).**
  For every $n\ge4$ and $p,q\in(0,1)$, take
  $\rho_{AC}=q|0,0\rangle\langle0,0|+(1-q)|1,2\rangle\langle1,2|$
  and any independent finite-dimensional state $\rho_B$. With
  $h(t)=-t\log t-(1-t)\log(1-t)$, the input entropies are
  $S(A)=h(q)$ and $S(C)=S(AC)=h(q)$. The two selected preparations
  have disjoint output supports $\{0,1\}$ and $\{2,3\}$, with
  conditional weights $(1-p,p)$. The output spectrum therefore has
  weights $q(1-p),qp,(1-q)(1-p),(1-q)p$, giving
  $S(C')=S(AC')=h(q)+h(p)$ while $S(A)=h(q)$ is unchanged.
  Tensoring the independent $B$ adds $S(B)$ to each joint entropy
  containing $B$, so these terms cancel in both four-term CMIs:
  $I(A:C|B)=I(A:C'|B)=h(q)>0$. This paper derivation extends the
  module's $n=4$, $p=q=1/2$, trivial-$B$ instance; the general
  entropy family is not kernel-certified here.
- **Computed — general-family examples.** The NumPy script below checks
  $n\in\{4,5,6,7,8\}$,
  $p\in\{0.01,0.1,0.25,0.5,0.73,0.99\}$,
  $q\in\{0.03,0.2,0.5,0.8,0.97\}$ and $d_B\in\{1,2\}$,
  with independent $B$ weights $(0.37,0.63)$ in dimension two.
  All 300 cases have commutant dimension one and input/output CMI
  equal to $h(q)=-q\log q-(1-q)\log(1-q)$ within the recorded tolerance.
  The maximum absolute CMI error is `4.440892098500626e-16`.
  **Open:** a separate Lean theorem for arbitrary $n\ge4$, $p,q\in(0,1)$
  and arbitrary independent $B$; this grid is not a proof of that extension.
- **Computed — faithful input states.** For
  $\rho_\delta=(1-\delta)\rho+\delta I/(2n)$, the same script checks
  $n\in\{4,5,6,7,8\}$, $p\in\{0.1,0.5,0.9\}$,
  $q\in\{0.2,0.5,0.8\}$ and
  $\delta\in\{10^{-1},10^{-2},10^{-3},10^{-4},10^{-6},10^{-8}\}$.
  All 270 input and output matrices are positive definite. At
  $\delta=10^{-8}$, the output/input CMI ratios range from
  `0.9999999110153958` to `0.9999999680697633`.
  **Open:** kernel formalization of the limit of this ratio as
  $\delta\downarrow0$. Continuity of finite-dimensional entropy would
  transfer the positive equality at the singular endpoint to a limiting
  ratio of one; the finite grid alone cannot certify the limit or refute
  a uniform contraction bound restricted to faithful states.
- **Computed — support-sensitive recovery mechanism.** The exact SymPy
  script below uses $\sigma=\mathrm{diag}(1/2,0,1/2,0)$,
  $F=\mathrm{diag}(1,0,-1,0)$ and the Petz recovery map
  $R(X)=\mathrm{diag}(X_{00}+X_{11},0,X_{22}+X_{33},0)$.
  It verifies $R(\mathcal E(\sigma))=\sigma$ and, for
  $Z=R\circ\mathcal E$, $Z^\dagger F=F$ but
  $Z^\dagger(F^2)=I\ne F^2$. Thus this dual fixed space is not closed
  under multiplication.
  **Open:** formalizing this recovery-map computation and the general
  overlap-graph characterization as separate content.
- **Proved on paper — failed source step (not a Lean result here).**
  The argument supporting Proposition III.3 treats the dual fixed
  space of the Petz recovered map for a singular reference state as a
  multiplication algebra (`main.tex`, lines 1080–1099, proof of
  `lem:equalMI`), invoking the appendix's fixed-space claim (`invar`,
  line 1686). The computed $Z^\dagger F=F$ and
  $Z^\dagger(F^2)\ne F^2$ above disprove that algebra claim in this
  case. Bény–Kempf–Kribs, arXiv:0705.1574, Theorem 9, is a paper
  result using the support projection $P$ in
  $[P K_i^\dagger K_jP,O]=0$. A correctable algebra on the support
  $P=\mathrm{diag}(1,0,1,0)$ does not give a correctable observable
  on the whole input space; the support cannot be dropped.
- **Proved on paper — follow-up boundary (not a Lean result here).**
  arXiv:2608.27171v1, §7.2, Propositions 23–24 and the paragraph
  following Proposition 24, assumes full-rank Choi matrices for its
  correlation-decay result. This stronger noise hypothesis does not
  settle the scalar whole-space correctable-algebra conjecture.
- **Open — nearest surviving multi-step statement.** After $n-1$ steps,
  the diagonal transition kernel has all cyclic displacements with
  positive weights
  $\binom{n-1}{k}p^k(1-p)^{n-1-k}$.
  The proposed forgetful-component weight is
  $\alpha=n\min_{0\le k\le n-1}\binom{n-1}{k}p^k(1-p)^{n-1-k}$.
  A separate proof must establish the channel decomposition and its
  ancilla-uniform CMI contraction bound. Neither the decomposition nor
  a bound with factor $1-\alpha$ is kernel-certified or numerically
  tested by this delivery.
- **Proved on paper — source consequence.** The displayed positive-CMI
  equality violates Proposition III.3's strict inequality; this is a
  paper consequence of the module's instance, not an additional Lean
  theorem here. **Open — MPDO consequences:** Proposition III.4's paper
  implication from Conjecture III.1 to exponential CMI decay supplies
  no unconditional conclusion once that conjecture is refuted.
  Exponential decay for every Y-shaped MPDO is not refuted by this witness. Sufficient
  conditions for that decay, including stronger noise or multi-step
  forgetfulness, remain separate questions. Source results with proofs
  independent of these assertions are outside the refutation's scope.

### Numerical family and faithful-state computation

Command: `python3 /tmp/op-ckb/checks.py`; exit code: `0`.
Dependencies: Python 3 and NumPy. Create `/tmp/op-ckb`, save this complete
script as `checks.py` there, then run the command. It writes `checks.json`.
SHA-256: `243f86aaf2465aefb69f889e4914a9cce6f65a036c089e750d87962eb05731b4`.

```python
import json, math, numpy as np
from pathlib import Path

def entropy(M):
    v=np.linalg.eigvalsh(M)
    assert min(v)>=-1e-12
    v=v[v>1e-15]
    return float(-(v*np.log(v)).sum())
def ptr(M,dims,keep):
    a=M.reshape(tuple(dims)*2)
    left=list(dims)
    for k in reversed(range(len(dims))):
        if k not in keep:
            a=np.trace(a,axis1=k,axis2=k+len(left));left.pop(k)
    return a.reshape(math.prod(left),math.prod(left))
def cmi(M,dims):
    return entropy(ptr(M,dims,[0,1]))+entropy(ptr(M,dims,[1,2]))-entropy(ptr(M,dims,[1]))-entropy(M)
def kraus(n,p):
    out=[]
    for j in range(n):
        for b in (0,1):
            K=np.zeros((n,n),dtype=complex)
            K[(j+b)%n,j]=math.sqrt(p if b else 1-p)
            out.append(K)
    return out
rows=[]
for n in range(4,9):
 for p in (.01,.1,.25,.5,.73,.99):
  Ks=kraus(n,p)
  normal=sum(K.conj().T@K for K in Ks)
  assert np.max(np.abs(normal-np.eye(n)))<1e-14
  # Exact zero pattern establishes connected overlap; full commutant rank is also computed.
  products=[Ks[j].conj().T@Ks[k] for j in range(2*n) for k in range(2*n)]
  comm=np.vstack([np.kron(P.T,np.eye(n))-np.kron(np.eye(n),P) for P in products])
  rank=int(np.linalg.matrix_rank(comm,tol=1e-10))
  assert rank==n*n-1
  for q in (.03,.2,.5,.8,.97):
   for dB in (1,2):
    bweights=np.array([1.]) if dB==1 else np.array([.37,.63])
    diag=np.zeros((2,dB,n));diag[0,:,0]=q*bweights;diag[1,:,2]=(1-q)*bweights
    rho=np.diag(diag.flatten())
    Ls=[np.kron(np.eye(2*dB),K) for K in Ks]
    out=sum(L@rho@L.conj().T for L in Ls)
    before=cmi(rho,[2,dB,n]);after=cmi(out,[2,dB,n])
    h=-q*math.log(q)-(1-q)*math.log(1-q)
    assert abs(before-h)<1e-12 and abs(after-h)<1e-12
    rows.append(dict(n=n,p=p,q=q,dB=dB,commutant_dimension=n*n-rank,input_cmi=before,output_cmi=after,expected=h))
pert=[]
for n in range(4,9):
 for p in (.1,.5,.9):
  for q in (.2,.5,.8):
   diag=np.zeros(2*n);diag[0]=q;diag[n+2]=1-q;rho=np.diag(diag)
   Ks=kraus(n,p);Ls=[np.kron(np.eye(2),K) for K in Ks]
   for delta in (.1,.01,.001,.0001,.000001,.00000001):
    rd=(1-delta)*rho+delta*np.eye(2*n)/(2*n)
    out=sum(L@rd@L.conj().T for L in Ls)
    before=cmi(rd,[2,1,n]);after=cmi(out,[2,1,n]);ratio=after/before
    assert min(np.linalg.eigvalsh(rd))>0 and min(np.linalg.eigvalsh(out))>0
    assert 0<ratio<=1+1e-12
    pert.append(dict(n=n,p=p,q=q,delta=delta,input_cmi=before,output_cmi=after,ratio=ratio,min_input_eig=float(np.linalg.eigvalsh(rd).min()),min_output_eig=float(np.linalg.eigvalsh(out).min())))
summary={'grid_count':len(rows),'perturbation_count':len(pert),'max_cmi_error':max(max(abs(r['input_cmi']-r['expected']),abs(r['output_cmi']-r['expected'])) for r in rows),'delta_1e_8_ratio_range':[min(r['ratio'] for r in pert if r['delta']==1e-8),max(r['ratio'] for r in pert if r['delta']==1e-8)],'anchor':[r for r in rows if r['n']==4 and r['p']==.5 and r['q']==.5],'perturbation_anchor':[r for r in pert if r['n']==4 and r['p']==.5 and r['q']==.5]}
Path('/tmp/op-ckb/checks.json').write_text(json.dumps({'summary':summary,'grid':rows,'perturbations':pert},indent=2)+'\n')
print(json.dumps(summary,indent=2))
```

### Exact recovery-map computation

Command: `python3 /tmp/op-ckb/exact-check.py`; exit code: `0`.
Dependencies: Python 3 and SymPy. Save this complete script as
`/tmp/op-ckb/exact-check.py`; it writes `exact-check.json`.
SHA-256: `6ea0dd377f892073635a020594091b2992b70ae71e14ec2efc9c1ebf552fb6c1`.

```python
import sympy as s, json
from pathlib import Path
n=4; I=s.eye(n)
K=[]
for j in range(n):
 for b in (0,1):
  M=s.zeros(n);M[(j+b)%n,j]=1;K.append(M)
normal=sum((M.T*M/2 for M in K),s.zeros(n));assert normal==I
unital=sum((M*M.T/2 for M in K),s.zeros(n));assert unital==I
constraints=s.zeros(0,n*n)
for A in K:
 for B in K:
  P=A.T*B/2
  constraints=constraints.col_join(s.kronecker_product(P.T,I)-s.kronecker_product(I,P))
rank=constraints.rank();assert rank==15
sigma=s.diag(s.Rational(1,2),0,s.Rational(1,2),0)
def E(X):return sum((M*X*M.T/2 for M in K),s.zeros(n))
def R(X):return s.diag(X[0,0]+X[1,1],0,X[2,2]+X[3,3],0)
def Edag(X):return sum((M.T*X*M/2 for M in K),s.zeros(n))
def Rdag(X):return s.diag(X[0,0],X[0,0],X[2,2],X[2,2])
F=s.diag(1,0,-1,0)
assert E(sigma)==I/4 and R(E(sigma))==sigma
assert Edag(Rdag(F))==F
assert Edag(Rdag(F*F))==I and F*F!=I
out={'kraus_normal':True,'unital':True,'commutant_rank':rank,'commutant_dimension':16-rank,'sigma':[str(v) for v in sigma.diagonal()],'E_sigma':[str(v) for v in E(sigma).diagonal()],'F':[str(v) for v in F.diagonal()],'Z_dual_F':[str(v) for v in Edag(Rdag(F)).diagonal()],'F_squared':[str(v) for v in (F*F).diagonal()],'Z_dual_F_squared':[str(v) for v in Edag(Rdag(F*F)).diagonal()],'fixed_space_not_algebra':True}
Path('/tmp/op-ckb/exact-check.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
```

## ASSUMED-UNVERIFIED

The recorded literature checks are bounded searches, not an exhaustive
priority certification. arXiv:2608.27171v1 §7.2 assumes full-rank Choi
matrices for its correlation-decay paper result and does not settle the
scalar whole-space correctable-algebra conjecture; it is not a Lean
result here.
The numerical tolerances certify only the listed finite grids; they are
not Lean proofs. The full-rank limiting ratio, overlap-graph theorem,
multi-step contraction and Y-shaped MPDO extensions remain open here.
