---
slug: lindblad-guerrero-2025-anderson-symmetry-converse-refutation
bibkey: lindbladguerrero2025anderson
doi: null
url: https://arxiv.org/abs/2512.00278v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/AndersonSymmetryConverseRefutation.result
---

# A bad Anderson potential without nontrivial shared symmetry

## Problem

O. Lindblad and E. Guerrero, *Simple Eigenvalues and Non-vanishing Eigenvectors
of the Anderson Model*, arXiv:2512.00278v1, ask after Theorem 1.3:

> Conversely, we also ask whether every bad potential shares a nontrivial symmetry with the laplacian.

Section 4 also states:

> In general, we do not know whether the converse of lemma 3.2 is true.

On the cycle with $L>2$, the source's operator is
$$(H_t\psi)(j)=\sum_{k\sim j}(\psi(j)-\psi(k))+t v_j\psi(j).$$
Definition 1.1 calls $V=\operatorname{diag}(v)$ bad when for every real $t$
at least one of simple eigenvalues and non-vanishing eigenvectors fails.
The target LG-CONV quantifies over every $L>2$ and every
$v:\operatorname{Fin}L\to\mathbb R$ taking values in $\{-1,1\}$.
Issue #13591 fixes nontrivial shared symmetry as a real orthogonal matrix
$O\ne I$, $O\ne-I$, commuting with both $\Delta$ and $V$.
Both sufficient branches of Lemma 3.2 exclude $-I$, so refuting this weak
reading also refutes their converse. A one-dimensional counterexample is a
counterexample to the general-grid question. An affine change
$V\mapsto\alpha V+\beta I$, $\alpha\ne0$, reparametrizes the coupling and
shifts eigenvalues without changing eigenvectors or shared commutants;
normalization to $\{-1,1\}$ therefore represents any two distinct values.

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Simple eigenvalues | `bad`: `∀ μ : ℂ, H.charpoly.IsRoot μ → H.charpoly.rootMultiplicity μ = 1`, with `H = (SimpleGraph.cycleGraph L).lapMatrix ℂ + (t : ℂ) • Matrix.diagonal (fun j => (v j : ℂ))` | Each characteristic-polynomial root has algebraic multiplicity one. |

## Motivation

The frozen declaration
`D5/S3/Combinatorics/Graph/AndersonSymmetryConverseRefutation.result`
refutes LG-CONV using the eight-cycle potential
$v=(1,1,1,1,-1,1,-1,-1)$. The converse would identify all bad potentials
through shared symmetries and support symmetry-based counting. This example
shows a persistent zero in an eigenvector even though every shared commuting
matrix is scalar.

## Gap

Issue #13591 supplies the verbatim source, the Tier-1 literature assessment,
the symmetry convention and the completion criteria. Its exact-title,
author and identifier searches report no later proof or refutation in the
searched scope. Citation-index coverage is incomplete: ADS returned 405 and
Google Scholar returned 429. These are preregistration readings, rather than
an exhaustive literature or priority claim.
The paper's prime-cycle theorem does not answer the composite-cycle question.

## Route

Put $\Delta=2I-A$, where $A$ is the adjacency matrix of the eight-cycle.
For every $t\in\mathbb R$, set $a=\sqrt{t^2+2}-t$ and
$$z=(1,0,-1,a,1-a^2,-2t,1,-a).$$
Then $a^2+2ta-2=0$ and $H_tz=(2+a+t)z$. Since $z_0=1$ and $z_1=0$,
non-vanishing fails at every coupling.
The exact finite commutator equations imply $X=X_{00}I$ whenever
$X\Delta=\Delta X$ and $XV=VX$. Orthogonality forces $X_{00}^2=1$,
so there is no shared orthogonal symmetry other than $I$ and $-I$.
The implementation reuses Mathlib's `SimpleGraph.cycleGraph`, `lapMatrix`
and `Matrix.charpoly`; simple spectrum is the inline condition
`∀ μ : ℂ, H.charpoly.IsRoot μ → H.charpoly.rootMultiplicity μ = 1`.

## Falsifier

The refutation targets the literal universal badness predicate and the
preregistered exclusion of both scalar symmetries. Allowing $-I$ would make
the symmetry conclusion hold for every potential. A reading of badness
requiring failure of both spectral conditions would be a different statement
from Definition 1.1. The theorem establishes the eight-cycle counterexample;
it does not infer universal badness at other lengths from sampled couplings.

## Evidence

The canonical Lean source is
`D5/S3/Combinatorics/Graph/AndersonSymmetryConverseRefutation.lean`.
Its settling declaration has type `result : ¬ claim`; `potential_bad` and
`scalar_commutant` are used by `result`, and `cycle8_lap` is used by
`scalar_commutant`. The public surface consists of `nonvanishingEigenvectors`,
`bad`, `sharedSymmetry`, `claim` and `result`.
The proof uses only pinned Mathlib imports. The computed census and
length-nine checks are reproduced below with their full programs.

## Triage

Tier 1; `proof_shape: content` for `potential_bad` and `result`;
`escape_witness`: the all-couplings nodal eigenvector in `potential_bad`,
on the live proof path of `result`;
`scalar_commutant`: `proof_shape: bind-only`, `escape_witness: none`,
consumer `result`;
`admission_basis: open-problem-resolution (#13591; Refuted)`.
The helpers are consumed on the settling proof's live path.
`cycle8_lap` is a bind-only auxiliary declaration consumed by `scalar_commutant`.
Information-escape registration is paused under CLAUDE.md §3.9.

### What the settlement shows

- **Proved in this module:** LG-CONV fails at $L=8$. The witness is bad at
  every real coupling and has scalar shared commutant, so it admits no
  nontrivial shared orthogonal symmetry.
- **Computed:** for $3\le L\le12$, the census flags symmetry-free bad
  candidates at $L=8,9,12$, and none at $L\le7$, $L=10$ or $L=11$.
  The exact tested scope and numerical thresholds are given below. These
  finite sampled flags are not proofs of badness for every real coupling.
- **Computed:** at $L=9$, $v=(1,1,-1,1,1,-1,1,-1,-1)$ has numerical shared
  commutant dimension one. At $t=0.731$ its minimum eigenvalue gap is
  $0.14640748161689665$ and its minimum eigenvector-coordinate magnitude is
  $3.981463187258188\times10^{-16}$; the spectrum passes the simplicity
  threshold while non-vanishing fails the numerical threshold. The same
  two flags hold at the four census couplings. Uniform badness at $L=9$
  remains **open** here.
- **Proved in this module:** the failure mechanism at $L=8$ is a persistent
  nodal eigenbranch that cannot arise from a nontrivial shared symmetry.
  A symmetry-free invariant predicting such branches on other composite
  cycles is **open**.
- **Proved consequence at $L=8$:** counting only potentials with nontrivial
  shared symmetries does not exhaust bad potentials in the general
  composite-cycle setting. This refutation supplies no symmetry-counting
  upper bound for composite $L$. **Proved in the source:** the prime-cycle
  theorem and Theorem 1.3's probability lower bound stand; their arguments
  do not require the open converse. They are cited source results, not new
  theorems of this module.
- **Open:** determine exactly which composite $L$ admit counterexamples.
  The kernel-checked case is $L=8$; the sampled census suggests $L=9,12$
  and finds no candidate at $L=10$. Neither a general composite-length
  classification nor a minimal-length theorem is proved here.

### Census computation

Command: `python3 census.py`; exit code **0**.
The inline source below is that script, SHA-256 `6169bb180bdab2fc88fbf2453b7250f9bf826a0f246e0144601dc94c0b97783d`.
To reproduce from this dossier, save the code as `census.py` and run
`python3 census.py` with NumPy 2.2.5.
It enumerates every binary vector with $v_0=1$ for $3\le L\le12$.
The sign normalization removes the global-sign duplicate. Badness is tested
only at $t\in\{0.37,1.913,-2.71,5.3\}$. Simple eigenvalues require the
minimum gap to exceed $10^{-8}$, non-vanishing requires the minimum absolute
eigenvector entry to exceed $10^{-8}$, and the shared-commutant rank uses
SVD tolerance $10^{-9}$. The two count columns are numerical flags.

| $L$ | Flagged bad, $v_0=1$ | Flagged bad with scalar commutant |
| --- | ---: | ---: |
| 3 | 4 | 0 |
| 4 | 6 | 0 |
| 5 | 16 | 0 |
| 6 | 20 | 0 |
| 7 | 50 | 0 |
| 8 | 74 | 16 |
| 9 | 148 | 18 |
| 10 | 152 | 0 |
| 11 | 342 | 0 |
| 12 | 734 | 312 |

The eight-cycle check reports commutant dimension one. Its eigenvector
residuals at $t=0.3,-1.7,4.2$ are floating-point checks; the all-coupling
statement at $L=8$ comes from Lean.

```python
import numpy as np, itertools
from fractions import Fraction
def adj(L):
    A=np.zeros((L,L))
    for i in range(L): A[i,(i+1)%L]=A[(i+1)%L,i]=1
    return A
def commutant_dim(L,v):
    A=adj(L); V=np.diag(v); n=L
    rows=[]
    for M in (A,V):
        # X M - M X = 0, linear in vec(X)
        K=np.kron(np.eye(n),M.T)-np.kron(M,np.eye(n))
        rows.append(K)
    S=np.vstack(rows)
    return n*n-np.linalg.matrix_rank(S,tol=1e-9)
def bad(L,v,ts=(0.37,1.913,-2.71,5.3)):
    A=adj(L); D=2*np.eye(L)-A; V=np.diag(v)
    for t in ts:
        w,U=np.linalg.eigh(D+t*V)
        simple=np.min(np.diff(w))>1e-8
        nonvan=np.min(np.abs(U))>1e-8
        if simple and nonvan: return False
    return True
L=8; v=[1,1,1,1,-1,1,-1,-1]
print('L=8 witness: bad',bad(L,v),'commutant dim',commutant_dim(L,v))
# eigenvector check
for t in [0.3,-1.7,4.2]:
    r=np.sqrt(t*t+2); a=r-t; lam=2+r
    z=np.array([1,0,-1,a,1-a*a,-2*t,1,-a])
    H=2*np.eye(L)-adj(L)+t*np.diag(v)
    print('t',t,'residual',np.max(np.abs(H@z-lam*z)))
# survey: for each L, count bad potentials with scalar commutant (dim 1)
for L in range(3,13):
    cnt=0; badc=0
    for v in itertools.product([1,-1],repeat=L):
        if v[0]==-1: continue
        if bad(L,v):
            badc+=1
            if commutant_dim(L,v)==1: cnt+=1
    print('L',L,'bad (v0=+1)',badc,'bad with scalar commutant',cnt)
```

### Length-nine computation

Command: `python3 l9.py`;
exit code **0**. The full source follows, SHA-256 `01eaef37251d164606d239265f34969d961551a29c3acccbb53ba3f4d16558d5`.
Save it as `l9.py` and run `python3 l9.py` with NumPy 2.2.5.
It tests exactly the five couplings listed in the code, with the same
spectral and rank thresholds as the census.

```python
import numpy as np
L = 9
v = np.array([1, 1, -1, 1, 1, -1, 1, -1, -1])
A = np.zeros((L, L))
for i in range(L):
    A[i, (i + 1) % L] = A[(i + 1) % L, i] = 1
V = np.diag(v)
rows = [np.kron(np.eye(L), M.T) - np.kron(M, np.eye(L)) for M in (A, V)]
print("commutant dimension", L * L - np.linalg.matrix_rank(np.vstack(rows), tol=1e-9))
for t in (0.37, 1.913, -2.71, 5.3, 0.731):
    w, U = np.linalg.eigh(2 * np.eye(L) - A + t * V)
    print("t", t, "minimum eigenvalue gap", np.min(np.diff(w)),
          "minimum eigenvector coordinate", np.min(np.abs(U)),
          "simple", np.min(np.diff(w)) > 1e-8,
          "nonvanishing", np.min(np.abs(U)) > 1e-8)
print("numpy", np.__version__)
```

## ASSUMED-UNVERIFIED

The numerical census uses floating-point eigenvectors and SVD ranks; it
neither certifies exact rank nor quantifies over all real couplings. The
length-nine and length-twelve extensions and the absence of smaller
counterexamples have no Lean proof here. The preregistration's literature
search has the citation-index limits stated in Gap; no exhaustive search,
priority or model-family diversity is claimed.
