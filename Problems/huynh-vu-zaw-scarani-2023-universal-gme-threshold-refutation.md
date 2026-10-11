---
slug: huynh-vu-zaw-scarani-2023-universal-gme-threshold-refutation
bibkey: huynhvu2024universal
doi: 10.1103/PhysRevA.109.042402
url: https://arxiv.org/abs/2311.00806v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/PrecessionUniversalThresholdRefutation.result
---

# Singlet padding refutes the universal precession GME threshold

## Problem

Khoi-Nguyen Huynh-Vu, Lin Htoo Zaw and Valerio Scarani,
*Certification of genuine multipartite entanglement in spin ensembles with
measurements of total angular momentum*, Phys. Rev. A 109, 042402,
arXiv:2311.00806v2, Conjecture 3, PDF p. 9:

> Consider a spin ensemble. Perform the precession protocol with odd $K \geq 3$ on the total angular momentum of the system. If the score $P_K > \mathbf{P}_K^{\mathrm{conj}}$ is obtained, then the spin ensemble is GME.

Here $J_k=\cos(2\pi k/K)J_x+\sin(2\pi k/K)J_y$ is the sum of the
particle observables, $Q_K=K^{-1}\sum_k\operatorname{pos}(J_k)$ and
$P_K=\operatorname{tr}(\rho Q_K)$. The spectral weight is
$(1+\operatorname{sgn}m)/2$, including one half at zero.
Separability across a cut means a normalized finite convex mixture of
products of density matrices. GME excludes convex mixtures over all
nontrivial cuts. Preregistration: [#13586](https://github.com/the-omega-institute/trureturing/issues/13586).

## Motivation

`D5/S3/Quantum/Entanglement/PrecessionUniversalThresholdRefutation.result`
proves the negation of the literal universal claim. Its state has constituent
spins $\{1/2,1/2,3/2\}$: a normalized singlet projector on the pair tensored
with the normalized projector onto the difference of the spin-$3/2$
endpoint basis vectors. It is a product across the pair–rest cut, yet scores
$3/4>23/32$, with exact gap $1/32$.
The source anchor is `Library/QuantumStates/huynhvu2024universal.md`.

## Gap

The paper proposes a composition-independent GME threshold. The
preregistration classifies the question as Tier 1 and records literature
checks of arXiv:2411.03132v3, 2509.03166v4 and 2608.21217v2, with
2405.17966 and 2401.16147 also inspected, and no correction found in
that searched scope. The APS full text was inaccessible in those checks;
this dossier uses the verified arXiv v2 source and makes no priority claim.

The reduction to effective spins on each side of a cut must retain the
spin-zero representation. A singlet-capable side has effective spin zero,
although every constituent particle has strictly positive spin.

## Route

For the singlet $s$, the pair's total $J_x$ and $J_y$ annihilate $s$.
Consequently the embedding $V\varphi=s\otimes\varphi$ intertwines the
padded total observable and the rest observable. Finite Hermitian spectral
calculus respects this intertwining. Thus, for every finite Hermitian rest
family $B_k$ and every matrix $\sigma$,

$$
\operatorname{tr}\left[(|s\rangle\langle s|\otimes\sigma)
 \frac1K\sum_k\operatorname{pos}(P_k\otimes I+I\otimes B_k)\right]
 =\operatorname{tr}\left[\sigma\frac1K\sum_k\operatorname{pos}(B_k)\right]
$$

whenever $P_ks=0$ and the padded observables are Hermitian.
The private `singlet_padding_ensemble_score` identifies this family with
the literal `ensembleJ` and `ensembleQ` of every spin list with two
spin-1/2 particles prepended. It proves score equality for every matrix
$\sigma$ and every $K$, hence for every state and every odd $K\ge3$
in the source protocol. Its coordinate equivalence only splits a padded
configuration into the pair and the remaining configuration. The witness
score uses this bridge on `padded_precession_score` → `result`'s live path. No continuity of the
sign function is assumed: the Hermitian matrices have finite spectra.
`pair_rest_product` supplies density normalization and the non-GME cut.

## Falsifier

The witness obeys the source's positive constituent-spin, odd-$K$,
normalization and nontrivial-cut requirements. The score is the source's
spectral protocol, rather than a substitute certificate. The universal
claim would require this witness to be GME, contradicting its explicit
one-term pair–rest decomposition.

## Evidence

The settling declaration is `result : ¬ claim`. Its only public companions
are the definitions needed to state that claim. All private helpers are
consumed in the refutation. The settling result and helpers have
`proof_shape: bind-only`; the module's admission basis is
`open-problem-resolution (#13586; Refuted)`.

Registration is paused under CLAUDE.md §3.9.

### Reproducible finite computation

The following command directly diagonalizes every full tensor-product
observable for $K=3,5,7$, both for the GHZ state and for its singlet-padded
state. Command exit code: 0. Script SHA-256: `e038954f9d1e979d393cc05e57f990ad0def5144e30135655786c449751ec14c` (the bytes
between the heredoc delimiter lines, including the final newline).

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 - <<'PY'
import json, math
import numpy as np

def total_xy(N):
    d = 2**N
    X = np.zeros((d, d), complex)
    Y = np.zeros((d, d), complex)
    for col in range(d):
        for n in range(N):
            bit = 1 << n
            row = col ^ bit
            X[row, col] += 0.5
            Y[row, col] += 0.5j if row & bit else -0.5j
    return X, Y

def score(K, X, Y, state):
    answer = 0.0
    for k in range(K):
        angle = 2*math.pi*k/K
        values, vectors = np.linalg.eigh(math.cos(angle)*X + math.sin(angle)*Y)
        weights = np.where(values > 1e-9, 1.0, np.where(values < -1e-9, 0.0, 0.5))
        answer += float(np.sum(weights*np.abs(vectors.conj().T @ state)**2))/K
    return answer

rows = []
singlet = np.array([0, 1, -1, 0], complex)/math.sqrt(2)
PX, PY = total_xy(2)
for K in (3, 5, 7):
    X, Y = total_xy(K)
    ghz = np.zeros(2**K, complex)
    ghz[0], ghz[-1] = 1/math.sqrt(2), (-1)**((K-1)//2)/math.sqrt(2)
    padded = np.kron(singlet, ghz)
    TX = np.kron(PX, np.eye(2**K)) + np.kron(np.eye(4), X)
    TY = np.kron(PY, np.eye(2**K)) + np.kron(np.eye(4), Y)
    c = math.comb(K-1, (K-1)//2)/2**(K-1)
    threshold = 23/32 if K == 3 else (69+math.sqrt(181))/128 if K == 5 else (1+c*(K-1)/(K+1))/2
    a, b = score(K, X, Y, ghz), score(K, TX, TY, padded)
    assert abs(a-(1+c)/2) < 1e-10 and abs(a-b) < 1e-10
    assert b > threshold+1e-11 and (K+2)/2 <= 15
    rows.append(dict(K=K, dimension=2**(K+2), ghz_score=a, padded_score=b, threshold=threshold, gap=b-threshold, total_spin=(K+2)/2))
print(json.dumps(rows, indent=2))
PY
```

| $K$ | Padded dimension | GHZ score | Padded score | Threshold | Gap | $\sum j_n$ |
| --- | --- | --- | --- | --- | --- | --- |
| 3 | 32 | 0.7499999999999994 | 0.7499999999999997 | 0.71875 | 0.031249999999999667 | 2.5 |
| 5 | 128 | 0.6874999999999999 | 0.6874999999999998 | 0.6441689378677633 | 0.043331062132236475 | 3.5 |
| 7 | 512 | 0.6562499999999999 | 0.6562499999999999 | 0.6171875 | 0.03906249999999989 | 4.5 |

Eigenvalues within $10^{-9}$ of zero receive half weight. Formula and
padding agreement are checked to $10^{-10}$. These floating-point
computations support only these three values; they are not kernel proofs
of Result 4's negation or of the uniform family.

## Triage

### What the settlement shows

- **Proved in this module — $K=3$ refutation.** The $\{1/2,1/2,3/2\}$
  ensemble has a density matrix separable across a nontrivial cut, exact
  score $3/4$ and threshold $23/32$. `result` refutes Conjecture 3.
- **Proved on paper; computed for $K=3,5,7$ — the GHZ family for every odd
  $K\ge3$.** Let $L=(K-1)/2$, $c_K=2^{-(K-1)}\binom{K-1}{L}$ and
  $g_K=(|\uparrow^K\rangle+(-1)^L|\downarrow^K\rangle)/\sqrt2$.
  In the two-endpoint subspace, the diagonal entries of the positive
  spectral weight are $1/2$. Its off-diagonal entry is
  $2^{-K}\sum_{r=0}^{L}(-1)^r\binom Kr=(-1)^Lc_K/2$,
  using $\sum_{r=0}^{L}(-1)^r\binom Kr=(-1)^L\binom{K-1}{L}$.
  Precession multiplies this entry by $e^{iK(2\pi k/K)}=1$.
  Hence $P_K(g_K)=(1+c_K)/2$. Singlet padding preserves the score and
  produces a non-GME state. For $K=3$ the gap is $1/32$; for $K=5$ it
  is $(19-\sqrt{181})/128>0$; for $K\ge7$ it is $c_K/(K+1)>0$.
  The inline computation above verifies $K=3,5,7$, exit 0, SHA-256
  `e038954f9d1e979d393cc05e57f990ad0def5144e30135655786c449751ec14c`. The all-odd family is not a separately kernel-checked
  theorem in this module; its Lean extension remains **open**.
- **Proved in Lean — the arbitrary-ensemble score-preserving mechanism
  for equality of the unrestricted threshold and quantum supremum.**
  `singlet_padding_ensemble_score` preserves the literal score of every
  remaining ensemble and every state, and
  `pair_singlet_annihilation` covers every linear combination of the
  pair's two angular-momentum components. Define $S_K^{\rm q}$ as the
  scores over all nonempty finite positive-spin ensembles and all their states,
  and $S_K^{\rm bisep}$ with states restricted to non-GME ones.
  Padding realizes every member of $S_K^{\rm q}$ in
  $S_K^{\rm bisep}$; the reverse inclusion follows from the definitions.
  Therefore $S_K^{\rm q}=S_K^{\rm bisep}$ and their suprema agree.
  This argument allows the ensemble to change and does not assert a
  fixed-ensemble equality. The arbitrary-ensemble operator identification and score equality are
  kernel checked on `result`'s live path. The score-set argument above
  gives the equal-supremum consequence; no separate Lean declaration
  of the score sets or their suprema is exported.
- **Computed — Result 4 is contradicted within its stated range.**
  Result 4 requires odd $3\le K\le21$, $\sum j_n\le15$, and
  $P_K>\mathbf P_K^{\rm conj}+10^{-11}$.
  The computed $K=3,5,7$ ensembles satisfy every range condition, with
  $K+2$ spin-$1/2$ particles and $\sum j_n=(K+2)/2$.
  The inline script asserts the strict comparison for all three rows,
  exit 0, SHA-256 `e038954f9d1e979d393cc05e57f990ad0def5144e30135655786c449751ec14c`. The state is a pair–rest product by
  construction. No extension to other numerical values is asserted.
- **Proved in the source or existing repository — what survives.**
  Result 1 assumes the fixed constituent-spin sum $\sum j_n=K/2$ and
  uses threshold $\frac12[1+2^{-K}\binom{K-1}{(K-1)/2}]$.
  A singlet-bearing side leaves the rest with maximum effective spin
  strictly below $K/2$, where the precession score is $1/2$; this padding
  family has sum $(K+2)/2$, outside Result 1's hypothesis. Result 1 is a
  source result, not newly proved here. The existing frozen
  `PrecessionSpinOneSeparableBound.result` (#11873) proves the
  $\{1,K/2\}$ product-pure separable bound for odd $K\ge7$.
  The counterexample uses an effective spin-zero side and contradicts
  neither that theorem nor its hypotheses. Any universal maximization
  deduced solely from the positive-effective-spin cases must be revised;
  the individual positive-spin bounds survive.
- **Open — corrected universal statement.** Exclude spin-zero sectors
  on both sides of every nontrivial bipartition, or restrict the allowed
  ensembles to cuts admitting no singlet subspace. These restrictions
  remove this padding counterexample. They do not prove that the printed
  threshold then certifies GME; that corrected implication remains open.
  Positive constituent spins alone do not supply the needed restriction.

## ASSUMED-UNVERIFIED

The journal full text is not independently verified; the statement and
ranges use arXiv:2311.00806v2. Numerical diagonalization is floating point,
with the tolerances and tested scope stated above. No model-family
independence or literature-priority claim is made.
