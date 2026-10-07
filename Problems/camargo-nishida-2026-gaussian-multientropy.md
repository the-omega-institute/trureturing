---
slug: camargo-nishida-2026-gaussian-multientropy
bibkey: camargo2026gaussianmultientropy
doi: 10.48550/arXiv.2609.30754
url: https://arxiv.org/abs/2609.30754v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/GaussianMultiEntropyAsymptotic.result
---

# The large-squeezing law of the genuine multi-entropy of fully symmetric Gaussian states

## Problem

H. A. Camargo and M. Nishida, *Genuine Multi-Entropy of Fully Symmetric Gaussian States*,
arXiv:2609.30754v1, compute the tripartite genuine Rényi multi-entropy
$\mathrm{GM}^{(3)}_n(A:B:C)$ of the fully symmetric pure Gaussian state of $N$ bosonic modes
(diagonal $a\ge1$, off-diagonal $e^-$ of their Eq. (3.1)) for $N\le8$ and $n\le4$, observe
$\mathrm{GM}^{(3)}_n\sim\frac{2-n}{2n}\log a$ as $a\to\infty$ (Eq. (3.8)), and write "we
\emph{conjecture} that the asymptotic behavior \eqref{AsymB} is valid for the fully symmetric
Gaussian states with any $n$ and $N$." The verbatim definitions are in
[the literature note](../Library/QuantumStates/camargo2026gaussianmultientropy.md).

Issue [#13990](https://github.com/the-omega-institute/trureturing/issues/13990) reads the
conjecture for every replica order $n\ge2$ and every tripartition with positive party sizes
$N_A,N_B,N_C$, with the replica partition functions as the literal Lebesgue integrals of products
of the real Gaussian density kernels under the twists $g_A,g_B,g_C$, and asymptotic equivalence in
the sense of `Asymptotics.IsEquivalent` (for $n=2$ both sides are the zero function).

## Motivation

At infinite squeezing the fully symmetric states approach the continuous-variable GHZ state, whose
genuine multi-entropy has the same leading term; the conjecture asserts that the finite-$N$
computations of the paper extend to every number of modes and every replica order.

## Gap

Issue #13990 records the literature check before any Lean: one arXiv version; arXiv abstract
searches for multi-entropy with Gaussian states and for genuine multi-entropy found no proof of
Eq. (3.8); Zenodo had no record; the repository had no result on Gaussian multi-entropy.
`not-found-in-searched-scope`.

## Route

1. The replica integral of the Gaussian kernels is a Gaussian integral
   $\int e^{-x^\top Mx}=\pi^{d/2}(\det M)^{-1/2}$ (transplanted into `GaussianReplicaReduction`), and
   with $\mathbf W=\alpha[I-(1-\varepsilon)P]$, $P$ the projection onto constant mode vectors, it
   equals $(\varepsilon^m/\det H_\varepsilon)^{1/2}$ with $H_\varepsilon=I-(1-\varepsilon)(P_0+P_1)/2$.
2. Writing $P_0=V_0V_0^\top$, $P_1=V_1V_1^\top$ with orthonormal columns, Sylvester's identity and
   the Schur complement reduce $\det H_\varepsilon$ to the replica-level determinant
   $\det\big(\tfrac{(1+\varepsilon)^2}{4}I-\tfrac{(1-\varepsilon)^2}{4}Q^\top Q\big)$, where
   $Q=\sum_k(N_k/N)\,\mathrm{Perm}(g_k)$.
3. $Q^\top Q$ is symmetric and row stochastic. If one twist is the identity and the twists act
   transitively, a vector fixed by a stochastic matrix with positive twist entries is constant
   (a maximal coordinate propagates along twist paths), so the eigenvalue $1$ is simple and
   $\det=\varepsilon D(\varepsilon)$ with $D$ continuous and $D(0)>0$.
4. $a^2\varepsilon(a)\to(N-1)/N^2$, hence $\log\varepsilon\sim-2\log a$, and the four replica
   determinants give $\mathrm{GM}^{(3)}_n=\frac{n-2}{4n}\log\varepsilon+O(1)$ for $n\ge3$.
5. For $n=2$, the squared non-trivial eigenvalues of the tripartite and the three bipartite replica
   matrices coincide, which gives $\det H_{AB:C}\det H_{BC:A}\det H_{CA:B}=\varepsilon^2\det H_3$
   and $\mathrm{GM}^{(3)}_2=0$ for all $a\ge1$.

## Falsifier

The settlement concerns the fully symmetric states of the paper and the asymptotic regime
$a\to\infty$; other Gaussian families, finite-$a$ values and other replica conventions are outside
the claim.

## Evidence

The canonical sources are `D5/S3/Quantum/Entanglement/GaussianMultiEntropyAsymptotic.lean`
(the definitions of the replica integrals `Z`, `Z3`, `Z2`, the entropies `S3`, `S2`, `GM3`,
`claim`, `result`, and the bridges from the integrals to the replica determinants) and its helper
module `D5/S3/Quantum/Entanglement/GaussianReplicaReduction.lean` (the transplanted Gaussian
integral, see [its source note](../Library/Analytic/brcic2026gaussianquadratic.md), the
block-determinant reduction, the kernel of stochastic twist averages, the determinant
factorization and the asymptotic lemmas; Mathlib only). The axiom closure of
`result` is exactly `propext`, `Classical.choice` and `Quot.sound`; there is no `sorry`,
`native_decide`, or new axiom.
The settlement module statement is `sha256:1e9e370f3b4f550a2b6d8038fd7afaf11ea9965043eb15f5187d2d08c77a487e`,
the `result` statement `sha256:a34bff0157a712c7a0e0a93aa692ecfe0e0e123ae890c7a188268cd72c0abe89` and the
`claim` statement `sha256:5a42c12a9865413553ec0317926bcfb6cbcacbbe473f27e7135ab7270beccff2`; its Freeze event is
`sha256:2021168bd5dce175bf113ddcdb3306504b22694ad0d2e77e857e38bc205fc6dd`, with the helper module as
project-level prerequisite. The helper `GaussianReplicaReduction` has module statement
`sha256:767695a861b18eb09b63f64a115f6056e9fba1a35e6d43cbe03f4b5aed88419c` and Freeze event
`sha256:842cb437647dc94fe8b162ab98569ad2838eea347014873987534dc6f047964e`, with no project-level
prerequisite.

## Triage

Tier 1 conjecture of a September 2026 paper, preregistered in issue #13990 before any Lean and
run as a research line. `theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | content | the kernel of stochastic twist averages (`stochastic_twist_kernel`, `permutation_average_kernel`) on its proof path | open-problem-resolution |

The other public declarations of the two modules carry free parameters and lie on the proof
path of `result`. Utility is `none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every $n\ge2$ and all positive $N_A,N_B,N_C$,
$\mathrm{GM}^{(3)}_n\sim\frac{2-n}{2n}\log a$ as $a\to\infty$; for $n=2$ the multi-entropy is
eventually zero.

**Proved on the way, for general data:**

- *Replica determinant.* For any finite replica type and any twists, the replica integral of the
  fully symmetric state is $(\varepsilon^m/\det H_\varepsilon)^{1/2}$, and $\det H_\varepsilon$
  equals the replica-level determinant
  $\det\big(\tfrac{(1+\varepsilon)^2}{4}I-\tfrac{(1-\varepsilon)^2}{4}Q^\top Q\big)$.
- *Simple eigenvalue.* For twists that contain the identity and act transitively, the only vectors
  fixed by $Q^\top Q$ are the constants, and the determinant is $\varepsilon D(\varepsilon)$ with
  $D$ continuous and $D(0)>0$.
- *Exact $n=2$ identity.* For every tripartition,
  $\det H_{AB:C}\det H_{BC:A}\det H_{CA:B}=\varepsilon^2\det H_3$ at $n=2$, which is the
  fully symmetric case of the paper's §4 theorem $\mathrm{GM}^{(3)}_2=0$.

**Argued, not formalized.**

- *Mechanism.* The coefficient of $\log\varepsilon$ is fixed by the replica counts alone
  ($n^2-1$ for the tripartite term, $n-1$ for each bipartite term), because the eigenvalue $1$ is
  simple in every term; the remaining spectrum contributes only the constant
  $\frac{\log D_3(0)}{2n(n-1)}-\sum_R\frac{\log D_R(0)}{4(n-1)}$.
- *The subleading constant.* $\mathrm{GM}^{(3)}_n-\frac{2-n}{2n}\log a$ converges to
  $\frac{n-2}{4n}\log\frac{N-1}{N^2}+\frac{\log D_3(0)}{2n(n-1)}-\sum_R\frac{\log D_R(0)}{4(n-1)}$;
  numerically the limits lie between $0.044$ and $0.239$ for the configurations of #13990.

**Open.** A closed form of $D_R(0)$ in terms of $n$ and the party fractions, and the corresponding
statement for the $\mathtt q\ge4$ multi-entropy, are not settled here.

**Effect on the paper.** Eq. (3.8) holds for every $n$ and every tripartition with positive
party sizes.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty, priority, or the
absence of an independent proof.
