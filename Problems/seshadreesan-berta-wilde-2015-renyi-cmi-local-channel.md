---
slug: seshadreesan-berta-wilde-2015-renyi-cmi-local-channel
bibkey: seshadreesan2015renyi
doi: 10.1088/1751-8113/48/39/395303
url: https://arxiv.org/abs/1410.1443v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/RenyiCMILocalChannelRefutation.result
---

# Local-channel monotonicity of Rényi conditional quantum mutual information

## Problem

K. P. Seshadreesan, M. Berta, M. M. Wilde, *Rényi squashed entanglement, discord,
and relative entropy differences*, §3, Conjecture 1:

> Conjecture 1 The Rényi conditional quantum mutual information obeys monotonicity with respect to CPTP maps on system A, i.e., for ρABE ∈ S(HABE) and α ∈ (0, 1) ∪ (1, 2], Iα(A; B|E)ρ ≥ Iα(A′; B|E)τ, where τA′BE ≡ MA→A′(ρABE) and MA→A′ is a CPTP map acting on system A alone.

Equation (3.18) and the source's hypothesis statements appear in
[the literature note](../Library/QuantumChannels/seshadreesan2015renyi.md).
Issue [#16068](https://github.com/the-omega-institute/trureturing/issues/16068)
preregisters the witness.

## Motivation

The paper uses local-channel monotonicity to obtain LOCC monotonicity for its
Rényi squashed entanglement. Conditional correlation measures must distinguish
monotonicity on the two unconditioned systems when their defining formula is asymmetric.

## Gap

Equation (3.18) has established monotonicity on $B$. The conjecture requires
monotonicity on $A$ for the same expression and parameter range.

## Route

Write $M(p,q,s;u,v)$ for the real Hermitian matrix on $AE$ with rows
$[p,0,0,q]$, $[0,u,0,0]$, $[0,0,v,0]$, $[q,0,0,s]$ in the order $00,01,10,11$.
The state has classical $B$ and blocks
$X_0=M(13,8,7;13,39)/144$, $X_1=M(7,8,13;39,13)/144$.
Both blocks are positive definite: the coupled corner has positive trace and
positive determinant $27/144^2$, and the other entries are positive.
The trace is one. Dephasing $A$ uses $K_0=\operatorname{diag}(1,0)$ and
$K_1=\operatorname{diag}(0,1)$.

The input marginal is $S=M(5,4,5;13,13)/36=H^2$,
$H=M(2,1,2;\sqrt{13},\sqrt{13})/6$ and
$H^{-1}=M(4,-2,4;6/\sqrt{13},6/\sqrt{13})$.
The $E$ marginal is $1/2$ times the identity. At $\alpha=2$, the matrix under
the final square root is $\operatorname{diag}(9,1,1,9)/64$, with square-root
trace one. After dephasing it is $\operatorname{diag}(377,57,57,377)/2880$.
The square-root trace exceeds one; equivalently the output is
$\log((217+\sqrt{21489})/360)>0$, while the input is zero.

## Falsifier

A failure of positivity, normalization, Kraus completeness, the partial traces,
or either CFC power identity would invalidate this witness. A different
Rényi CMI definition requires a separate settlement.

## Evidence

The Lean module defines equation (3.18), its finite-dimensional claim and the
explicit witness, and proves `result : ¬ claim`. It verifies positive semidefiniteness,
trace one, Kraus completeness, the channel output, the marginals and the CFC power
identities. The input value is zero and the output value is strictly positive.
The latter proof bounds the square-root trace
$2\sqrt{377/2880}+2\sqrt{57/2880}>1$; elementary square-root and logarithm
identities give the equivalent expression $\log((217+\sqrt{21489})/360)$.
The axiom closure is exactly `propext`, `Classical.choice` and `Quot.sound`;
there is no `sorry` or `native_decide`.

## Triage

Tier 1: a named conjecture, preregistered in #16068. Admission basis:
`open-problem-resolution`; resolution: `Refuted`; `result` has
`proof_shape: bind-only` under normalization, with external open-problem admission.

### What the refutation shows

- **Proved (Lean):** the three-qubit state with classical $B$ refutes Conjecture 1
  under complete dephasing of $A$ at $\alpha=2$,
  $0\to\log((217+\sqrt{21489})/360)>0$. The explicit block factorizations
  also show that the state is faithful; strict positivity of the input state and
  the closed-form logarithm equality are algebraic consequences, while Lean
  certifies the positive semidefinite state and the strict increase.
- **Reasoning:** for positive definite $S_{AE}$ and a POVM $\{E_b\}$ on $E$,
  blocks $X_b=\sqrt S E_b\sqrt S$ give $I_2=0$. Here
  $E_0=\operatorname{diag}(3/4,1/4)$ and
  $E_1=\operatorname{diag}(1/4,3/4)$. An $A$-channel does not preserve this
  square-root factorization. The input has positive von Neumann CMI and is
  not a quantum Markov chain; the failure is specific to the Rényi formula.
- **Computed:** a rank-four variant with projective $E_b$ gives
  $0\to\log(10/9)$; numerical violations also occur at $\alpha=1.5$.
- **Reasoning:** the optimised sandwiched quantity of arXiv:1403.6102,
  Definition 19 and Remark 25, fails at $\alpha=1/2$ for this state,
  $0\to\log(648/(388+13(\sqrt{195}+\sqrt{35})))$.
  This quantity is not proved here.
- **Consequences (reasoning):** results that assume Conjecture 1, including
  LOCC monotonicity of this Rényi squashed entanglement and Consequences 3–4,
  lose that hypothesis. The $B$-side monotonicity proved in arXiv:1403.6102
  is unaffected.
- **Open:** whether a modified Rényi CMI, such as the log-Euclidean quantities
  of Rubboli–Arqand–Wilde, arXiv:2609.34699, is the right replacement lies
  outside this settlement.

## ASSUMED-UNVERIFIED

Worldwide novelty and priority are not conclusions of the formal refutation.
The numerical variants and the optimised sandwiched quantity are distinct
from the theorem's CFC expression and remain outside its proof scope.
