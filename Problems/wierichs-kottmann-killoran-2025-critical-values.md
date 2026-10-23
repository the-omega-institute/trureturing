---
slug: wierichs-kottmann-killoran-2025-critical-values
bibkey: wierichs2025brickwall
doi: 10.48550/arXiv.2511.16736
url: https://arxiv.org/abs/2511.16736v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/PauliRotationCriticalValues.result
---

# Critical values of parametrized quantum circuits

## Problem

D. Wierichs, K. Kottmann and N. Killoran, *Unitary synthesis with optimal brick wall circuits*,
arXiv:2511.16736v1, §V (page 9):

> Conjecture 3. The critical values F(C) of a PQC that has full rank almost everywhere in T^d form an at
> most (d−2)-dimensional subset of G.

A PQC (Appendix F, Definition 1) consists of Clifford gates and $d$ rotations from $\{R_X,R_Y,R_Z\}$, each
input feeding one rotation without preprocessing, viewed as $F:T^d\to G\subset\mathbb C^{2^n\times 2^n}$
with $d=\dim G$; $C$ is the set of inputs at which the Jacobian has rank below $d$. The verbatim texts are
in [the literature note](../Library/QuantumChannels/wierichs2025brickwall.md). Issue
[#15435](https://github.com/the-omega-institute/trureturing/issues/15435) preregisters the two-qubit,
$G=SU(4)$, $d=15$ specialization with Hausdorff dimension and the refutation.

## Motivation

The authors reduce universality of their optimal brick wall circuits to Conjecture 3: if the critical
values had codimension at least two they could not separate the image from full-dimensional regions of
$G$, and full Jacobian rank almost everywhere would imply surjectivity. With it, they "know [their] circuit
families to be universal for n≤5".

## Gap

The paper proves that a dense image is the whole group and that full rank at one point gives full rank
almost everywhere, and supports Conjecture 3 by numerical experiments and lower-dimensional examples. The
literature check in #15435 found no settlement; `not-found-in-searched-scope`.

## Route

Take the two-qubit Pauli words, in this order,
$P=(YY,IY,XX,ZY,ZX,IZ,XY,YZ,IX,XZ,ZI,YI,YX,XI,ZZ)$, the rotations
$R_P(a)=\cos\tfrac a2\,I-i\sin\tfrac a2\,P$ (each a Clifford conjugate of a single-qubit $R_Z$) and
$F(\alpha)=R_{P_1}(\alpha_1)\cdots R_{P_{15}}(\alpha_{15})$.

1. $\partial_jF=-\tfrac i2H_jF$ with $H_j$ the $j$-th prefix conjugate of $P_j$, so the rank of $DF(\alpha)$
   is the rank of the real $15\times15$ matrix $J(\alpha)$ of Pauli coefficients of the $H_j$.
2. $\det J$ is real-analytic and not identically zero, so $F$ has full rank almost everywhere.
3. At $\alpha^*$ with $\alpha^*_6=\alpha^*_7=\alpha^*_8=\alpha^*_{11}=\pi/4$ and all other inputs $0$,
   rational changes of coordinates reduce $J(\alpha^*)$ to a diagonal matrix with fourteen ones and one
   zero; along the kernel direction $v$ the normalized determinant $g$ has derivative $-1$.
4. The map $\alpha\mapsto(Q(F(\alpha)),g(\alpha))$, with $Q$ a fixed linear projection onto
   $\mathbb R^{14}$, has a surjective derivative at $\alpha^*$; its image therefore contains a neighborhood,
   and $Q(F(C))$ contains an open subset of $\mathbb R^{14}$. Hence $\dim_HF(C)\ge14>13$.

## Falsifier

A reading of the class, the dimension notion or the rotation convention narrower than the source's; or an
error in the certificate at $\alpha^*$. Control in #15435: for all 720 orders of the six two-qubit Pauli
words spanning $\mathfrak{so}(4)$, every fold point found numerically has critical-value rank $d-2=4$, the
bound the conjecture predicts.

## Evidence

`D5/S3/Quantum/Information/PauliRotationCriticalValues.lean` defines the class of circuits of fifteen
nonidentity two-qubit Pauli rotations, the rank of `fderiv`, the critical set and `claim` (full rank almost
everywhere implies `dimH (circuit P '' critical P) ≤ 13`, Hausdorff dimension in the Frobenius metric), and
proves `result : ¬ claim`. The axiom closure of `result` is exactly `propext`, `Classical.choice` and
`Quot.sound`; there is no `sorry` or `native_decide`. The step from a nonzero analytic determinant to full
rank almost everywhere is the zero-set theorem of [Mityagin](../Library/AnalyticClosure/mityagin2015zeroset.md),
proved in the module by induction on the dimension with Fubini.

## Triage

Tier 1: a named conjecture of a November 2025 preprint, preregistered in #15435 before any Lean.
`theorem`; resolution `refuted`. `result` is bind-only in the repository's sense (instantiation of pinned
Mathlib calculus, rank, analyticity and Hausdorff-dimension facts with an exact finite certificate);
admission basis `open-problem-resolution`; utility `kind=certified-instance; basis=refutes`. There is no
digestion atom.

### What the refutation shows

- **Proved by `result`:** a two-qubit circuit of fifteen Pauli rotations with full rank almost everywhere
  whose critical values have Hausdorff dimension at least $14=d-1$ in $SU(4)$.
- **Mechanism:** the critical point is a fold. $J(\alpha^*)$ has corank one, and the second derivative
  contracted with its kernel and cokernel vectors is nonzero. The critical set is then a hypersurface
  transverse to the kernel of $DF$, and $F$ maps it onto a codimension-one wall in $G$. This is the
  generic singularity of a map between manifolds of equal dimension. In Euler-angle circuits on $SU(2)$
  the critical points are gimbal locks, where two rotations merge and the image loses two dimensions; in
  the $\mathfrak{so}(4)$ control the derivative restricted to the critical set has rank $d-2$ at every fold
  point found (computed, mechanism not analysed).
- **Consequence for the source:** the reduction "full rank almost everywhere and Conjecture 3 imply
  universality" no longer applies. Universality of the authors' brick wall circuits for $n\le5$ is not
  decided by this result and remains open.
- **Reported, not verified here (#15435):** tensoring the witness with the identity and appending every
  other Pauli word gives a $(d-1)$-dimensional critical-value patch for every $n\ge2$.
- **Open:** whether codimension-one critical walls actually separate the image of a circuit from part of
  $G$, i.e. whether full rank almost everywhere still implies surjectivity by another route.

## ASSUMED-UNVERIFIED

The literature check in #15435 is bounded and does not establish worldwide novelty or priority.
