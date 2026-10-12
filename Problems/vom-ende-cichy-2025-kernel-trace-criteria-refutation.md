---
slug: vom-ende-cichy-2025-kernel-trace-criteria-refutation
bibkey: vomende2025witnessoptimality
doi: null
url: https://arxiv.org/abs/2505.15615v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation.result
---

# The kernel criterion for witness optimality does not imply the trace criterion

## Problem

F. vom Ende and S. Cichy, *Simple Sufficient Criteria for Optimality of Entanglement Witnesses*,
arXiv:2505.15615v2, Section IV (p. 12):

> Next: is our trace-based criterion (Coro. 2) actually equivalent to our kernel criterion (Thm. 2)?
> This is the question mark in Fig. 2, and while the kernel criterion seems stronger we were not able
> to find a witness for which only the kernel criterion holds.

The kernel criterion asks for a vector of Schmidt rank $\min\{m,n\}$ in the kernel of
$W+{\rm tr}_2(W)\otimes{\bf1}$ (if $m\le n$) or of $W+{\bf1}\otimes{\rm tr}_1(W)$ (if $m\ge n$); the
trace criterion asks for a maximally entangled $\Omega$ with
$\langle\Omega|W|\Omega\rangle=-{\rm tr}(W)/\min\{m,n\}$. The verbatim texts are in
[the literature note](../Library/QuantumChannels/vomende2025witnessoptimality.md).
Issue [#14763](https://github.com/the-omega-institute/trureturing/issues/14763) preregisters the
reading and the refutation.

## Motivation

Optimal entanglement witnesses are the extreme detectors of entanglement; the source derives two
cheap sufficient conditions for optimality from the spanning property, one a kernel condition and
one an expectation-value condition that numerics can test by a minimization over one local unitary
group. The source proves that the trace criterion implies the kernel criterion and asks whether the
two have the same reach.

## Gap

The source reports no witness that satisfies only the kernel criterion. Its citing works
arXiv:2510.06863 and arXiv:2604.02420 do not address the question; the literature check in #14763
found no answer; `not-found-in-searched-scope`.

## Route

In the basis $(00,01,10,11)$ of $\mathbb C^2\otimes\mathbb C^2$ take

$$W=\begin{pmatrix}0&0&0&-2\\0&1&0&0\\0&0&4&0\\-2&0&0&0\end{pmatrix}
=(X\otimes{\bf1})W_{\rm red}(X^\dagger\otimes{\bf1}),\qquad X=\operatorname{diag}(1,2),$$

the reduction witness $W_{\rm red}={\bf1}-|\Gamma\rangle\langle\Gamma|$ filtered on the first factor.

1. $\langle x\otimes y|W|x\otimes y\rangle=|\bar x_0y_1-2\bar x_1y_0|^2\ge0$, and
   ${\rm tr}(W|\Omega_0\rangle\langle\Omega_0|)=-2<0$ for $\Omega_0=(|00\rangle+|11\rangle)/\sqrt2$: $W$ is a witness.
2. ${\rm tr}_2(W)=\operatorname{diag}(1,4)$ and
   $z^*(W+{\rm tr}_2(W)\otimes{\bf1})z=|z_{00}-2z_{11}|^2+2|z_{01}|^2+8|z_{10}|^2$, so $(2,0,0,1)$, of
   Schmidt rank $2$, lies in the kernel: the kernel criterion holds.
3. $z^*(W+2\cdot{\bf1})z=2|z_{00}-z_{11}|^2+3|z_{01}|^2+6|z_{10}|^2\ge0$, so every unit vector has
   $\langle\Omega|W|\Omega\rangle\ge-2>-5/2=-{\rm tr}(W)/2$: the trace criterion fails.

## Falsifier

An error in the two sums of squares or in the kernel, or a reading of block positivity, Schmidt rank
or maximal entanglement different from the source. Positive controls in #14763: the reduction
witness and the two-qubit flip satisfy both criteria.

## Evidence

`D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation.lean` defines `blockPositive`
(the product-vector expectation is nonnegative in the complex order), `IsWitness`, the partial
traces `trTwo`, `trOne` (the frozen `partialTraceRight`, `partialTraceLeft`), `schmidtRank` (the rank of
the coefficient matrix), `kernelCriterion`, `maximallyEntangled` (an equal-coefficient Schmidt sum over
orthonormal families of size $\min\{m,n\}$), `traceCriterion` and `claim`, and proves
`result : ¬ claim`. `IsWitness` states ${\rm tr}(W\sigma)<0$ in the complex order, literally as in the source. The axiom closure of `result` is exactly `propext`,
`Classical.choice` and `Quot.sound`; there is no `sorry` or `native_decide`.
The module statement is `sha256:21e7e69d5fb3b0823b89be6d5b2e6e9581a42a77d933e7864a0833cbe22fe2e1`; `result` is
`sha256:01e9450248d36bfbcb9028325842962e0e2af3d48208a203adf28173fee94911` and `claim` is
`sha256:7240a2d88de7184ca142279ac4a6119a08de03475d76f0286cb91c55acb53644`. The Freeze event is
`sha256:119b1c06df26ac2ebd73265a208ed6218be64e15bcfe75d96728a13c743b33fd`.

## Triage

Tier 1: an explicit question of a 2025 paper, preregistered in #14763 before any Lean.
`theorem`; resolution `refuted`. `result` and its private lemmas are bind-only (the explicit matrix, its sums of squares and a
$2\times2$ determinant, by normalization); admission basis `open-problem-resolution`. Utility
`kind=certified-instance; basis=refutes`. There is no digestion atom.

### What the refutation shows

- **Proved by `result`:** the kernel criterion of Theorem 2 does not imply the trace criterion of
  Corollary 2, already for two qubits; the implication in the source's Fig. 2 is strict.
- **Mechanism (derived, not formalized):** the kernel criterion is invariant under local invertible
  filtering. For branch (i) ($m\le n$), $W\mapsto(Y\otimes{\bf1})W(Y^\dagger\otimes{\bf1})$ transforms
  $W+{\rm tr}_2(W)\otimes{\bf1}$ by the same congruence and its kernel by $(Y^\dagger)^{-1}\otimes{\bf1}$, which
  preserves Schmidt rank; for branch (ii) ($m\ge n$) the same holds with filters ${\bf1}\otimes Y$ on the second
  factor and $W+{\bf1}\otimes{\rm tr}_1(W)$. The trace criterion is not: it needs a
  kernel vector with equal Schmidt coefficients. The family
  $W_t=(\operatorname{diag}(1,t)\otimes{\bf1})W_{\rm red}(\operatorname{diag}(1,t)\otimes{\bf1})$, $t>0$, has
  trace $1+t^2$ and least eigenvalue $-t$, so the trace criterion holds exactly at $t=1$; the gap is
  $(t-1)^2/2$ (computed, not formalized).
- **Derived, not formalized:** up to filtering the two criteria agree. If $m\le n$ and
  $v\in\ker(W+{\rm tr}_2(W)\otimes{\bf1})$ has coefficient matrix $M$ of rank $m$, then
  $Y^\dagger=(m\,MM^\dagger)^{1/2}$ makes $(Y^{-\dagger}\otimes{\bf1})v$ maximally entangled, so
  $W'=(Y\otimes{\bf1})W(Y^\dagger\otimes{\bf1})$ satisfies the trace criterion; conversely the trace
  criterion implies the kernel criterion (source). So a witness satisfies the kernel criterion if and
  only if some local filtering of it satisfies the trace criterion (the case $m\ge n$ with filters on
  the second factor is symmetric).
- **Open:** the source's other two Section IV questions (an explicit entanglement-breaking channel of
  full Choi rank detecting the optimality of the flip in odd dimensions; multipartite versions).

## ASSUMED-UNVERIFIED

The literature check in #14763 is bounded and does not establish worldwide novelty or priority; the
journal status of the source was checked only through Crossref.
