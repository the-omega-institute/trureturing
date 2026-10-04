---
bibkey: kaplanski2026williamson
authors: PK
year: 2026
title: The Williamson normal form in QIQT-H
doi: null
url: https://github.com/kaplan196883/QIQT-H/blob/0313e288c7ab3d3868c73ccdc6a68242efc0214a/lean/mathlib/QIQTH/WilliamsonNormalForm.lean
claim: Every finite positive-definite real matrix on paired modes has a symplectic positive repeated diagonal congruence, including the empty mode set.
strata_touched:
  - D5/S3/QuadraticForms/PositiveDefiniteWilliamson
license: Apache-2.0
triage: anchor
---

# Finite-mode skew pairing and positive Williamson form

## Verified locator

https://github.com/kaplan196883/QIQT-H/blob/0313e288c7ab3d3868c73ccdc6a68242efc0214a/lean/mathlib/QIQTH/WilliamsonNormalForm.lean

## Theorem 1. Oriented skew paired basis

Let E be a finite-dimensional real inner product space of even dimension and let a be a real linear operator satisfying
$\langle ax,y\rangle=-\langle x,ay\rangle$ for all x,y.
There are a finite index set K, an orthonormal basis $(p_k,q_k)_{k\in K}$ of E, and nonnegative real numbers $\nu_k$ such that
$a p_k=-\nu_k q_k$ and $a q_k=\nu_k p_k$ for every k.
The statement includes dimension zero and the zero operator.

For nonzero a, a negative Rayleigh eigenvalue of $a^2$ gives an invariant oriented orthonormal plane. Its orthogonal complement is invariant because a is skew adjoint. Strong induction on dimension and orthonormal gluing produce the full frame. For zero a in positive even dimension, any orthonormal pair starts the same induction.

## Theorem 2. Positive Williamson congruence

For any finite set L, let M be a positive-definite real matrix indexed by $L\sqcup L$ and put
$J=\begin{pmatrix}0&-I\\ I&0\end{pmatrix}$.
There exist one real matrix S and strictly positive frequencies $\nu_i$, i in L, such that
$SJS^T=J$, $S^TJS=J$, and
$S^TMS=\begin{pmatrix}\operatorname{diag}(\nu)&0\\0&\operatorname{diag}(\nu)\end{pmatrix}$.
No nonempty-mode hypothesis or supplied paired basis is required.

Set $R=\sqrt M$ and $A=RJR$. Apply the oriented skew paired basis construction to A; its frame matrix O satisfies
$O^TAO=\begin{pmatrix}0&D\\-D&0\end{pmatrix}$ with $D=\operatorname{diag}(\nu)$.
Since R and J are invertible, A is injective. A zero frequency would annihilate a nonzero orthonormal basis vector, so all frequencies are strictly positive.
With $E=\begin{pmatrix}0&\sqrt D\\\sqrt D&0\end{pmatrix}$, the same $S=R^{-1}OE$ satisfies all three congruences. The empty set gives vacuous frequency positivity and the unique empty matrices.

## Provenance and limits

The selected source is PK, *The Williamson normal form*, at the immutable URL above. The selected file has SHA-256
`fcf010d357e36c1112224100a6e89014c1776f7c5e09f97c130e379982b918a7`.
Its notices are “Copyright (c) 2026 PK. All rights reserved.” and “Released under Apache 2.0 license.” The adapted Lean source retains these notices, its modification attribution, and the complete Apache-2.0 grant distributed in the repository LICENSE. This is attributed established normal-form mathematics, with no new dependency.

Mathlib supplies Rayleigh eigenvectors, adjoint invariance of orthogonal complements, orthonormal basis completion/reindexing, matrix coordinate changes, functional calculus, inverse cancellation and symplectic membership. The paired-plane induction constructs the actual frame. Retire the port when the receiving pinned Mathlib supplies an exact directly usable equivalent.

This matrix normal form supplies a supporting Williamson step for the original quantum theorem 2.4, within consolidated theorem 2.3. It does not supply the actual observation-compatible Darboux split, metaplectic unitary, unbounded-operator domains, completed tensor factorization, oscillator spectrum, trace-class Gibbs state or product partition identities. Mathlib J is the negative of physical J+; multiplying a symplectic congruence by -1 preserves the physical sign convention for the same S.
