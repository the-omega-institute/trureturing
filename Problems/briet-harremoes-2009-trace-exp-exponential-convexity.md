---
slug: briet-harremoes-2009-trace-exp-exponential-convexity
bibkey: briet2009jensenshannon
doi: 10.1103/PhysRevA.79.052311
url: https://arxiv.org/abs/0806.4472v4
triage: theorem
motivation_gids:
  - D5/S3/Divergence/TraceExpExponentialConvexityRefutation.result
---

# The trace exponential is not exponentially convex on density matrices

## Problem

Jop Briët and Peter Harremoës, *Properties of classical and quantum Jensen-Shannon divergence*, Physical Review A 79, 052311 (2009), arXiv:0806.4472v4, Definition 4 (Exponential convexity):

> Let X be a convex set and φ : X → R a mapping. Then φ is said to be exponentially convex if the function X × X → R given by (x, y) → φ((x+y)/2) is positive definite.

§VI (Conclusions and open problems):

> Whether (QJD1)^{1/2} is a metric for all mixed states remains unknown. However, based on a large amount of numerical evidence, we conjecture the function A → Tr(e^A) to be exponentially convex for density matrices A. Proving this would imply that QJDα is negative definite for α ∈ (0, 2], and hence the square of a metric that can be embedded in a real Hilbert space.

## Motivation

The conjecture proposes a route from exponential convexity to negative definiteness of the quantum Jensen–Shannon divergence. Positive definiteness requires every finite real quadratic form of the midpoint kernel to be nonnegative.

## Gap

For density matrices $\rho_i$ and real coefficients $c_i$, the assertion requires $\sum_{i,j}c_i c_j\operatorname{Tr}\exp((\rho_i+\rho_j)/2)\ge0$. Four qubit states suffice to contradict it.

## Route

Use the maximally mixed state and three real rank-one projectors:

$$
\rho_0=\frac12 I,\quad
\rho_1=\begin{pmatrix}1&0\\0&0\end{pmatrix},\quad
\rho_2=\begin{pmatrix}1/4&\sqrt3/4\\\sqrt3/4&3/4\end{pmatrix},\quad
\rho_3=\begin{pmatrix}1/4&-\sqrt3/4\\-\sqrt3/4&3/4\end{pmatrix}.
$$

All four are positive semidefinite with trace one. For real $t\ne0$, put $u=e^{t/4}$ and $c=(-3(u+u^{-1})/2,1,1,1)$. Explicit rotations diagonalize each sum of two states. The kernel $K_{ij}=\operatorname{Tr}\exp(t(\rho_i+\rho_j)/2)$ has

$$
K_{00}=2u^2,\qquad K_{kk}=u^4+1\ (k>0),\qquad
K_{ij}=u^3+u\quad(i\ne j).
$$

## Falsifier

The exact quadratic form is

$$
\sum_{i,j=0}^3c_i c_jK_{ij}=-\frac32(u-1)^4<0.
$$

Since the real exponential is injective, $t\ne0$ implies $u\ne1$. The same states refute every nonzero temperature parameter, including its negative sign.

## Evidence

`D5/S3/Divergence/TraceExpExponentialConvexityRefutation.lean` defines `trExp` using Mathlib's matrix exponential, `IsDensity`, and the exact finite positive-definiteness assertion `claim`. The theorem `family` constructs a negative quadratic form for every $t\ne0$; `result : ¬ claim` uses `family 1 one_ne_zero`. The supporting lemmas are private. The proof computes the matrix exponential by conjugating diagonal matrices and then proves the displayed real polynomial identity. Both public theorems use only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorry` or additional axiom.

## Triage

### What the settlement shows

1. **Proved (Lean) — the trace-exponential conjecture fails.** The centre-plus-trine qubit configuration gives the certified quadratic-form identity $-\frac32(u-1)^4$. The failure holds for every real $t\ne0$, so the kernels $\operatorname{Tr}e^{-t(\rho+\sigma)/2}$ used in the proof scheme also fail positive definiteness.

2. **Reasoning — the symmetric block explains the obstruction.** With Bloch vectors $b_i$ and $\rho_i=(I+b_i\cdot\sigma)/2$, the qubit kernel is $K_{ij}=2e^{t/2}\cosh(t|b_i+b_j|/4)$. Restricting the centre-plus-trine kernel to the centre and the normalized sum of the three pure states gives the block

   $$
   \begin{pmatrix}2u^2&\sqrt3(u^3+u)\\\sqrt3(u^3+u)&u^4+1+2(u^3+u)\end{pmatrix}.
   $$

   Its determinant is $-u^2(u-1)^4=-4u^4(\cosh(t/4)-1)^2$, strictly negative when $t\ne0$. These block and Bloch formulas are reasoning; the certified statement is the quadratic-form identity above. The pure-state kernel is positive definite in the paper's Lemma 5, so the mixed centre is necessary in this mechanism.

3. **Computed — five random mixed qubit states already violate the assertion.** At $t=1$, the following Bloch vectors give a double-precision kernel with minimum eigenvalue approximately $-1.39805644042\cdot10^{-5}$:

   $$
   \begin{pmatrix}
   0.154797569556&-0.255119901323&-0.861888260057\\
   -0.662089804100&0.070383184311&0.061858775706\\
   0.175382034576&0.058939030070&0.494804068611\\
   0.200993681097&-0.214184343478&0.739283816694\\
   0.512414101302&0.347359294060&0.257649132399
   \end{pmatrix}.
   $$

   Their Euclidean norms are below one. This numerical example is distinct from the exact Lean certificate.

4. **Reasoning — the proposed embedding route is closed.** Exponential convexity of $A\mapsto\operatorname{Tr}e^A$ cannot provide the proposed argument for Hilbert-space embeddability of quantum Jensen–Shannon divergence. This refutes the premise of that route, rather than its desired embedding conclusion.

5. **Open — higher-dimensional Hilbert-space embeddability.** Embeddability of $\sqrt{\mathrm{QJSD}}$ in a real Hilbert space for dimension at least three is not settled here. Dániel Virosztek, arXiv:1910.10447, proves the metric property in every dimension and attributes the qubit embedding to Carlen–Lieb–Seiringer. The metric and embedding properties are separate assertions.

## ASSUMED-UNVERIFIED

The Bloch formula, symmetric-block determinant, numerical eigenvalue, and literature consequences are not additional Lean theorems in this module. The numerical eigenvalue is a floating-point calculation, without an interval certificate. No novelty or priority conclusion beyond the named conjecture's refutation is asserted.
