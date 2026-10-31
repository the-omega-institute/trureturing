---
bibkey: monraswinter2014realization
authors: Alex Monràs; Andreas Winter
year: 2014
title: "Quantum learning of classical stochastic processes: The Completely-Positive Realization Problem"
doi: null
url: https://arxiv.org/abs/1412.3634v1
claim: "Section 2 distinguishes a future-sufficient latent-variable factorization from a finite positive realization; Theorem 6 characterizes positive realizations by a convex pointed polyhedral invariant cone with initial and dual terminal conditions."
strata_touched: []
license: citation-only
triage: anchor
---

## Primary source and exact conditions

Alex Monràs and Andreas Winter, arXiv:1412.3634v1, [primary text](https://arxiv.org/html/1412.3634v1).

Section 2 begins with the conditional-independence factorization

$$
p(\mathbf v\mid\mathbf u)
 =\sum_X P(\mathbf v\mid X)P(X\mid\mathbf u).
$$

Its process setting assumes stationary word probabilities. A positive realization additionally supplies common nonnegative word maps, an initial element and a terminal functional. Theorem 6 states that a quasi-realization $(\mathcal V,\pi,D,\tau)$ has an equivalent positive realization exactly when there is a convex pointed polyhedral cone $\mathscr C$ with $\tau\in\mathscr C$, $D^{(v)}\mathscr C\subseteq\mathscr C$ for all words, and $\pi\in\mathscr C^*$. Example 2 uses dense rotations to explain a non-polyhedral obstruction. These are literature-attested suppliers; none is a repository-new theorem.

Section 4, Theorem 9, identifies quotient realizations of the same process up to linear isomorphism. It does not identify every larger hidden state space with the quotient, nor does it supply a positive lift from mere linear dimension.

## Native terminal parameter map

[Continuation III, Definition 143.1 and Theorem 143.2](../../docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_III.md) use the conditional-factorization meaning with past $a$, externally requested continuation $f$ and event $w$. The encoding $\alpha_a(s)$ corresponds to the conditional latent distribution, and $\beta_{f,w}(s)$ to the future response. This map supplies no source-generated probability law, no stationarity-to-intervention theorem and no cross-programme statistical equality.

That result permits arbitrary responses for whole continuations, without requiring positive per-letter transitions or a common invariant cone. It proves its finite native witnesses directly from the specified Fibonacci source and one original terminal event. The paper's general positive-realization criterion, Example 2 and quotient theorem are not renamed as the native result. Quantum CP realization, arbitrary physical preparations, affine mixing and statistical learning guarantees are not imported.
