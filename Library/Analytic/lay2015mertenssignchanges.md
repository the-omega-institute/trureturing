---
bibkey: lay2015mertenssignchanges
authors: Jeffrey P. S. Lay
year: 2015
title: Sign changes in Mertens' first and second theorems
doi: null
url: https://arxiv.org/abs/1505.03589v1
claim: The unnumbered identities in the proof of Lemma 4 identify the unconditional Chebyshev tail and its exact value at one; equation (9) alone is an asymptotic Mertens-error identity.
strata_touched: []
license: citation-only
triage: anchor
---

# Existing Chebyshev primitive and its normalization

The inspected primary is [arXiv:1505.03589v1](https://arxiv.org/pdf/1505.03589v1), 14 May 2015. Lemma 4 and its proof occupy printed p.6. This note uses that preprint; no journal version or DOI is asserted. The paper writes $C_0$ for Euler's constant, as specified on printed p.1.

Let $\psi(x)=\sum_{n\le x}\Lambda(n)$ and $\psi_r(x)=\sum_{n\le x}\Lambda(n)/n$, with the same endpoint convention. The unnumbered integration-by-parts displays and constant evaluation in the proof of Lemma 4 directly give

$$
J(x)=\int_x^\infty\frac{\psi(t)-t}{t^2}dt
=\log x-(1+\gamma)+\frac{\psi(x)}x-\psi_r(x),
\qquad J(1)=-(1+\gamma).
$$

These identities are unconditional. Both counting functions vanish for $1<x<2$, and their jumps cancel in the displayed combination at every prime power. Equation (9) instead concerns the paper's prime-only Mertens error $M_1(x)$ and contains an $O(x^{-1/2})$ term; that equation is not substituted for this exact all-prime-power identity.

## Parameter correspondence

In the [actual FIB contour interface](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md), §415 identifies the existing boundary inverse $h(u)$ with $J(e^u)$ for $u>0$ through two representations of the same $I_\psi$. The source's $x$ is $e^u$, and its $C_0$ is the project's $\gamma$. This interface is a paper application, not a statement printed in Lay's article and not Lean verified.

The source therefore directly supplies the actual normalization $h(0)=-(1+\gamma)$ and $h(u)=u-(1+\gamma)$ for $0<u<\log2$, after the separate interface and continuity are established. It does not supply an unconditional square-root decay estimate, a Robin comparison or an RH proof. The [published weighted-error supplier](bhattacharyamartinsimpson2026weightedprimeerrors.md) gives an exact quantitative match with an explicit RH premise.
