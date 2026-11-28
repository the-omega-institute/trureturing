---
slug: carrozza-chevrier-lionni-2026-corollary-seven-converses
bibkey: carrozzachevrierlionni2026detection
doi: 10.48550/arXiv.2611.27660
url: https://arxiv.org/abs/2611.27660v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/HiguchiSudbery/HiguchiSudberyEntropyMaximum
---

# The general converse criterion after Corollary 7

## Problem

The paragraph immediately after Corollary 7 asks:

> In general, whether the converse implication also holds (for $R_{\sigma}^{(n)}$ or its color-symmetric version $R^{(n)}$) remains an open question.

The single proposition here is the disjunction of the two universal converse assertions, as preregistered in issue #35139. Each assertion ranges over every integer $D\ge 3$, every family of positive finite local dimensions, every unit complex pure tensor, and every integer $n\ge 2$. Its hypothesis is irreducibility in Definition 1. The ordered assertion concludes $R_{\sigma}^{(n)}>0$ for every $\sigma\in S_D$. The color-symmetric assertion concludes $R^{(n)}>0$.

[Source sentence](https://arxiv.org/html/2611.27660v1#Thmtheo7) · [Preregistration #35139](https://github.com/the-omega-institute/trureturing/issues/35139)

## Motivation

The same four-qubit cluster-state family appears in Gour and Wallach's results on marginal entropy. The cited frozen module concerns normalized four-qubit tensors and marginal entropy, while this question concerns a trace ratio from a different multipartite graph contraction. Gour and Wallach's $C_1$ supplies the explicit vector.

[Gour and Wallach, Eq. (3)](https://arxiv.org/pdf/1006.0036v2)

## Gap

Proposition 8 proves the converse for three qubits, and Theorem 6 proves positivity for irreducible spectral hypergraph-tensor states. The source asks about arbitrary finite-dimensional tensors. The literature screen recorded in issue #35139 found no matching general settlement in the cited related papers and indices it examined.

[Proposition 8](https://arxiv.org/html/2611.27660v1#Thmtheo8) · [Theorem 6](https://arxiv.org/html/2611.27660v1#Thmtheo6) · [Literature screen](https://github.com/the-omega-institute/trureturing/issues/35139)

## Route

In finite orthonormal bases, compress product unit legs off each factor's support to one-dimensional legs. Enumerate proper supports in one direction and regroup factors with identical support and pad missing supports with units in the other direction. Absorb the comparison unitary of cited Definition 2.2 into one family of isometries into the common spaces. Cut rank is invariant under these embeddings and multiplies in the regrouped product. Prime singleton ranks force the active factor supports to partition the parties. Rank-one stripping then gives a rank-one proper cut of any hypothetical factorization. The proposed vector has a nonzero minor at every proper nonempty cut.

[Definition 1](https://arxiv.org/html/2611.27660v1#Thmtheo1) · [Cited Definition 2.2](https://arxiv.org/html/2604.02269#S2.Thmtheo2)

## Falsifier

A proper-support normalized factorization of the proposed vector up to local-unitary equivalence, or a nonzero ordered value for any color permutation and any integer order at least two for this vector, would invalidate the simultaneous witness as stated. The logarithm's argument must be checked in the real domain of Eq. (30).

## Evidence

The normalized vector has amplitudes $1/2$ on $0000$, $0011$ and $1100$, amplitude $-1/2$ on $1111$, and zero elsewhere. In the endpoint basis $(00,01,10,11)$, the four-party specialization of Eq. (24) has matrix $ee^T/16$ for each permutation, where $e=(1,0,0,1)^T$. Its Gram matrix $X=ee^T/128$ has trace $t=1/64$ and satisfies $X^2=tX$. Thus $\mathrm{tr}(X^n)=t^n$, the logarithm has argument one, and all ordered values and their factorial-normalized average vanish for every $n\ge 2$. In Lean the closed proposition is named `claim`, and `result` has literal type `¬ claim`.

[Eqs. (24)–(26)](https://arxiv.org/html/2611.27660v1#S0.E24) · [Eqs. (30)–(31)](https://arxiv.org/html/2611.27660v1#S0.E30)

## Triage

Theorem. Issue #35139 preregisters the proposed Tier 1 settlement. The state refutes the arbitrary-finite-dimension converse criterion by a single four-party example.

## ASSUMED-UNVERIFIED

The cited literature screen has bounded source and index coverage. Native MathDB coverage remains unverified. The comparison of the paper's graphical and Hilbert-space definitions with their finite-coordinate counterparts is given in the Blueprint.

[Search scope and MathDB result](https://github.com/the-omega-institute/trureturing/issues/35139)
