---
bibkey: iosuemooneyehrenberggorshkov2024toric
authors: Joseph T. Iosue, T. C. Mooney, Adam Ehrenberg, Alexey V. Gorshkov
year: 2024
title: "Projective toric designs, quantum state designs, and mutually unbiased bases"
doi: 10.22331/q-2024-12-03-1546
url: https://arxiv.org/abs/2311.13479v3
claim: "The paper defines projective toric t-designs on P(T^n), constructs them from difference and Sidon sets, disproves Zhu's conjecture on uniformly weighted quantum state 2-designs, shows that complete sets of mutually unbiased bases in dimension d correspond to P(T^d) 2-designs of size d^2 satisfying an overlap condition, finds by exhaustive search that no group design of size 36 in P(T^6) satisfies it, and conjectures that in any dimension a P(T^d) 2-design of size d^2 that is not a subgroup does not satisfy the overlap condition."
strata_touched:
  - D5/S3/Quantum/Measurements/ProjectiveToricDesignNonGroup
license: citation-only
triage: anchor
---

# Iosue, Mooney, Ehrenberg and Gorshkov, projective toric designs

## Verified locator

DOI: https://doi.org/10.22331/q-2024-12-03-1546 (Quantum 8, 1546, 2024).

Source: https://arxiv.org/abs/2311.13479v3

J. T. Iosue, T. C. Mooney, A. Ehrenberg and A. V. Gorshkov, arXiv:2311.13479v3 (the latest version). Quotations are from the v3 TeX source (`main.tex`).

## Statement

With $T=\mathbb R/2\pi\mathbb Z$ and $P(T^n)=T^n/T$ (quotient by the diagonal), points are written through representatives with $\phi_1=0$. A uniformly weighted $X$ is a $P(T^n)$ $t$-design when $\frac1{|X|}\sum_{\phi\in X}\exp\big(i\sum_{j=1}^t(\phi_{a_j}-\phi_{b_j})\big)$ equals $1$ if the multisets $\{\!\{a_j\}\!\}$ and $\{\!\{b_j\}\!\}$ coincide and $0$ otherwise. The overlap condition (Eq. `eq:toric-angle`, TeX macros expanded) is

> $$\forall \phi \neq \theta \in X: \quad \Big|\sum_{j=1}^{d} e^{i(\phi_j - \theta_j)}\Big|^2 \in \{0,d\},$$

and a complete set of mutually unbiased bases in dimension $d$ exists if and only if some $P(T^d)$ $2$-design of size $d^2$ satisfies it. After an exhaustive search excluding group designs of size $36$ in $P(T^6)$, the source states (TeX macros expanded, the equation reference written out):

> Let $d$ be any dimension and let $X$ be a $P(T^d)$ $2$-design of size $|X| = d^2$. If $X$ is not a subgroup of $P(T^d)$, then $X$ does not satisfy [the overlap condition].

and notes that the conjecture would prove the non-existence of complete sets of mutually unbiased bases in dimension $6$.

## Encoding and boundary

The repository writes points of $P(T^d)$ through the representatives with first coordinate $0$, requires in addition that $X$ contain the identity, and proves that the conjecture fails for $d=27$: the design built from the inverse of the Albert spread of $x\mapsto x^4$ over $\mathbb F_{27}$ is a $2$-design of size $729$ containing the identity, satisfies the overlap condition and is not closed under addition. The intended reading that every complete set of mutually unbiased bases admits some anchoring whose design is a group, the related conjectures for non-prime-power dimensions and the non-existence of complete sets in dimension $6$ are outside this conclusion.
