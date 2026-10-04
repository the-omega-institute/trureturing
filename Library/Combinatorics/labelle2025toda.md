---
bibkey: labelle2025toda
authors: Labelle, A.
year: 2025
title: On a specialization of Toda eigenfunctions
doi: 10.48550/arXiv.2502.10655
url: https://arxiv.org/abs/2502.10655v3
claim: Conjecture 7.3 states that the polynomial (q)_α² J_α is unimodal.
strata_touched:
  - D5/S0/Certificates/Combinatorics/TodaSpecializationUnimodalityRefutation
license: citation-only
triage: anchor
---

# Labelle's Toda specialization

## Verified locator

DOI: 10.48550/arXiv.2502.10655.
Primary version: https://arxiv.org/abs/2502.10655v3.
The mathematical text is available at https://arxiv.org/html/2502.10655v3.
Section 1, Definition 1.1 and equation (2), supplies the fermionic recursion
and the displayed q-factor. Section 7, Conjecture 7.3, page 21, states the
unimodality assertion in the paper's general root-system setting.

## Statement and scope

Section 1, page 1, states:

> Let $\mathfrak{g}$ be a split semisimple Lie algebra over $\mathbb{Q}$ with Cartan subalgebra $\mathfrak{h}$ and let $\Phi \subseteq \mathfrak{h}^*$ be its root system. Fix a choice of positive roots $\Phi_+ \subseteq \Phi$ and let $\alpha_1, \ldots, \alpha_n$ be the corresponding simple roots. … Let $(\cdot, \cdot)$ be the invariant bilinear form on $\mathfrak{h}^*$, normalized so that short roots have length $2$. Let $d_i=\frac{(\alpha_i,\alpha_i)}{2}$ and let $a_{ij} = \frac{(\alpha_i,\alpha_j)}{d_i}$ be the entries of the Cartan matrix.

Definition 1.1, page 1, states:

> Define $\mathfrak{J}_\alpha \in \mathbb{Q}(q)$, for $\alpha \in Q^{\ge 0}$, by $\mathfrak{J}_\alpha = \sum_{0 \le \beta \le \alpha} \frac{q^{\frac{(\beta, \beta)}{2}}}{(q)_{\alpha-\beta}} \mathfrak{J}_\beta$ and $\mathfrak{J}_0 = 1,$ where $(q)_{\alpha}=\prod_{i=1}^n \prod_{j=1}^{a_i} (1-q^{d_i j})$ for $\alpha= \sum a_i \alpha_i \in Q^{\ge 0}$.

Conjecture 7.3, page 21, states:

> The polynomial $(q)_\alpha^2\mathfrak{J}_\alpha$ is unimodal.

The C₂ datum uses short-root Gram matrix `[[2, −2], [−2, 4]]`, `d = (1, 2)`, and `α = 2α₁ + 2α₂`. The certificate polynomial is
`1 + q + 3q² + 2q³ + 5q⁴ + 2q⁵ + 3q⁶ + q⁷ + q⁸`, whose coefficients contain the strict valley `3, 2, 5`.

Equation (2) on page 1 moves the self-term to the left and gives, for α>0,

$$
\mathfrak{J}_\alpha = \frac{1}{1-q^{(\alpha,\alpha)/2}}
\sum_{0\le\beta<\alpha}\frac{q^{(\beta,\beta)/2}}{(q)_{\alpha-\beta}}
\mathfrak{J}_\beta.
$$

The module defines this recursion in `RatFunc ℚ` on normalized finite-type
symmetrizable Cartan data of every finite rank. Coordinates are functions
`Fin r → ℕ`, and the Gram quadratic form is even on integral coordinates.
The exponent is its exact integer half, used with integer powers in `RatFunc ℚ`.
Unimodality uses the finite coefficient list through `natDegree`. The nine C₂ certificate identities
are consequences of this recursion, rather than defining values of J.
An existential polynomial with the indicated rational-function image uniquely
represents the polynomial because the algebra map `ℚ[X] → RatFunc ℚ` is injective.
