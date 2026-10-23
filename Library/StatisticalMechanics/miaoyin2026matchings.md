---
bibkey: miaoyin2026matchings
authors: Tianshun Miao; Yitong Yin
year: 2026
title: Sampling Matchings in Near-linear Time
doi: null
url: https://arxiv.org/abs/2609.21936v1
claim: Unit-deletion insertion dynamics on a positive downward-closed law gives exact monomial covariance and energy matrices; low-degree approximation bounds additionally require field-dynamics spectral stability and an integrable rate.
strata_touched: []
license: citation-only
triage: anchor
---

# Monomial forms and the field-dynamics approximation boundary

The primary source is [arXiv:2609.21936v1](https://arxiv.org/pdf/2609.21936v1),
Section 3.2, equations (13), (21) and (22). The source's principal
sampling results concern matchings. The monomial calculation in
Section 3.2 applies to a general positive law on a downward-closed
finite configuration family.

Its auxiliary insertion-deletion dynamics deletes every occupied
coordinate at rate one and inserts a legal coordinate with rate
equal to the occupied-to-empty mass ratio. Equation (13) counts
each edge through its occupied endpoint. At retention one, the
normalized monomial formulas in (21)–(22) give, after removing the
normalizations,

$$
\operatorname{Cov}(m_I,m_J)
=\mu_{I\cup J}-\mu_I\mu_J,\qquad
\mathcal E_1(m_I,m_J)=|I\cap J|\mu_{I\cup J}.
$$

For the product-activity weighted heat-bath form, the deletion rate
at site $i$ is instead $\omega_i/(1+\lambda_i)$. The same occupied
endpoint calculation replaces the intersection cardinality by
$\sum_{i\in I\cap J}\omega_i/(1+\lambda_i)$. This is a weighted
application of the published mechanism, not a new general monomial
energy principle. No independence of occupations is assumed.

Lemma 3.2's quantitative approximation estimate uses Definition
1.1's covariance domination for every positive pinning of every
decreasing-field posterior. The rate must be nonincreasing,
at least one, and have finite integral of $(C(t)-1)/(1-t)$.
A legal insertion-ratio bound also enters the comparison with
uniform-coordinate heat-bath dynamics. These constants have not
been bounded uniformly for arbitrary positive FIB activities and
site weights. The auxiliary unit-deletion clock must not be
substituted for the FIB normalized heat-bath clock.

This note cites the source without redistributing its text or PDF.
