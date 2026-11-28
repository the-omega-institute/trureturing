---
bibkey: sushkov2026jacobihurwitz
authors: Matvey Sushkov
year: 2026
title: Correlators of the Jacobi Unitary Ensemble on a General Interval and Hurwitz Numbers
doi: 10.48550/arXiv.2611.02795
url: https://arxiv.org/abs/2611.02795v1
claim: "Section 6, item 1 asks whether multiplicativity of the partition coefficients in (6.1) is necessary for the Frobenius image to be a KP tau function."
strata_touched:
  - D5/S3/Combinatorics/PerfectMatchings/SushkovKPMultiplicativityRefutation
license: citation-only
triage: anchor
---

# Sushkov’s KP multiplicativity question

## Source statement

Version 1, dated 2 November 2026, §6 “Conclusion and open problems,”
item 1, printed p. 29, asks the following.

> For which coefficients $a_\nu$, not necessarily multiplicative, is $\mathrm{ch}\,[(6.1)]$ a tau function of the KP hierarchy in $u$? Multiplicativity of $a_\nu$ is sufficient, but we do not know whether it is necessary.

Equation (6.1), printed p. 28, sums over all degrees n ≥ 0 and partitions
ν of n. At H(x) ≡ 1
and N = 1 the Jucys–Murphy factors are all units, including the empty
product. N specifies the argument Jᵢ/N and leaves all partition lengths in
scope. Equations (2.14)–(2.15), printed p. 12, send a permutation of
cycle type ν to $p_\nu/n!$ and the unscaled class sum $C_\nu$ to
$p_\nu/z_\nu$, where $z_\nu = \prod_{j\ge1} j^{m_j}m_j!$ and $m_j$
counts parts of size $j$. Equation (1.14) gives
$p_\nu(u) = \prod_{r\in\nu} u_r$. Set uⱼ = pⱼ = j tⱼ for the KP times.
[Pinned PDF](https://arxiv.org/pdf/2611.02795v1)

## Exact scope

The necessity clause requires a single value bⱼ for each positive size,
with $a_\nu = \prod_{r\in\nu} b_r$ for every partition. The product includes every repeated
part and equals one for the empty partition. The normalized family with
a∅ = a₍₁₎ = 1 and all coefficients of degree at least two zero maps to
1 + t₁. The full bilinear residue vanishes for independent time sequences:
after clearing z⁻², the shifted product is
((1 + t₁)z − 1)((1 + s₁)z + 1). The exponential has constant coefficient
one and linear coefficient t₁ − s₁, so the residue equals
(1 + t₁) − (1 + s₁) − (t₁ − s₁) = 0. The partition (1) forces b₁ = 1
and (1,1) forces the contradiction 0 = b₁² = 1. The scope is the necessity
clause. The full classification, the sufficient construction and items 2
and 3 are separate questions.
[Preregistration](https://github.com/the-omega-institute/trureturing/issues/35289)

## Literature

The affine tau function follows from the classical shifted Schur
construction. Kac and van de Leur give the equal-charge bilinear
criterion in (3)–(4) and the polynomial construction in Theorem 16(a)
and (52). The choice λ = (1) with time shift (1, 0, 0, …) gives 1 + t₁.
[Kac–van de Leur, arXiv:1801.02845v2](https://arxiv.org/pdf/1801.02845v2)

The preregistration records the v1 arXiv check, an OpenAlex exact DOI
citation count of zero, the Formal Conjectures and repository duplicate
searches, and a Crossref title search covering the top five results.
Its outcome for an explicit settlement of this necessity clause was
`not-found-in-searched-scope`. Semantic Scholar and OpenAlex title
searches were rate-limited. MathDB coverage and bibliographic priority
remain unverified. [Preregistered literature screen](https://github.com/the-omega-institute/trureturing/issues/35289)
