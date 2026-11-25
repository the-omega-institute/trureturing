---
bibkey: rajchelgasiorowskizyczkowski2018robust
authors: Grzegorz Rajchel; Adam Gąsiorowski; Karol Życzkowski
year: 2018
title: "Robust Hadamard Matrices, Unistochastic Rays in Birkhoff Polytope and Equi-Entangled Bases in Composite Spaces"
doi: 10.1007/s11786-018-0384-y
url: https://arxiv.org/abs/1804.10715v2
claim: "Two n×n permutation matrices are complementary when P_ij = P_hk = Q_ik = 1 implies Q_hj = 1, and strongly complementary when moreover their nonzero entries lie in different places; the paper asks how the maximal number of pairwise strongly complementary permutation matrices depends on n. Appendix A presents Haagerup's one-phase procedure for order-four unistochasticity."
strata_touched:
  - D5/S3/Combinatorics/Permutation/StronglyComplementaryPermutationMaximum
  - D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic
  - D5/S3/Quantum/Measurements/ThreeDistinguishabilityMixedPurity
license: citation-only
triage: anchor
---

# Rajchel, Gąsiorowski and Życzkowski, Robust Hadamard matrices, unistochastic rays in Birkhoff polytope and equi-entangled bases in composite spaces

G. Rajchel, A. Gąsiorowski and K. Życzkowski, Mathematics in Computer Science 12, 473–490 (2018); arXiv:1804.10715v2. Quotations are from the v2 TeX source.

Permutation matrices $P$ and $Q$ are complementary if $P_{ij}=P_{hk}=Q_{ik}=1$ implies $Q_{hj}=1$ for all $i,j,h,k$, and strongly complementary if moreover $P_{ij}=1$ implies $Q_{ij}=0$. With $P=\mathbb I$, $Q$ is strongly complementary exactly when it is an involution with zero diagonal. For a set of $k$ pairwise strongly complementary permutation matrices of dimension $n$, the paper notes $k\le n$ and states:

> We are not able to determine how the maximal number $k$ of such matrices depends on the dimension $n$, nor whether the bistochastic matrices belonging to the interior of this polytope are unistochastic.

## Haagerup's order-four unistochasticity procedure

Appendix A of the arXiv v2 PDF (pp. 13–14) describes a procedure due to
Uffe Haagerup. The flat matrix has a real Hadamard lift. For another
bistochastic matrix of order four, permute rows and columns so that the
upper-left 2 × 2 block of a prospective unitary has squared
Hilbert–Schmidt norm below one. In the block notation of Eq. (7.1), this
makes the adjacent block X invertible when the first two rows are
orthonormal. Complete the quadrilaterals for the first two rows and the
first two columns at a common choice of the free phase φ. Then
D = −YA* (X*)⁻¹ by Eq. (7.3). The decision condition asks whether some
choice of φ and the completions yields |D₁₁|² = B₃₃.

For B = [p,p,p,1−3p] with nonuniform p under the row cap, use two
repeated columns and the two smallest weights as the first two rows.
The block sum is twice the sum of those weights and is strictly below
one. The prior procedure therefore applies to the slice studied by the
repository's cubic module. Korzekwa et al., arXiv:1812.09083v3,
Appendix C.3, report applying it there. Once the mixed-to-pure reduction
holds on the full simplex, the repeated-column problem and its exact cubic
criterion also decide the mixed region.

- Appendix A, Eqs. (7.1)–(7.5) and the one-entry modulus test. [arXiv v2 PDF](https://arxiv.org/pdf/1804.10715v2)

## Verified locator

Source: https://arxiv.org/abs/1804.10715v2
- DOI: https://doi.org/10.1007/s11786-018-0384-y (Mathematics in Computer Science 12(4), 473–490; title, authors, journal, volume, issue and pages from Crossref).
- URL: https://arxiv.org/abs/1804.10715v2. The e-print member `unisto9.tex` has 1401 lines and md5 `bc7893394ee3708e2bb9d4ba277b4a41`. Locations:
  - complementary permutation matrices, Definition 4.1, l. 605–611; strong complementarity, Definition 4.3, l. 622–626;
  - the involution reformulation, l. 630–636; the question, l. 678–690.
