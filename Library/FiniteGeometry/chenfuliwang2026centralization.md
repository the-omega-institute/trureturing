---
bibkey: chenfuliwang2026centralization
authors: Yanru Chen; Houshan Fu; Ang Li; Suijie Wang
year: 2026
title: Convolution-type Identity for Characteristic Polynomials of Geometric Semilattices
doi: 10.48550/arXiv.2606.00599
url: https://arxiv.org/abs/2606.00599v1
claim: Corollary 1.2 gives the centralization convolution and the final paragraph of §4.2 asks for its interpretation by a natural CRT bijection.
strata_touched:
  - D5/S3/Combinatorics/Geometry/HyperplaneArrangements/CentralizationBijection
license: citation-only
triage: anchor
---

<!-- GID: D5/L/FiniteGeometry/chenfuliwang2026centralization -->

# Convolution-type Identity for Characteristic Polynomials of Geometric Semilattices

## Verified locator

[arXiv:2606.00599v1](https://arxiv.org/abs/2606.00599v1), v1 submitted 30 May 2026, printed pp. 3–5 and 15–17.
[DOI](https://doi.org/10.48550/arXiv.2606.00599).

The question in the final paragraph of §4.2, printed p. 17, reads

> It is natural to conjecture that the convolution formula established in Corollary 1.2 should also admit a corresponding interpretation over $\mathbb{Z}_{pq}$, $\mathbb{Z}_p$, and $\mathbb{Z}_q$. To date, however, we have not been able to find a natural bijection that proves this. We therefore record this as an open problem, in the hope that it may be resolved by other researchers in the future.

[Versioned PDF, p. 17](https://arxiv.org/pdf/2606.00599v1#page=17)

## Which convolution?

Corollary 1.2 on p. 3 sums over the linear flats of the centralization of an arrangement. For each flat V the factors are the characteristic polynomials of the central restriction to V and the affine localization at V, at the second and first arguments respectively. Definition 2.4 on pp. 4–5 defines the localization by those affine hyperplanes that contain V or are disjoint from it. The restriction intersects with V and omits empty and whole-flat intersections. Section 4.1 gives a finite-field interpretation using a degree-two extension. Theorem 4.6 on pp. 16–17 proves Wang's distinct convolution by CRT, using the affine flats of the original arrangement and its restriction and containing-hyperplane subarrangement at each such flat. [Corollary 1.2 and Definition 2.4](https://arxiv.org/pdf/2606.00599v1#page=3)

For the modular setting, Proposition 4.4 (Athanasiadis [Ath99, Theorem 2.1]) states that for an integral arrangement A in real n-space there exist positive integers q_A and ρ_A depending only on A. For every positive integer m greater than q_A, coprime to ρ_A, the intersection posets of A and A_m are naturally isomorphic and χ(A,m) equals the cardinality of the complement in (ℤ/mℤ)^n. The isomorphism sends V to the intersection of the reductions of hyperplanes containing it. Under those same conditions Lemma 4.5 identifies the reductions of containing-hyperplane subarrangements and restrictions with the corresponding subarrangements and restrictions of A_m, and their intersection posets. Theorem 4.6 additionally requires p and q coprime to each other and each greater than q_A and coprime to ρ_A. [Proposition 4.4 and Lemma 4.5](https://arxiv.org/pdf/2606.00599v1#page=15)

## Relation to the repository result

The exact registered target in [issue #34739](https://github.com/the-omega-institute/trureturing/issues/34739) uses a finite type of integer affine rows, a single positive D independent of p and q, all p,q greater than 1 with gcd(p,q)=gcd(p,D)=gcd(q,D)=1, and an actual equivalence of the concrete complements. The first residue is preserved coordinatewise. Rational central flats are actual common-kernel subspaces of the rational coordinate space. Integral minors give equal ranks over ℚ and ℝ for every row subset and after adjoining any row, so row closures agree. A row's normal vanishes identically on V exactly when the affine hyperplane contains V or is disjoint from V. A nonzero restriction is surjective and meets the affine equation properly. Good reduction of homogeneous implication ensures that the modular common kernel depends only on the rational flat and that rows outside its closure give proper homogeneous restrictions.

The checked construction splits z by CRT as (x,zq), chooses c(x) solving all the original affine rows hit by x over ℤ/qℤ, and sets y=zq−c(x). The output consists of the rational flat indexed by the exact homogeneous zero rows of y, together with x and y in the corresponding fibres. The inverse adds the same center and applies inverse CRT. The proof uses integer good-reduction certificates for all subsystems, including affine inconsistency and homogeneous implication over composite good moduli. It implements any valid center family through a transport parametrized by such a family and uses Classical.choose for its existence. The lexicographically least satisfying vector in coordinate order with residues 0 through q−1 yields the deterministic mathematical variant, since the solution set is finite and nonempty.

The cardinality identity holds at all modulus pairs covered by the Lean theorem. For a real integral hyperplane arrangement, the characteristic-polynomial reading follows from the source's counting results under additional hypotheses. Apply Proposition 4.4 to A at pq and each integral affine localization at p. Apply Lemma 4.5 to the centralization and Proposition 4.4 to the central restrictions in integral coordinates on the rational flats at q. Integral lattice kernel bases with the relevant invariant factors invertible give compatible coordinates. It suffices to take coprime p and q each greater than the maximum of 1 and the finitely many counting thresholds, and each coprime to the product of D, the applicable periods and the coordinate factors. These conditions also cover the counting requirements at pq. The Lean result is the bijection with both inverse laws and the first-residue equation. The characteristic-polynomial evaluation follows from the cited counting results.

## Literature check

The preregistration records the checked arXiv v1 and DataCite entry, zero indexed forward citations, no matching repository problem, and related Chen–Li–Wang and Fu papers about other enumerations. The cited literature supplies good reduction, modular counting and Wang's different convolution. No solution to this particular bijection surfaced in those checks. OpenAlex citing-works lookup was rate limited and a thesis landing page inaccessible. Unindexed coverage remains unverified. [Preregistration](https://github.com/the-omega-institute/trureturing/issues/34739)
