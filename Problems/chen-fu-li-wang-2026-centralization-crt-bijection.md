---
slug: chen-fu-li-wang-2026-centralization-crt-bijection
bibkey: chenfuliwang2026centralization
doi: 10.48550/arXiv.2606.00599
url: https://arxiv.org/abs/2606.00599v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Geometry/HyperplaneArrangements/CentralizationBijection
---

# Chen–Fu–Li–Wang centralization CRT bijection

## Problem

The final paragraph of §4.2, printed p. 17, of Yanru Chen, Houshan Fu, Ang Li and Suijie Wang, *Convolution-type Identity for Characteristic Polynomials of Geometric Semilattices*, arXiv:2606.00599v1 (v1 submitted 30 May 2026), asks

> It is natural to conjecture that the convolution formula established in Corollary 1.2 should also admit a corresponding interpretation over $\mathbb{Z}_{pq}$, $\mathbb{Z}_p$, and $\mathbb{Z}_q$. To date, however, we have not been able to find a natural bijection that proves this. We therefore record this as an open problem, in the hope that it may be resolved by other researchers in the future.

[Primary source](https://arxiv.org/pdf/2606.00599v1#page=17)

The quantified target was preregistered before the proof in [issue #34739](https://github.com/the-omega-institute/trureturing/issues/34739). For every dimension and every integral affine row system on a universe-polymorphic finite index type, there is a positive D, chosen before p and q, such that all p,q>1 with gcd(p,q)=gcd(p,D)=gcd(q,D)=1 admit an equivalence from the product-modulus complement to the dependent sum over rational central flats V of the affine-localization complement modulo p and the central-restriction complement in the reduced V modulo q. The first vector equals the original point reduced coordinatewise modulo p, given by the literal cast from `ZMod (p * q)` to `ZMod p`.

## Motivation

Tier 1, recent published open question. Corollary 1.2 uses centralization, while Theorem 4.6 in §4.2 gives Wang's CRT bijection using affine flats of the original arrangement. The desired interpretation involves genuine modular complement fibres over central flats, including composite coprime moduli.

## Gap

The preregistration reports source verification, DataCite and zero indexed forward citations, no matching problem in the repository and no answer in checked later Chen–Li–Wang or Fu papers. Athanasiadis and Kamiya–Takemura–Terao give good reduction and counting methods, and Wang's convolution has the other flat indexing. OpenAlex citing-works was rate limited and one thesis landing page inaccessible. Coverage of unindexed work remains unverified.

## Route

Construct integer good-reduction certificates from rational solutions and integral separating functionals for inconsistent rational systems. The product of finitely many positive certificate integers controls both affine solvability and homogeneous row implication, including over rings with zero divisors. For a CRT split (x,zq), the affine rows hit at x are rationally consistent and therefore have a center c(x) over ℤ/qℤ. Subtract the center and tag the result y with its exact zero rows. Homogeneous implication closes the tag; its rational common kernel is the actual flat. An excluded original row would require simultaneous affine hits in both CRT coordinates, equivalent to an affine hit at x and a zero row of y. The inverse adds the same center before inverse CRT. Both inverse laws and first-residue preservation follow from these maps and the exact flat reindexing.

## Falsifier

A finite integral row system for which no positive D makes the specified equivalence possible for all good coprime moduli would refute the universal assertion. A fixed bad modulus outside the coprimality conditions, failure of a particular choice of center to satisfy the required equations, or an example involving a different affine-flat indexing would leave the quantified assertion undecided.

## Evidence

The endpoint is `D5/S3/Combinatorics/Geometry/HyperplaneArrangements/CentralizationBijection.result`. The checked module constructs an actual Equiv, retaining its inverse laws and the first-residue equation for all coordinates. Its domain is the original integral affine complement and its codomain the dependent sum of concrete fibres indexed by actual rational common kernels. Integral minors give equal ranks over the rationals and reals for each row set and after adjoining any row. Thus rational and real flats correspond by extension of scalars and have the same row closures. Definition 2.4 identifies the rows whose normals vanish on the flat with the affine localization rows. At p the complement lies in the original ambient dimension. At q the complement lies in the reduced flat, of dimension dim V in compatible coordinates, and avoids each proper homogeneous restriction. The source's Proposition 4.4 and Lemma 4.5 give the characteristic-polynomial interpretation under their arrangement-specific size and good-reduction bounds. See [versioned source](https://arxiv.org/pdf/2606.00599v1#page=15).

## Triage

theorem. The quantified bijection in #34739 is proved by the endpoint above.

### What the settlement shows

- Proved in the module. There is a uniform positive D for the row system, with a concrete complement equivalence and preserved first residue at every allowed p,q, including composite moduli.
- Proved by the construction in the module. Translation by a valid family of modular centers and its inverse give the transport. The implementation obtains that family with Classical.choose.
- Mathematical consequence. The lexicographically least satisfying center exists at each first residue because the set of satisfying vectors is finite and nonempty. The same construction with this choice gives the deterministic variant.
- The equivalence gives equality of the complement cardinality at pq and the sum over central flats of the products of the two fibre cardinalities at p and q. This holds for all modulus pairs in the theorem, including composite good moduli.
- For real integral hyperplane arrangements, Proposition 4.4 evaluates each relevant complement count at a positive modulus m greater than its threshold and coprime to its period. Apply it to the original arrangement at pq, the affine localizations at p and the central restrictions at q. Lemma 4.5 identifies the reduced centralization flats and restrictions. Use integral coordinates on the flats compatible with reduction. It suffices that coprime p and q each exceed the maximum of 1 and the applicable thresholds and each be coprime to the product of D, the applicable periods and the coordinate factors. These conditions also suffice at pq. Corollary 1.2 follows at these arguments by the cited evaluations. A Lean characteristic-polynomial evaluation remains open in this delivery.
- The paper already proves Corollary 1.2 algebraically. The result supplies the requested modular combinatorial interpretation with its good-reduction scope. Wang's distinct affine-flat CRT theorem retains its own indexing.

## ASSUMED-UNVERIFIED

Unindexed literature coverage remains unverified.
