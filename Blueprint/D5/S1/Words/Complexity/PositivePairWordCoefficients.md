# Actual Positive-Pair Magnus Coefficients

## Abstract

Actual Magnus polynomials turn the full recursive positive-pair family into filtered coefficient differences whose first live term is a Lyndon-bracket direction.

Magnus expansions and shuffle or infiltration identities are classical context, but the complete recursively indexed positive-pair construction below is a repository route. Indices are retained even when two evaluated pairs coincide.

**Definition 1.1 (Rational word algebra).**

$$RationalWordPolynomial$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairWordCoefficients.RationalWordPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

RationalWordPolynomial A abbreviates MonoidAlgebra Q (FreeMonoid A).

**Definition 1.2 (Extend integer coefficients to rationals).**

$$toRationalWordPolynomial$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairWordCoefficients.toRationalWordPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

This ring homomorphism maps the integral WordPolynomial coefficients through Int.castRingHom Q while retaining every word monomial.

**Definition 1.3 (Words through a cutoff degree).**

$$CutoffWord$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairWordCoefficients.CutoffWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

CutoffWord A r is the subtype of free words whose length is at most r.

**Definition 1.4 (Finite cutoff coefficient vectors).**

$$CutoffCoefficients$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairWordCoefficients.CutoffCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

CutoffCoefficients A r is the function space CutoffWord A r -> Q.

**Definition 1.5 (Restrict a polynomial to bounded words).**

$$cutoffRestriction$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairWordCoefficients.cutoffRestriction` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

cutoffRestriction r p evaluates the coefficient of p at each free word of length at most r.

**Definition 1.6 (Lift bounded coefficients by zero).**

$$cutoffLift$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairWordCoefficients.cutoffLift` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For finite A, cutoffLift r extends a CutoffCoefficients vector to the full rational word algebra and assigns zero outside the cutoff subtype.

**Definition 1.7 (Split convolution in the cutoff algebra).**

$$cutoffMul$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairWordCoefficients.cutoffMul` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

cutoffMul r p q at a target word sums p(prefix)*q(suffix) over every cut from zero through the target length.

**Definition 1.8 (The empty-word unit vector).**

$$cutoffOne$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairWordCoefficients.cutoffOne` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

cutoffOne r is the restriction of the multiplicative unit of the rational word algebra.

**Theorem 1.9 (Restriction preserves multiplication).**

$$cutoffRestrictionmul$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairWordCoefficients.cutoffRestriction_mul` (`✓ std3`). ∎

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For every cutoff r and rational word polynomials p,q, restriction of p*q equals cutoffMul r of their restrictions.

**Definition 1.10 (Filtration vanishing).**

$$VanishesBelow$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairWordCoefficients.VanishesBelow` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

VanishesBelow r d p means p is zero on every cutoff word of length strictly below d.

**Theorem 1.11 (Filtration degrees add).**

$$cutoffMulvanishesBelow$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairWordCoefficients.cutoffMul_vanishesBelow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

If p vanishes below d and q below e, their cutoff product vanishes below d+e.

**Definition 1.12 (Powers inside the cutoff algebra).**

$$cutoffPow$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairWordCoefficients.cutoffPow` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

cutoffPow r p 0=cutoffOne r and cutoffPow r p (n+1)=cutoffMul r p (cutoffPow r p n).

**Theorem 1.13 (Cutoff powers are genuine restrictions).**

$$cutoffPoweqrestrictionpow$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairWordCoefficients.cutoffPow_eq_restriction_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For finite A and every n, cutoffPow r p n equals cutoffRestriction r of (cutoffLift r p)^n.

**Theorem 1.14 (Positive degree accumulates).**

$$cutoffPowvanishesBelow$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairWordCoefficients.cutoffPow_vanishesBelow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

If p vanishes below degree one, then its nth cutoff power vanishes below degree n.

**Definition 1.15 (Finite geometric inverse).**

$$cutoffGeometricInverse$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairWordCoefficients.cutoffGeometricInverse` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For finite A, cutoffGeometricInverse r c restricts the finite sum of powers of cutoffLift r (-c) from zero through r.

**Theorem 1.16 (Right inverse of one plus a tail).**

$$cutoffMulgeometricInverse$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairWordCoefficients.cutoffMul_geometricInverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

If c vanishes below degree one, cutoffMul r (cutoffOne r+c) (cutoffGeometricInverse r c)=cutoffOne r.

**Theorem 1.17 (Left inverse of one plus a tail).**

$$geometricInversecutoffMul$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairWordCoefficients.geometricInverse_cutoffMul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

Under the same positive-degree hypothesis, the same finite geometric series is also a left inverse.

**Definition 1.18 (Actual positive-word Magnus polynomial).**

$$magnusPolynomial$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairWordCoefficients.magnusPolynomial` (`✓ std3`).

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

magnusPolynomial []=1 and magnusPolynomial (a::w)=(1+X_a)*magnusPolynomial w, preserving source order.

**Theorem 1.19 (Magnus is multiplicative on concatenation).**

$$magnusPolynomialappend$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairWordCoefficients.magnusPolynomial_append` (`✓ std3`). ∎

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For all finite words left,right, the Magnus polynomial of left++right is the product of their Magnus polynomials.

**Theorem 1.20 (Magnus coefficients are scattered counts).**

$$magnusPolynomialcoeffscatteredCount$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairWordCoefficients.magnusPolynomial_coeff_scatteredCount` (`✓ std3`). ∎

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

With decidable equality on A, the coefficient at pattern in magnusPolynomial source is exactly the natural scatteredCount pattern source, cast to Z.

**Definition 1.21 (Degree-one letter sum).**

$$wordAbelianization$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairWordCoefficients.wordAbelianization` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

wordAbelianization recursively sums the singleton wordMonomial for each source letter and maps the empty word to zero.

**Theorem 1.22 (Abelianization is additive).**

$$wordAbelianizationappend$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairWordCoefficients.wordAbelianization_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

wordAbelianization (left++right) is the sum of the two word abelianizations.

**Theorem 1.23 (Singleton coefficients count letters).**

$$wordAbelianizationcoeffsingleton$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairWordCoefficients.wordAbelianization_coeff_singleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

With decidable equality, the coefficient of [b] in wordAbelianization source is scatteredCount [b] source, cast to Z.

**Theorem 1.24 (No empty coefficient).**

$$wordAbelianizationcoeffempty$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairWordCoefficients.wordAbelianization_coeff_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For every source, wordAbelianization source has coefficient zero at the empty free word.

**Definition 1.25 (Full recursive choice index).**

$$PositivePairIndex$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairWordCoefficients.PositivePairIndex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

PositivePairIndex A r abbreviates Fin r -> A. Distinct indices remain distinct even if their evaluated word pairs coincide.

**Definition 1.26 (Actual recursive positive pairs).**

$$positivePairWords$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairWordCoefficients.positivePairWords` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

Level zero is ([],[]), level one is ([a],[]), and a successor step sends (u,v) and a to (u++[a]++v, v++[a]++u).

**Definition 1.27 (Actual Magnus cutoff).**

$$cutoffMagnus$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairWordCoefficients.cutoffMagnus` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For finite A, cutoffMagnus r source is the rational coefficient extension of the actual Magnus polynomial restricted through degree r.

**Definition 1.28 (Actual positive-pair Magnus ratio).**

$$positivePairRatio$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairWordCoefficients.positivePairRatio` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For independent cutoff and level parameters, positivePairRatio is cutoffMagnus(u) multiplied by the finite geometric inverse of cutoffMagnus(v)-1 for the actual pair (u,v).

**Theorem 1.29 (Full indexed family agrees below its level).**

$$fullpositivePairratiofiltration$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairWordCoefficients.full_positivePair_ratio_filtration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For every finite alphabet, cutoff, level r, and full PositivePairIndex, both the actual cutoff-Magnus difference M(u)-M(v) and the ratio minus one vanish below r. Duplicate pairs and zero leading directions remain in the quantified family.

**Theorem 1.30 (Successor difference is a commutator).**

$$fullpositivePairsuccessorleadingbracket$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairWordCoefficients.full_positivePair_successor_leading_bracket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For finite A with decidable equality and index at level r+2, let c be the preceding actual cutoff-Magnus difference and x the rationalized abelianization of the previous right word plus X_a. The successor Magnus difference equals cutoffMul c x - cutoffMul x c in cutoff r+2.

**Theorem 1.31 (The ratio has the same leading commutator).**

$$fullpositivePairsuccessorratioleadingbracket$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairWordCoefficients.full_positivePair_successor_ratio_leading_bracket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

Under the same hypotheses and definitions, positivePairRatio at level and cutoff r+2 minus cutoffOne equals cutoffMul c x - cutoffMul x c.

**Theorem 1.32 (Actual coefficient checkpoint).**

$$fullpositivePaircoefficientcheckpoint$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairWordCoefficients.full_positivePair_coefficient_checkpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For every finite alphabet with decidable equality, level r, and full index: when 2<=r both actual pair words are nonempty and equally long; for every cutoff word, the rational Magnus-difference coefficient is exactly the difference of the two frozen scattered counts.

## References

- Truth anchor: `D5/S1/Words/Complexity/PositivePairWordCoefficients.CutoffCoefficients`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairWordCoefficients.CutoffWord`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairWordCoefficients.PositivePairIndex`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairWordCoefficients.RationalWordPolynomial`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairWordCoefficients.VanishesBelow`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairWordCoefficients.cutoffGeometricInverse`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairWordCoefficients.cutoffLift`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairWordCoefficients.cutoffMagnus`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairWordCoefficients.cutoffMul`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairWordCoefficients.cutoffMul_geometricInverse`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairWordCoefficients.cutoffMul_vanishesBelow`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairWordCoefficients.cutoffOne`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairWordCoefficients.cutoffPow`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairWordCoefficients.cutoffPow_eq_restriction_pow`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairWordCoefficients.cutoffPow_vanishesBelow`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairWordCoefficients.cutoffRestriction`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairWordCoefficients.cutoffRestriction_mul`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairWordCoefficients.full_positivePair_coefficient_checkpoint`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairWordCoefficients.full_positivePair_ratio_filtration`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairWordCoefficients.full_positivePair_successor_leading_bracket`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairWordCoefficients.full_positivePair_successor_ratio_leading_bracket`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairWordCoefficients.geometricInverse_cutoffMul`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairWordCoefficients.magnusPolynomial`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairWordCoefficients.magnusPolynomial_append`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairWordCoefficients.magnusPolynomial_coeff_scatteredCount`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairWordCoefficients.positivePairRatio`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairWordCoefficients.positivePairWords`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairWordCoefficients.toRationalWordPolynomial`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairWordCoefficients.wordAbelianization`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairWordCoefficients.wordAbelianization_append`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairWordCoefficients.wordAbelianization_coeff_empty`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairWordCoefficients.wordAbelianization_coeff_singleton`
- Dependency: [D5/S1/Words/Complexity/LyndonStandardBracket](LyndonStandardBracket.md)
- Dependency: [D5/S1/Words/Complexity/VivionBinomialConverseFails](VivionBinomialConverseFails.md)
