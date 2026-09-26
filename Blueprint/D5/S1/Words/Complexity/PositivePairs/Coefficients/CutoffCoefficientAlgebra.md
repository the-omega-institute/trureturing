# CutoffCoefficientAlgebra

## Abstract

Finite cutoff word coefficients form a truncated multiplicative algebra.

Magnus expansions and shuffle or infiltration identities are classical context, but the complete recursively indexed positive-pair construction below is a repository route. Indices are retained even when two evaluated pairs coincide.

**Definition 1.1 (Rational word algebra).**

$$\operatorname{RationalWordPolynomial}\left(A\right) = \operatorname{MonoidAlgebra}\left(Q, \operatorname{FreeMonoid}\left(A\right)\right)$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra.RationalWordPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

RationalWordPolynomial A abbreviates MonoidAlgebra Q (FreeMonoid A).

**Definition 1.2 (Extend integer coefficients to rationals).**

$$\forall p,\operatorname{toRationalWordPolynomial}\left(p\right) = \operatorname{mapCoefficients}\left(castZQ, p\right)$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra.toRationalWordPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

This ring homomorphism maps the integral WordPolynomial coefficients through Int.castRingHom Q while retaining every word monomial.

**Definition 1.3 (Words through a cutoff degree).**

$$\forall A,r,\operatorname{CutoffWord}\left(A, r\right) = \operatorname{subtype}\left(w, \operatorname{length}\left(w\right)\leq r\right)$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra.CutoffWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

CutoffWord A r is the subtype of free words whose length is at most r.

**Definition 1.4 (Finite cutoff coefficient vectors).**

$$\forall A,r,\operatorname{CutoffCoefficients}\left(A, r\right) = \operatorname{functions}\left(\operatorname{CutoffWord}\left(A, r\right), Q\right)$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra.CutoffCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

CutoffCoefficients A r is the function space CutoffWord A r -> Q.

**Definition 1.5 (Restrict a polynomial to bounded words).**

$$\forall r,p,w,\operatorname{length}\left(w\right)\leq r\Rightarrow\operatorname{cutoffRestriction}\left(r, p, w\right) = \operatorname{coeff}\left(p, w\right)$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra.cutoffRestriction` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

cutoffRestriction r p evaluates the coefficient of p at each free word of length at most r.

**Definition 1.6 (Lift bounded coefficients by zero).**

$$\forall r,p,w,\operatorname{coeff}\left(\operatorname{cutoffLift}\left(r, p\right), w\right) = \operatorname{ifThenElse}\left(\operatorname{length}\left(w\right)\leq r, \operatorname{apply}\left(p, w\right), 0\right)$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra.cutoffLift` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For finite A, cutoffLift r extends a CutoffCoefficients vector to the full rational word algebra and assigns zero outside the cutoff subtype.

**Definition 1.7 (Split convolution in the cutoff algebra).**

$$\forall r,p,q,w,\operatorname{cutoffMul}\left(r, p, q, w\right) = \operatorname{sum}\left(\operatorname{range}\left(\operatorname{length}\left(w\right) + 1\right), \operatorname{lambda}\left(i, \operatorname{apply}\left(p, \operatorname{take}\left(w, i\right)\right) \cdot \operatorname{apply}\left(q, \operatorname{drop}\left(w, i\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra.cutoffMul` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

cutoffMul r p q at a target word sums p(prefix)*q(suffix) over every cut from zero through the target length.

**Definition 1.8 (The empty-word unit vector).**

$$\forall r,\operatorname{cutoffOne}\left(r\right) = \operatorname{cutoffRestriction}\left(r, 1\right)$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra.cutoffOne` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

cutoffOne r is the restriction of the multiplicative unit of the rational word algebra.

**Theorem 1.9 (Restriction preserves multiplication).**

$$\forall r,p,q,\operatorname{cutoffRestriction}\left(r, p \cdot q\right) = \operatorname{cutoffMul}\left(r, \operatorname{cutoffRestriction}\left(r, p\right), \operatorname{cutoffRestriction}\left(r, q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra.cutoffRestriction_mul` (`✓ std3`). ∎

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For every cutoff r and rational word polynomials p,q, restriction of p*q equals cutoffMul r of their restrictions.

**Definition 1.10 (Filtration vanishing).**

$$\forall r,d,p,\operatorname{VanishesBelow}\left(r, d, p\right)\iff\forall w\in\operatorname{CutoffWord}\left(A, r\right),\operatorname{length}\left(w\right)< d\Rightarrow\operatorname{apply}\left(p, w\right) = 0$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra.VanishesBelow` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

VanishesBelow r d p means p is zero on every cutoff word of length strictly below d.

**Theorem 1.11 (Filtration degrees add).**

$$\forall r,d,e,p,q,\operatorname{VanishesBelow}\left(r, d, p\right)\land\operatorname{VanishesBelow}\left(r, e, q\right)\Rightarrow\operatorname{VanishesBelow}\left(r, d + e, \operatorname{cutoffMul}\left(r, p, q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra.cutoffMul_vanishesBelow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

If p vanishes below d and q below e, their cutoff product vanishes below d+e.

**Definition 1.12 (Powers inside the cutoff algebra).**

$$\forall r,p,n,\operatorname{cutoffPow}\left(r, p, 0\right) = \operatorname{cutoffOne}\left(r\right)\land\operatorname{cutoffPow}\left(r, p, n + 1\right) = \operatorname{cutoffMul}\left(r, p, \operatorname{cutoffPow}\left(r, p, n\right)\right)$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra.cutoffPow` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

cutoffPow r p 0=cutoffOne r and cutoffPow r p (n+1)=cutoffMul r p (cutoffPow r p n).

**Theorem 1.13 (Cutoff powers are genuine restrictions).**

$$\forall r,p,n,\operatorname{cutoffPow}\left(r, p, n\right) = \operatorname{cutoffRestriction}\left(r, \operatorname{pow}\left(\operatorname{cutoffLift}\left(r, p\right), n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra.cutoffPow_eq_restriction_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For finite A and every n, cutoffPow r p n equals cutoffRestriction r of (cutoffLift r p)^n.

**Theorem 1.14 (Positive degree accumulates).**

$$\forall r,p,n,\operatorname{VanishesBelow}\left(r, 1, p\right)\Rightarrow\operatorname{VanishesBelow}\left(r, n, \operatorname{cutoffPow}\left(r, p, n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra.cutoffPow_vanishesBelow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

If p vanishes below degree one, then its nth cutoff power vanishes below degree n.

**Definition 1.15 (Finite geometric inverse).**

$$\forall r,c,\operatorname{cutoffGeometricInverse}\left(r, c\right) = \operatorname{cutoffRestriction}\left(r, \operatorname{sum}\left(\operatorname{range}\left(r + 1\right), \operatorname{lambda}\left(i, \operatorname{pow}\left(\operatorname{cutoffLift}\left(r, 0 - c\right), i\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra.cutoffGeometricInverse` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For finite A, cutoffGeometricInverse r c restricts the finite sum of powers of cutoffLift r (-c) from zero through r.

**Theorem 1.16 (Right inverse of one plus a tail).**

$$\forall r,c,\operatorname{VanishesBelow}\left(r, 1, c\right)\Rightarrow\operatorname{cutoffMul}\left(r, \operatorname{cutoffOne}\left(r\right) + c, \operatorname{cutoffGeometricInverse}\left(r, c\right)\right) = \operatorname{cutoffOne}\left(r\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra.cutoffMul_geometricInverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

If c vanishes below degree one, cutoffMul r (cutoffOne r+c) (cutoffGeometricInverse r c)=cutoffOne r.

**Theorem 1.17 (Left inverse of one plus a tail).**

$$\forall r,c,\operatorname{VanishesBelow}\left(r, 1, c\right)\Rightarrow\operatorname{cutoffMul}\left(r, \operatorname{cutoffGeometricInverse}\left(r, c\right), \operatorname{cutoffOne}\left(r\right) + c\right) = \operatorname{cutoffOne}\left(r\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra.geometricInverse_cutoffMul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

Under the same positive-degree hypothesis, the same finite geometric series is also a left inverse.

## References

- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra.CutoffCoefficients`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra.CutoffWord`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra.RationalWordPolynomial`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra.VanishesBelow`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra.cutoffGeometricInverse`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra.cutoffLift`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra.cutoffMul`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra.cutoffMul_geometricInverse`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra.cutoffMul_vanishesBelow`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra.cutoffOne`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra.cutoffPow`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra.cutoffPow_eq_restriction_pow`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra.cutoffPow_vanishesBelow`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra.cutoffRestriction`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra.cutoffRestriction_mul`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra.geometricInverse_cutoffMul`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra.toRationalWordPolynomial`
- Dependency: [D5/S1/Words/Complexity/LyndonBrackets/LyndonBracketAlgebra](../../LyndonBrackets/LyndonBracketAlgebra.md)
- Dependency: [D5/S1/Words/Complexity/VivionBinomialConverseFails](../../VivionBinomialConverseFails.md)
