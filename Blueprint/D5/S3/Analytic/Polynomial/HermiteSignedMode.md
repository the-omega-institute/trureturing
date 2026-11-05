# Signed coefficient modes of physicists Hermite polynomials

## Abstract

The smallest exponent with maximum signed physicists Hermite coefficient changes by one or minus three.

All indices are natural numbers, including zero. Polynomial coefficients are represented exactly in the rationals. The comparison uses signed coefficients. Subtraction in the conclusion occurs in the integers after both exponents are cast. The function coeff(H,j) extracts the coefficient of X to the power j. Natural subtraction truncates at zero; all mode indices below satisfy four times the index at most n.

**Definition 1.1 (Exact signed coefficient).**

$$\forall n:\mathbb{N}, \forall j:\mathbb{N}, \operatorname{signedCoeff}\left(n, j\right) = \operatorname{ite}\left((j \le n) \land (\operatorname{mod}\left((n-j), 2\right) = 0), \frac{(-1)^{\operatorname{div}\left((n-j), 2\right)} \cdot \operatorname{factorial}\left(n\right) \cdot 2^{j}}{\operatorname{factorial}\left(\operatorname{div}\left((n-j), 2\right)\right) \cdot \operatorname{factorial}\left(j\right)}, 0\right)$$

*Formalization.* `D5/S3/Analytic/Polynomial/HermiteSignedMode.signedCoeff` (`✓ std3`).

*Citation.* NIST Digital Library of Mathematical Functions (2010). *DLMF 18.5.13, explicit representation of Hermite polynomials*. URL: <https://dlmf.nist.gov/18.5.E13>.

*Commentary.*

For j at most n with n-j even, this is (-1) to the power (n-j)/2 times n! times 2 to the power j, divided by ((n-j)/2)! j!. Otherwise it is zero. div and mod are natural division and remainder. Factorials and powers in the quotient are cast to the rationals. This is the coefficient formula from DLMF 18.5.13, reindexed by exponent.

**Definition 1.2 (The physicists polynomial).**

$$\forall n:\mathbb{N}, \operatorname{physicistsHermite}\left(n\right) = \sum_{k\in\operatorname{range}\left(\operatorname{div}\left(n, 2\right)+1\right)}\operatorname{monomial}\left((n-2 \cdot k), \frac{(-1)^{k} \cdot \operatorname{factorial}\left(n\right) \cdot 2^{(n-2 \cdot k)}}{\operatorname{factorial}\left(k\right) \cdot \operatorname{factorial}\left((n-2 \cdot k)\right)}\right)$$

*Formalization.* `D5/S3/Analytic/Polynomial/HermiteSignedMode.physicistsHermite` (`✓ std3`).

*Citation.* NIST Digital Library of Mathematical Functions (2010). *DLMF 18.5.13, explicit representation of Hermite polynomials*. URL: <https://dlmf.nist.gov/18.5.E13>.

*Commentary.*

The sum runs over every k from zero through floor(n/2). monomial(j,c) denotes c times X to the power j. This is exactly DLMF 18.5.13 with n! distributed into the sum and (2X) to the power n-2k expanded. It defines the physicists normalization directly; it does not rescale a probabilists argmax. The coefficient extraction proof shows that every coefficient in the source range equals signedCoeff(n,j).

**Theorem 1.3 (Exact coefficient extraction).**

$$\forall n:\mathbb{N}, \forall j:\mathbb{N}, (j \le n) \implies (\operatorname{coeff}\left(\operatorname{physicistsHermite}\left(n\right), j\right) = \operatorname{signedCoeff}\left(n, j\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/HermiteSignedMode.polynomial_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2010). *DLMF 18.5.13, explicit representation of Hermite polynomials*. URL: <https://dlmf.nist.gov/18.5.E13>.

*Commentary.*

For every natural n and j with j at most n, the coefficient of X to the power j in the original physicists polynomial equals signedCoeff(n,j). This includes zero coefficients outside the parity support. The absolute-mode selector consumes this same extraction theorem; its statement and proof also serve the signed selector.

**Definition 1.4 (A certified smallest maximizing exponent).**

$$\forall n:\mathbb{N}, \operatorname{a}\left(n\right) = n-4 \cdot \operatorname{mode}\left(n\right)$$

*Formalization.* `D5/S3/Analytic/Polynomial/HermiteSignedMode.a` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mike Sheppard (2025). *OEIS A381423, exponent of the maximal signed Hermite coefficient*. URL: <https://oeis.org/A381423/internal>.

*Commentary.*

mode(n) is the largest r satisfying 4r at most n and 16(2r)(2r-1) at most (n-4r+1)(n-4r+2)(n-4r+3)(n-4r+4). The finite set contains zero. The theorem certifies that n-4mode(n) is exactly the smallest exponent maximizing the signed coefficient, so this constructive selector agrees with the source's upward scan and first maximum. No uniqueness hypothesis is used.

**Definition 1.5 (Signed maximum with the first-index tie rule).**

$$\forall n:\mathbb{N}, \forall j:\mathbb{N}, \operatorname{IsSmallestMax}\left(n, j\right) = ((j \le n) \land ((\forall k:\mathbb{N}, (k \le n) \implies (\operatorname{coeff}\left(\operatorname{physicistsHermite}\left(n\right), k\right) \le \operatorname{coeff}\left(\operatorname{physicistsHermite}\left(n\right), j\right))) \land (\forall k:\mathbb{N}, (k \le n) \implies ((\operatorname{coeff}\left(\operatorname{physicistsHermite}\left(n\right), k\right) = \operatorname{coeff}\left(\operatorname{physicistsHermite}\left(n\right), j\right)) \implies (j \le k)))))$$

*Formalization.* `D5/S3/Analytic/Polynomial/HermiteSignedMode.IsSmallestMax` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mike Sheppard (2025). *OEIS A381423, exponent of the maximal signed Hermite coefficient*. URL: <https://oeis.org/A381423/internal>.

*Commentary.*

The predicate requires membership in zero through n, maximality against every coefficient in that range, and that every tied maximizer has exponent at least j. The last condition handles all possible ties.

**Definition 1.6 (The independent OEIS difference assertion).**

$$claim = ((\forall n:\mathbb{N}, \operatorname{IsSmallestMax}\left(n, \operatorname{a}\left(n\right)\right)) \land (\forall n:\mathbb{N}, ((\operatorname{a}\left(n+1\right):\mathbb{Z})-(\operatorname{a}\left(n\right):\mathbb{Z}) = 1) \lor ((\operatorname{a}\left(n+1\right):\mathbb{Z})-(\operatorname{a}\left(n\right):\mathbb{Z}) = -3)))$$

*Formalization.* `D5/S3/Analytic/Polynomial/HermiteSignedMode.claim` (`✓ std3`).

*Citation.* Mike Sheppard (2025). *OEIS A381423, exponent of the maximal signed Hermite coefficient*. URL: <https://oeis.org/A381423/internal>.

*Commentary.*

OEIS A381423 revision 8 states: "Differences are either 1 or -3" as the first independent clause of its conjecture. The selector certificate is included explicitly, followed by the difference assertion for every natural n. Fine difference patterns, linearly or quadratically spaced positions, square-root growth and the separate uniqueness assertion remain outside this claim.

**Theorem 1.7 (The universal signed-mode transition).**

$$(\forall n:\mathbb{N}, \operatorname{IsSmallestMax}\left(n, \operatorname{a}\left(n\right)\right)) \land (\forall n:\mathbb{N}, ((\operatorname{a}\left(n+1\right):\mathbb{Z})-(\operatorname{a}\left(n\right):\mathbb{Z}) = 1) \lor ((\operatorname{a}\left(n+1\right):\mathbb{Z})-(\operatorname{a}\left(n\right):\mathbb{Z}) = -3))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/HermiteSignedMode.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a381423-hermite-differences` (proved) by `D5/S3/Analytic/Polynomial/HermiteSignedMode.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a381423-hermite-differences","declaration_gid":"D5/S3/Analytic/Polynomial/HermiteSignedMode.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mike Sheppard (2025). *OEIS A381423, exponent of the maximal signed Hermite coefficient*. URL: <https://oeis.org/A381423/internal>.

*Commentary.*

Write the positive coefficient at exponent n-4r as n! times w(n,r), where w(n,r)=2 to the power n-4r divided by (2r)! (n-4r)!. All coefficients outside this positive residue class are nonpositive. Successive positive weights obey w(n,r+1) times 16(2r+2)(2r+1) = w(n,r) times (n-4r)(n-4r-1)(n-4r-2)(n-4r-3). Thus the threshold predicate says precisely that the weight has not decreased from the previous index. Its true indices form an initial segment. Induction proves maximality at the largest true index and strict decrease past it; choosing that largest index gives the smallest exponent among ties. Increasing n preserves every true threshold; a true threshold at index r+1 for n+1 implies a true threshold at index r for n. Consequently mode(n+1) is mode(n) or mode(n)+1. The corresponding exponent difference is 1 or -3, with both exponents cast before subtraction. All factorial denominators are positive, and the proof covers the boundary indices without a cutoff. This is a repository derivation of the separate source assertion, with no global priority claim. The source-family audit observes the entire natural sequence, reconstructs this claim, rejects the constant-zero family, and proves actual dependence between indices zero and one. Its continuation is unknown.

## References

- Truth anchor: `D5/S3/Analytic/Polynomial/HermiteSignedMode.IsSmallestMax`
- Truth anchor: `D5/S3/Analytic/Polynomial/HermiteSignedMode.a`
- Truth anchor: `D5/S3/Analytic/Polynomial/HermiteSignedMode.claim`
- Truth anchor: `D5/S3/Analytic/Polynomial/HermiteSignedMode.physicistsHermite`
- Truth anchor: `D5/S3/Analytic/Polynomial/HermiteSignedMode.polynomial_coeff`
- Truth anchor: `D5/S3/Analytic/Polynomial/HermiteSignedMode.result`
- Truth anchor: `D5/S3/Analytic/Polynomial/HermiteSignedMode.signedCoeff`
