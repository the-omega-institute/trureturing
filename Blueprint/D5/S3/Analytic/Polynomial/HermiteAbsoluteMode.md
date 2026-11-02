# Absolute coefficient modes of physicists Hermite polynomials

## Abstract

The smallest exponent of a largest absolute physicists Hermite coefficient changes by one or minus one.

All orders and exponents are natural numbers, including zero. The polynomial physicistsHermite and its exact signedCoeff supplier are the original HermiteSignedMode declarations. Coefficients are rational, and absolute value is taken before comparing them. No rescaling or restriction to positive coefficients is made. Both exponents are cast to the integers before the subtraction in the transition statement.

The comparison functions are second(j)=(j+1)(j+2), rises(n,r) meaning 2r at most n and 4r at most second(n-2r), and mode(n), the largest rising index. mode_rises asserts the threshold at mode(n), le_mode bounds every rising index by mode(n), and second_mono states monotonicity of second. The weight is the absolute original signedCoeff at n-2r. weight_pos asserts positivity on 2r at most n, and adjacent gives its successive cross-product identity. weight_le_mode bounds every supported weight by the mode weight; weight_lt_mode makes this bound strict beyond the mode. coefficient_cases says that each original absolute signed coefficient is zero or is a supported weight.

**Definition 1.1 (The smallest absolute-coefficient mode).**

$$\forall n:\mathbb{N}, \operatorname{b}\left(n\right) = n-2 \cdot \operatorname{mode}\left(n\right)$$

*Formalization.* `D5/S3/Analytic/Polynomial/HermiteAbsoluteMode.b` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mike Sheppard (2025). *OEIS A381524, smallest exponent of a maximal absolute Hermite coefficient*. URL: <https://oeis.org/A381524/internal?rev=18>.

*Commentary.*

Let rises(n,r) mean 2r at most n and 4r at most (n-2r+1)(n-2r+2). mode(n) is the largest r in range(n+1) satisfying rises(n,r); zero always belongs. The selector is n-2mode(n). Equality in the threshold is included, so a tied maximum chooses the larger r and therefore the smaller exponent. The selector theorem verifies this construction against the original polynomial.

**Definition 1.2 (Full absolute maximum with the first-index tie rule).**

$$\forall n:\mathbb{N}, \forall j:\mathbb{N}, \operatorname{IsSmallestAbsMax}\left(n, j\right) = ((j \le n) \land ((\forall k:\mathbb{N}, (k \le n) \implies (\operatorname{abs}\left(\operatorname{coeff}\left(\operatorname{physicistsHermite}\left(n\right), k\right)\right) \le \operatorname{abs}\left(\operatorname{coeff}\left(\operatorname{physicistsHermite}\left(n\right), j\right)\right))) \land (\forall k:\mathbb{N}, (k \le n) \implies ((\operatorname{abs}\left(\operatorname{coeff}\left(\operatorname{physicistsHermite}\left(n\right), k\right)\right) = \operatorname{abs}\left(\operatorname{coeff}\left(\operatorname{physicistsHermite}\left(n\right), j\right)\right)) \implies (j \le k)))))$$

*Formalization.* `D5/S3/Analytic/Polynomial/HermiteAbsoluteMode.IsSmallestAbsMax` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mike Sheppard (2025). *OEIS A381524, smallest exponent of a maximal absolute Hermite coefficient*. URL: <https://oeis.org/A381524/internal?rev=18>.

*Commentary.*

The predicate requires j at most n, maximal absolute coefficient against every exponent from zero through n, and j at most every other exponent with equal absolute coefficient. Thus parity zeros and all ties remain in scope.

**Definition 1.3 (The complete OEIS adjacent-difference assertion).**

$$claim = ((\forall n:\mathbb{N}, \operatorname{IsSmallestAbsMax}\left(n, \operatorname{b}\left(n\right)\right)) \land (\forall n:\mathbb{N}, ((\operatorname{b}\left(n+1\right):\mathbb{Z})-(\operatorname{b}\left(n\right):\mathbb{Z}) = 1) \lor ((\operatorname{b}\left(n+1\right):\mathbb{Z})-(\operatorname{b}\left(n\right):\mathbb{Z}) = -1)))$$

*Formalization.* `D5/S3/Analytic/Polynomial/HermiteAbsoluteMode.claim` (`✓ std3`).

*Citation.* Mike Sheppard (2025). *OEIS A381524, smallest exponent of a maximal absolute Hermite coefficient*. URL: <https://oeis.org/A381524/internal?rev=18>.

*Commentary.*

OEIS A381524 revision 18 defines the smallest exponent of a maximal coefficient ignoring signs and conjectures: Differences are either +1 or -1. This claim includes the exact selector certificate for all natural orders, followed by that entire adjacent-difference assertion. It assumes neither uniqueness nor an asymptotic cutoff.

**Theorem 1.4 (The universal absolute-mode transition).**

$$(\forall n:\mathbb{N}, \operatorname{IsSmallestAbsMax}\left(n, \operatorname{b}\left(n\right)\right)) \land (\forall n:\mathbb{N}, ((\operatorname{b}\left(n+1\right):\mathbb{Z})-(\operatorname{b}\left(n\right):\mathbb{Z}) = 1) \lor ((\operatorname{b}\left(n+1\right):\mathbb{Z})-(\operatorname{b}\left(n\right):\mathbb{Z}) = -1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/HermiteAbsoluteMode.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a381524-hermite-absolute-differences` (proved) by `D5/S3/Analytic/Polynomial/HermiteAbsoluteMode.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a381524-hermite-absolute-differences","declaration_gid":"D5/S3/Analytic/Polynomial/HermiteAbsoluteMode.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mike Sheppard (2025). *OEIS A381524, smallest exponent of a maximal absolute Hermite coefficient*. URL: <https://oeis.org/A381524/internal?rev=18>.

*Commentary.*

Write w(n,r) for the absolute value of the original signedCoeff at exponent n-2r. The original polynomial_coeff theorem connects these values to the polynomial. On 2r at most n they are positive; all other parity coefficients are zero. For 2(r+1) at most n, successive weights satisfy w(n,r+1) times 4(r+1) = w(n,r) times (n-2r-1)(n-2r). Consequently rises(n,r+1) is exactly the nondecrease test. The true thresholds form an initial segment. Induction proves maximality at its last index and strict decrease beyond it, which supplies the smallest-exponent tie rule. Every true threshold persists when n increases by one; a true threshold at (n+1,r+1) implies a true threshold at (n,r). Hence mode(n+1) is mode(n) or mode(n)+1, and the exponent changes by +1 or -1. The argument includes order zero. It applies to the complete natural selector sequence, preserving parity zeros, all ties, and the stated first-index convention. The result is derived from the displayed coefficient identities and makes no uniqueness or asymptotic assumption.

## References

- Truth anchor: `D5/S3/Analytic/Polynomial/HermiteAbsoluteMode.IsSmallestAbsMax`
- Truth anchor: `D5/S3/Analytic/Polynomial/HermiteAbsoluteMode.b`
- Truth anchor: `D5/S3/Analytic/Polynomial/HermiteAbsoluteMode.claim`
- Truth anchor: `D5/S3/Analytic/Polynomial/HermiteAbsoluteMode.result`
- Dependency: [D5/S3/Analytic/Polynomial/HermiteSignedMode](HermiteSignedMode.md)
