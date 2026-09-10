# Hanna's Cubed Binary Product Conjecture

## Abstract

The coefficients of OEIS A373308 at indices 3n+1 and 3n+2 are divisible by three.

The entry cited in hanna2024a373308 defines the sequence by the expansion of Product_{n>=0} (1-x^(2^n))^3. Here the infinite product is represented by its exact defining functional equation A(x) = (1-x)^3 A(x^2), with constant coefficient one. Removing the first factor and shifting the remaining factors gives this characterization. The existence and uniqueness theorems below establish that characterization for the recursively constructed series; no infinite-product operator is used.

All indices are natural numbers, and a takes integer values. PowerSeries(Z) denotes the formal power-series ring with indeterminate X. The notation coeff(i,f) extracts coefficient i, mk constructs a series from its coefficient function, and subst(f,g) substitutes g into f. Index subtraction is natural subtraction and div is natural-number integer division. The finite sum ranges over i in range(n+2). The cast in the support theorem is the integer cast into ZMod(3).

**Definition 1.1 (The recursive integer coefficients).**

$$\begin{aligned}\operatorname{a}: \mathbb{N} \to \mathbb{Z}\\\operatorname{a}\left(0\right) = 1\\\forall n: \mathbb{N}, \operatorname{a}\left(n + 1\right) = \sum_{i \in \operatorname{range}\left(n + 2\right)} (\operatorname{coeff}\left(i, (1 - X)^{3}\right) \cdot (\operatorname{if} (2 \mid (n + 1 - i)) \operatorname{then} \operatorname{a}\left(\operatorname{div}\left((n + 1 - i), 2\right)\right) \operatorname{else} 0))\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Invariants/CubedBinaryProductModThree.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The convolution with (1-X)^3 defines each successor coefficient using only earlier coefficients. Substitution by X^2 selects even indices. The polynomial coefficient is zero beyond degree three, so this is the coefficient recurrence of the defining product equation.

**Definition 1.2 (The generating series).**

$$\operatorname{generatingSeries}: \operatorname{PowerSeries}\left(\mathbb{Z}\right) = \operatorname{mk}\left(\operatorname{a}\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/CubedBinaryProductModThree.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The series has coefficient function a and integer coefficients.

**Theorem 1.3 (The defining functional equation).**

$$(\operatorname{constantCoeff}\left(\operatorname{generatingSeries}\right) = 1) \land (\operatorname{generatingSeries} = (1 - X)^{3} \cdot \operatorname{subst}\left(\operatorname{generatingSeries}, (X)^{2}\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CubedBinaryProductModThree.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At degree zero the constant coefficient is one. At every positive degree, the product coefficient formula and the coefficient formula for substitution by X^2 reproduce exactly the recursive definition.

**Theorem 1.4 (Uniqueness of the normalized solution).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(B\right) = 1) \implies (B = (1 - X)^{3} \cdot \operatorname{subst}\left(B, (X)^{2}\right)) \implies B = \operatorname{generatingSeries}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CubedBinaryProductModThree.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strong induction compares the coefficients of any normalized solution with the constructed series. Every coefficient used at a positive degree has index at most half that degree and is therefore already equal.

**Theorem 1.5 (Support modulo three).**

$$\forall n: \mathbb{N}, (\neg (3 \mid n)) \implies \operatorname{cast}\left(\operatorname{a}\left(n\right), \operatorname{ZMod}\left(3\right)\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CubedBinaryProductModThree.mod_three_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Map the generating equation to ZMod(3). Frobenius gives (1-X)^3 = 1-X^3. In the resulting equation, coefficient n depends only on n/2 when n is even, and on (n-3)/2 when n is at least three and n-3 is even. If three does not divide n, each contributing predecessor is smaller and is also not divisible by three. Strong induction makes both contributions zero.

**Theorem 1.6 (The A373308 divisibility conjecture).**

$$\forall n: \mathbb{N}, (3 \mid \operatorname{a}\left(3 \cdot n + 1\right)) \land (3 \mid \operatorname{a}\left(3 \cdot n + 2\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CubedBinaryProductModThree.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a373308-cubed-binary-product-mod-three` (proved) by `D5/S1/Recurrence/Invariants/CubedBinaryProductModThree.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a373308-cubed-binary-product-mod-three","declaration_gid":"D5/S1/Recurrence/Invariants/CubedBinaryProductModThree.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2024). *OEIS A373308, expansion of Product_{n>=0} (1 - x^(2^n))^3*. URL: <https://oeis.org/A373308>.

*Commentary.*

Neither 3n+1 nor 3n+2 is divisible by three. The support theorem makes both integer coefficients zero in ZMod(3), which is equivalent to integer divisibility by three. The conjecture is the one quoted in hanna2024a373308.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/CubedBinaryProductModThree.a`
- Truth anchor: `D5/S1/Recurrence/Invariants/CubedBinaryProductModThree.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/CubedBinaryProductModThree.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Invariants/CubedBinaryProductModThree.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Invariants/CubedBinaryProductModThree.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Invariants/CubedBinaryProductModThree.mod_three_support`
