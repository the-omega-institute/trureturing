# Hanna's Square-Cube Substitution Conjecture

## Abstract

The normalized coefficients of OEIS A389536 are two modulo four exactly at powers of two plus one.

The entry cited in hanna2025a389536 defines A(x) by A(x)=A(x^2+2x^3)/x and conjectures its coefficient pattern modulo four. We use the equivalent formal power-series identity xA(x)=A(x^2+2x^3), with zero constant term and a(1)=1. Comparing degree two gives a(1)=a(1), so the first coefficient is a free normalization.

All indices and exponents are natural numbers. Fin(n) consists of the indices k with 0<=k<n; its elements are read as natural numbers in coefficients and exponents. Subtraction in indices is natural subtraction. The values of a and the displayed binomial coefficients in products are integers. PowerSeries(Z) is the formal power-series ring with indeterminate X. The notation subst(B,Q) means B composed with Q, coeff(n,B) is coefficient n, and mk(a) constructs the series with coefficient function a. Remainders in the final theorem are integer remainders.

**Definition 1.1 (The normalized coefficient sequence).**

$$\begin{aligned}\operatorname{a}: \mathbb{N} \to \mathbb{Z}\\\operatorname{a}\left(0\right) = 0\\\operatorname{a}\left(1\right) = 1\\\forall n: \mathbb{N}, \operatorname{a}\left(n + 2\right) = \sum_{k: \operatorname{Fin}\left(n + 2\right)} (\operatorname{a}\left(k\right) \cdot \operatorname{coeff}\left(n + 3, (X^{2} + 2 \cdot X^{3})^{k}\right))\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Invariants/SubstitutionSquareCubeModFour.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The recursion only uses indices smaller than n+2 and therefore defines an integer sequence without assuming existence of a solution to the equation.

**Definition 1.2 (The generating series).**

$$\operatorname{generatingSeries}: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{generatingSeries} = \operatorname{mk}\left(\operatorname{a}\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/SubstitutionSquareCubeModFour.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient of index n in generatingSeries is a(n).

**Theorem 1.3 (The normalized functional equation).**

$$(\operatorname{constantCoeff}\left(\operatorname{generatingSeries}\right) = 0) \land ((\operatorname{coeff}\left(1, \operatorname{generatingSeries}\right) = 1) \land (X \cdot \operatorname{generatingSeries} = \operatorname{subst}\left(\operatorname{generatingSeries}, X^{2} + 2 \cdot X^{3}\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/SubstitutionSquareCubeModFour.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The kth power of X^2+2X^3 has no coefficients below degree 2k. Consequently each substituted coefficient is a finite sum, and the defining recursion gives the equation coefficient by coefficient. The constant and linear coefficients supply the two normalizations.

**Theorem 1.4 (Uniqueness of the normalized solution).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(B\right) = 0) \implies (\operatorname{coeff}\left(1, B\right) = 1) \implies (X \cdot B = \operatorname{subst}\left(B, X^{2} + 2 \cdot X^{3}\right)) \implies B = \operatorname{generatingSeries}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/SubstitutionSquareCubeModFour.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n at least two, coefficient n+1 of the equation determines coefficient n using only smaller indices. Strong induction, with the prescribed constant and linear coefficients as initial cases, proves uniqueness.

**Theorem 1.5 (The binomial coefficient bridge).**

$$\forall n: \mathbb{N}, (2 \le n) \implies \operatorname{a}\left(n\right) = \sum_{k: \operatorname{Fin}\left(n\right)} (\operatorname{if} (2 \cdot k \le n + 1) \operatorname{then} \operatorname{a}\left(k\right) \cdot 2^{n + 1 - 2 \cdot k} \cdot \operatorname{choose}\left(k, n + 1 - 2 \cdot k\right) \operatorname{else} 0)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/SubstitutionSquareCubeModFour.coeff_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Extract coefficient n+1 from the proved generating equation. Factor the kth substituted power as X^(2k)(1+2X)^k and apply the binomial coefficient formula. The inequality in the summand excludes degrees below 2k.

**Theorem 1.6 (Evenness beyond the normalized term).**

$$\forall n: \mathbb{N}, (2 \le n) \implies 2 \mid \operatorname{a}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/SubstitutionSquareCubeModFour.a_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Modulo four only exponents zero and one in the binomial expansion survive. Thus a(2m-1) is congruent to a(m) for m>=2, and a(2m) is congruent to 2m a(m) for m>=1. Reducing these relations modulo two and applying strong induction proves evenness for every index at least two.

**Theorem 1.7 (The complete A389536 conjecture).**

$$\forall n: \mathbb{N}, (1 < n) \implies ((\operatorname{a}\left(n\right) \bmod 4 = 2) \iff (\exists k: \mathbb{N}, n = 2^{k} + 1)) \land ((\operatorname{a}\left(n\right) \bmod 4 = 0) \iff \neg (\exists k: \mathbb{N}, n = 2^{k} + 1))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/SubstitutionSquareCubeModFour.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a389536-substitution-square-cube-mod-four` (proved) by `D5/S1/Recurrence/Invariants/SubstitutionSquareCubeModFour.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a389536-substitution-square-cube-mod-four","declaration_gid":"D5/S1/Recurrence/Invariants/SubstitutionSquareCubeModFour.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2025). *OEIS A389536, G.f. A(x) = A(x^2 + 2*x^3)/x*. URL: <https://oeis.org/A389536>.

*Commentary.*

The even-index contraction and evenness give remainder zero at every even index at least four, while index two has remainder two. The odd-index contraction preserves the remainder and transforms m=2^k+1 into 2m-1=2^(k+1)+1. Strong induction proves the first equivalence. Evenness leaves only remainders zero and two, giving the complementary equivalence.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/SubstitutionSquareCubeModFour.a`
- Truth anchor: `D5/S1/Recurrence/Invariants/SubstitutionSquareCubeModFour.a_even`
- Truth anchor: `D5/S1/Recurrence/Invariants/SubstitutionSquareCubeModFour.coeff_recurrence`
- Truth anchor: `D5/S1/Recurrence/Invariants/SubstitutionSquareCubeModFour.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/SubstitutionSquareCubeModFour.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Invariants/SubstitutionSquareCubeModFour.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Invariants/SubstitutionSquareCubeModFour.hanna_conjecture`
