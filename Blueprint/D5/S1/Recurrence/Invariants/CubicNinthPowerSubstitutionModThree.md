# Hanna's Cubic Generating Equation Modulo Three

## Abstract

Every positive coefficient index outside the class one modulo seven in OEIS A363560 has coefficient divisible by three.

The generating equation and conjecture are recorded in hanna2023a363560. Write A for generatingSeries and U(k) for the auxiliary integer power-series approximations. All indices and exponents are natural numbers; X is the indeterminate. The operator coeff(n,f) extracts the degree-n coefficient, constantCoeff extracts the constant coefficient, and mk forms a series from its coefficient function. The remainder of n modulo seven is a natural-number remainder.

**Definition 1.1 (The stabilized integer coefficients).**

$$\begin{aligned}\operatorname{U}\left(0\right) = 1\\\forall k: \mathbb{N}, \operatorname{U}\left(k + 1\right) = 1 + X \cdot (\operatorname{U}\left(k\right) - \operatorname{U}\left(k\right)^{3} + \operatorname{U}\left(k\right)^{4} - \operatorname{U}\left(k\right)^{6} + \operatorname{U}\left(k\right)^{7})\\\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, \operatorname{U}\left(n + 1\right)\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Invariants/CubicNinthPowerSubstitutionModThree.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiplication by X raises coefficient agreement by one degree, while evaluating the displayed polynomial preserves agreement. Thus the degree-n coefficient has stabilized by approximation n+1.

**Definition 1.2 (The generating series).**

$$A = \operatorname{mk}\left(\operatorname{a}\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/CubicNinthPowerSubstitutionModThree.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A is the integer power series whose degree-n coefficient is a(n).

**Theorem 1.3 (The integral fixed-point bridge).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(B\right) = 1) \implies ((B^{3} = 1 + X \cdot (B + B^{2} + B^{9})) \iff (B = 1 + X \cdot (B - B^{3} + B^{4} - B^{6} + B^{7})))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CubicNinthPowerSubstitutionModThree.cubic_iff_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The polynomial t+t squared+t to the ninth factors as (t squared+t+1)(t-t cubed+t to the fourth-t to the sixth+t to the seventh). Subtracting the two sides of the cubic equation therefore gives (B squared+B+1)(B-1-X P(B))=0, where P is the polynomial in the displayed fixed-point equation. The first factor has constant coefficient three and is nonzero. Integer power series have no zero divisors, so cancellation proves the equivalence.

**Theorem 1.4 (The normalized cubic equation).**

$$(\operatorname{constantCoeff}\left(A\right) = 1) \land (A^{3} = 1 + X \cdot (A + A^{2} + A^{9}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CubicNinthPowerSubstitutionModThree.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stabilized approximations give the integral fixed-point identity and constant coefficient one. The bridge then gives the exact cubic generating equation.

**Theorem 1.5 (Uniqueness of the normalized integer solution).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(B\right) = 1) \implies (B^{3} = 1 + X \cdot (B + B^{2} + B^{9})) \implies B = A$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CubicNinthPowerSubstitutionModThree.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bridge turns any normalized cubic solution into a fixed point of the same polynomial operator. Induction on degree, using the extra factor X, proves agreement of every coefficient.

**Theorem 1.6 (The A363560 divisibility conjecture).**

$$\forall n: \mathbb{N}, (0 < n) \implies (n \bmod 7 \neq 1) \implies 3 \mid \operatorname{a}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CubicNinthPowerSubstitutionModThree.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a363560-cubic-ninth-power-substitution-mod-three` (proved) by `D5/S1/Recurrence/Invariants/CubicNinthPowerSubstitutionModThree.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a363560-cubic-ninth-power-substitution-mod-three","declaration_gid":"D5/S1/Recurrence/Invariants/CubicNinthPowerSubstitutionModThree.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2023). *OEIS A363560, g.f. satisfying A(x)^3 = 1 + x*(A(x) + A(x)^2 + A(x)^9)*. URL: <https://oeis.org/A363560>.

*Commentary.*

Reduce the integral fixed-point identity modulo three and subtract one, writing B for the reduced series minus one. The polynomial identity P(1+B)=1+B to the seventh in characteristic three gives B=X(1+B to the seventh). Below a fixed degree, convolution adds the residue classes of coefficient indices: the kth power of a series supported on class one is supported on class k modulo seven. Strong induction now shows that B vanishes outside class one. At positive degrees A and B have the same reduced coefficients, which proves divisibility by three.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/CubicNinthPowerSubstitutionModThree.a`
- Truth anchor: `D5/S1/Recurrence/Invariants/CubicNinthPowerSubstitutionModThree.cubic_iff_fixed`
- Truth anchor: `D5/S1/Recurrence/Invariants/CubicNinthPowerSubstitutionModThree.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/CubicNinthPowerSubstitutionModThree.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Invariants/CubicNinthPowerSubstitutionModThree.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Invariants/CubicNinthPowerSubstitutionModThree.hanna_conjecture`
