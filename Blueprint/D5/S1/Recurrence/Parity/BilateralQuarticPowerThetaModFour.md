# Bilateral Quartic Powers Modulo Four

## Abstract

The bilateral equation of OEIS A379204 implies Hanna's parity and square-shift conjectures.

The entry hanna2024a379204 defines A by 1/x equal to the sum over integer n of A(x)^n times (A(x)^n+4)^(n+1). Hanna conjectures that a(n) is even for n greater than one, and that its remainder modulo four is two exactly when n=(k-1)^2+1 for a natural k greater than one. The complete mod-four classification below implies the evenness conjecture.

Here generatingSeries is an integer formal power series and X is its indeterminate. The indices N, d, k, and the argument of a are natural numbers; the argument n of bilateralTerm is an integer. The operator toNat truncates an integer below zero, natAbs is its natural absolute value, and intCast embeds a natural number into the integers. Subtraction in natural exponents and k-1 is truncated. The operator coeff extracts a coefficient, mk constructs a series from its coefficient function, and invOfUnit denotes the formal inverse with the specified unit constant coefficient. The operator mod is integer remainder; map applies a ring homomorphism to every coefficient, and intCastRingHom denotes Int.castRingHom.

The imported thetaSeries belongs to `D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour`. Its constant coefficient is one; its other coefficients are two at positive square degrees and zero elsewhere, as stated by coeff_thetaSeries.

**Definition 1.1 (The ordinary-series bilateral terms).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall n: \mathbb{Z}, \operatorname{bilateralTerm}\left(A, n\right) = (\operatorname{if} (0 \le n) \operatorname{then} A^{\operatorname{toNat}\left(n\right)} \cdot (A^{\operatorname{toNat}\left(n\right)} + 4)^{\operatorname{toNat}\left(n\right) + 1} \operatorname{else} (\operatorname{if} (n = -(1)) \operatorname{then} 0 \operatorname{else} A^{(\operatorname{natAbs}\left(n\right) - 1)^{2} - 1} \cdot \operatorname{invOfUnit}\left(1 + 4 \cdot A^{\operatorname{natAbs}\left(n\right)}, 1\right)^{\operatorname{natAbs}\left(n\right) - 1}))$$

*Formalization.* `D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour.bilateralTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For n=-r with r at least two, factoring powers of A gives the displayed nonnegative exponent and unit inverse. The index -1 is the Laurent term A^(-1). Multiplication of the equation by X*A absorbs that term into the isolated X, so bilateralTerm(A,-1)=0.

**Definition 1.2 (The stabilized coefficient sequence).**

$$\begin{aligned}\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, \operatorname{P}\left(n + 1\right)\right)\\\operatorname{P}\left(0\right) = 0\\\forall d: \mathbb{N}, \operatorname{P}\left(d + 1\right) = \operatorname{mk}\left((N: \mathbb{N} \mapsto \operatorname{coeff}\left(N, X + X \cdot \operatorname{P}\left(d\right) \cdot \sum_{j \in \operatorname{Icc}\left(-(\operatorname{intCast}\left(N\right)) - 2, \operatorname{intCast}\left(N\right)\right)} (\operatorname{bilateralTerm}\left(\operatorname{P}\left(d\right), j\right))\right))\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The auxiliary P is the degree approximation. Its initial value is zero, and the displayed iteration preserves zero constant coefficient. Products, powers, and inverses of the unit denominators preserve agreement below degree d. The outer X improves agreement to degree d+1, so the diagonal coefficient stabilizes.

**Definition 1.3 (The integer generating series).**

$$\operatorname{generatingSeries} = \operatorname{mk}\left(\operatorname{a}\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The generating series has coefficient function a.

**Theorem 1.4 (The exact finite-window equation).**

$$(\operatorname{constantCoeff}\left(\operatorname{generatingSeries}\right) = 0) \land ((\operatorname{coeff}\left(1, \operatorname{generatingSeries}\right) = 1) \land (\forall N: \mathbb{N}, \operatorname{coeff}\left(N, \operatorname{generatingSeries}\right) = \operatorname{coeff}\left(N, X + X \cdot \operatorname{generatingSeries} \cdot \sum_{j \in \operatorname{Icc}\left(-(\operatorname{intCast}\left(N\right)) - 2, \operatorname{intCast}\left(N\right)\right)} (\operatorname{bilateralTerm}\left(\operatorname{generatingSeries}, j\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coefficient stabilization gives a fixed point of the displayed finite-window operator. Its constant coefficient is zero and its linear coefficient is one. The order bound below justifies the window as the coefficientwise meaning of the bilateral equation after multiplication by X*A.

**Theorem 1.5 (Uniqueness of the zero-constant solution).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(B\right) = 0) \implies ((\forall N: \mathbb{N}, \operatorname{coeff}\left(N, B\right) = \operatorname{coeff}\left(N, X + X \cdot B \cdot \sum_{j \in \operatorname{Icc}\left(-(\operatorname{intCast}\left(N\right)) - 2, \operatorname{intCast}\left(N\right)\right)} (\operatorname{bilateralTerm}\left(B, j\right))\right)) \implies (B = \operatorname{generatingSeries}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every solution is a fixed point of the same operator. For two unit denominators U and V, their inverse difference is -inv(U)*(U-V)*inv(V), so inversion preserves coefficient agreement. Induction using the outer X proves equality of every coefficient.

**Theorem 1.6 (The order and window bounds).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(A\right) = 0) \implies (\forall N: \mathbb{N}, \forall n: \mathbb{Z}, (((N < (\operatorname{if} (0 \le n) \operatorname{then} \operatorname{toNat}\left(n\right) \operatorname{else} (\operatorname{natAbs}\left(n\right) - 1)^{2} - 1)) \lor (\neg (n \in \operatorname{Icc}\left(-(\operatorname{intCast}\left(N\right)) - 2, \operatorname{intCast}\left(N\right)\right))))) \implies (\operatorname{coeff}\left(N, \operatorname{bilateralTerm}\left(A, n\right)\right) = 0))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour.bilateralTerm_coeff_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Zero constant coefficient makes A divisible by X. Each term is therefore divisible by the displayed power of X. An index outside [-N-2,N] makes this power greater than N, so both the order criterion and the outside-window criterion force a zero coefficient.

**Theorem 1.7 (The series modulo two).**

$$\operatorname{map}\left(\operatorname{intCastRingHom}\left(\operatorname{ZMod}\left(2\right)\right), \operatorname{generatingSeries}\right) = X$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour.mod_two_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Modulo four, A times the term at m and A times the term at -m-2 both equal A^((m+1)^2). The central term is zero. Pairing the whole finite interval therefore gives twice a finite sum of square powers. Mapping this identity to ZMod(2) removes the sum and gives A=X.

**Theorem 1.8 (The theta identity modulo four).**

$$\operatorname{map}\left(\operatorname{intCastRingHom}\left(\operatorname{ZMod}\left(4\right)\right), \operatorname{generatingSeries}\right) = X \cdot \operatorname{map}\left(\operatorname{intCastRingHom}\left(\operatorname{ZMod}\left(4\right)\right), \operatorname{thetaSeries}\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour.mod_four_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of integer series modulo two implies equality of their doubles modulo four. Apply this to the finite sums of square powers of A and X. The paired fixed-point equation becomes X times one plus twice the square-power sum. At each degree, at most one positive square root contributes, giving the imported theta coefficient.

**Theorem 1.9 (The square-shift characterization).**

$$\forall n: \mathbb{N}, (1 \le n) \implies ((((\operatorname{a}\left(n\right) \bmod 4 = 2) \iff (\exists k: \mathbb{N}, ((1 < k) \land (n = (k - 1)^{2} + 1)))) \land ((\operatorname{a}\left(n\right) \bmod 4 = 0) \iff ((1 < n) \land (\neg (\exists k: \mathbb{N}, ((1 < k) \land (n = (k - 1)^{2} + 1))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour.hanna_conjecture_mod_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n at least one, coefficient comparison gives remainder two exactly when n-1 is a positive square, equivalently n=(k-1)^2+1 with k greater than one. The remainder-zero clause also requires n greater than one, because the linear coefficient is one. The remainder-two biconditional proves the second conjecture in hanna2024a379204.

**Theorem 1.10 (Hanna's evenness conjecture).**

$$\forall n: \mathbb{N}, (1 < n) \implies (\operatorname{Even}\left(\operatorname{a}\left(n\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a379204-bilateral-quartic-power-theta-mod-four` (proved) by `D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a379204-bilateral-quartic-power-theta-mod-four","declaration_gid":"D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2024). *OEIS A379204, g.f. satisfying 1/x = Sum_{n in Z} A(x)^n (A(x)^n + 4)^(n+1)*. URL: <https://oeis.org/A379204>.

*Commentary.*

For n greater than one, the mod-four classification gives either remainder two or remainder zero. Both imply divisibility by two, proving the first conjecture in hanna2024a379204.

## References

- Truth anchor: `D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour.a`
- Truth anchor: `D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour.bilateralTerm`
- Truth anchor: `D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour.bilateralTerm_coeff_eq_zero`
- Truth anchor: `D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour.hanna_conjecture_mod_four`
- Truth anchor: `D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour.mod_four_identity`
- Truth anchor: `D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour.mod_two_identity`
- Dependency: [D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour](ThetaSelfCompositionModFour.md)
- Narrative reference: [D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour](ThetaSelfCompositionModFour.md)
