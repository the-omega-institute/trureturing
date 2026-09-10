# Strip-Three Ternary Catalan Parity

## Abstract

The coefficients of OEIS A378578 have ternary Catalan parity.

The entry cited in hanna2025a378578 defines A by removing every factor of three from the coefficients of 1+xA(x)^3. It conjectures that a(n) and binomial(3n,n)/(2n+1) have the same parity for every natural n.

PowerSeries(Z) is the integer formal power-series ring and X is its indeterminate. The functions coeff and constantCoeff extract coefficients, and mk constructs a series from its coefficient function. The notation div denotes integer division, with natural division on natural arguments; mod is remainder. Natural subtraction is truncated. The function intCast embeds a natural number into Z, and cast2 sends an integer or natural number to ZMod(2). The notation intCastRingHom denotes Lean's Int.castRingHom. The symbols approximation and step below describe the private construction of a.

**Definition 1.1 (Removing powers of three).**

$$\forall m: \mathbb{Z}, \operatorname{strip3}\left(m\right) = \operatorname{div}\left(m, (3)^{\operatorname{padicValInt}\left(3, m\right)}\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity.strip3` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The divisor is three to the integer's three-adic valuation. This divides every integer, including zero. The valuation of zero is zero, so strip3(0)=0.

**Theorem 1.2 (Stripping preserves parity).**

$$\forall m: \mathbb{Z}, \operatorname{cast2}\left(\operatorname{strip3}\left(m\right)\right) = \operatorname{cast2}\left(m\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity.strip3_mod_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiply strip3(m) by the removed power of three to recover m. In ZMod(2) that power is one, so the two integers have equal images.

**Definition 1.3 (Coefficientwise stripping).**

$$\forall F: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{strip3Series}\left(F\right) = \operatorname{mk}\left((n: \mathbb{N} \mapsto \operatorname{strip3}\left(\operatorname{coeff}\left(n, F\right)\right))\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity.strip3Series` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply strip3 separately to every coefficient.

**Definition 1.4 (The stabilized coefficient sequence).**

$$\begin{aligned}\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, \operatorname{approximation}\left(n + 1\right)\right)\\\operatorname{approximation}\left(0\right) = 1\\\forall d: \mathbb{N}, \operatorname{approximation}\left(d + 1\right) = \operatorname{step}\left(\operatorname{approximation}\left(d\right)\right)\\\forall F: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{step}\left(F\right) = \operatorname{strip3Series}\left(1 + X \cdot (F)^{3}\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The initial approximation is one. Multiplication by X makes the next coefficient depend only on preceding coefficients. Thus agreement below degree d improves to agreement below degree d+1 after applying step. The coefficient of degree n stabilizes by approximation n+1.

**Definition 1.5 (The integer generating series).**

$$\operatorname{generatingSeries} = \operatorname{mk}\left(\operatorname{a}\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The generating series has coefficient function a.

**Theorem 1.6 (The defining functional equation).**

$$(\operatorname{constantCoeff}\left(\operatorname{generatingSeries}\right) = 1) \land (\operatorname{generatingSeries} = \operatorname{strip3Series}\left(1 + X \cdot (\operatorname{generatingSeries})^{3}\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Stability of the diagonal coefficients proves the fixed-point equation. The constant coefficient is strip3(1)=1.

**Theorem 1.7 (Uniqueness of the generating series).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(B\right) = 1) \implies ((B = \operatorname{strip3Series}\left(1 + X \cdot (B)^{3}\right)) \implies (B = \operatorname{generatingSeries}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constant coefficients agree. Induction using the degree contraction then makes every coefficient agree with generatingSeries.

**Theorem 1.8 (Lucas recursions).**

$$\forall r: \mathbb{N}, (\operatorname{cast2}\left(\operatorname{choose}\left(3 \cdot (2 \cdot r), 2 \cdot r\right)\right) = \operatorname{cast2}\left(\operatorname{choose}\left(3 \cdot (r), r\right)\right)) \land ((\operatorname{cast2}\left(\operatorname{choose}\left(3 \cdot (4 \cdot r + 1), 4 \cdot r + 1\right)\right) = \operatorname{cast2}\left(\operatorname{choose}\left(3 \cdot (r), r\right)\right)) \land (\operatorname{cast2}\left(\operatorname{choose}\left(3 \cdot (4 \cdot r + 3), 4 \cdot r + 3\right)\right) = 0))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity.choose_three_lucas` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Lucas's theorem at the prime two removes the last binary digits. The even case takes one step, the residue-one case takes two steps, and the residue-three case contains the vanishing factor choose(0,1).

**Theorem 1.9 (Exact division at positive indices).**

$$\forall n: \mathbb{N}, (0 < n) \implies (\operatorname{div}\left(\operatorname{choose}\left(3 \cdot (n), n\right), 2 \cdot n + 1\right) = \operatorname{choose}\left(3 \cdot (n), n\right) - 2 \cdot \operatorname{choose}\left(3 \cdot n, n - 1\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity.ternary_catalan_div` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The adjacent-binomial identity gives n choose(3n,n) = (2n+1) choose(3n,n-1). For positive n it implies 2 choose(3n,n-1) <= choose(3n,n). Multiplying the displayed natural difference by 2n+1 gives choose(3n,n), proving the quotient identity.

**Theorem 1.10 (The reduced generating series).**

$$\operatorname{map}\left(\operatorname{intCastRingHom}\left(\operatorname{ZMod}\left(2\right)\right), \operatorname{generatingSeries}\right) = \operatorname{mk}\left((n: \mathbb{N} \mapsto \operatorname{cast2}\left(\operatorname{choose}\left(3 \cdot (n), n\right)\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity.mod_two_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Stripping preserves parity, so the mapped series F satisfies F=1+XF^3. Multiplication by F and characteristic two give F=F^2+XF^4. Frobenius expresses squares by substitution of X^2. The coefficient at 2r repeats that at r, the coefficient at 4r+1 repeats that at r, and the coefficient at 4r+3 vanishes. With constant coefficient one, strong induction and the Lucas recursions determine every coefficient.

**Theorem 1.11 (Hanna's parity conjecture).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) \bmod 2 = \operatorname{intCast}\left(\operatorname{div}\left(\operatorname{choose}\left(3 \cdot (n), n\right), 2 \cdot n + 1\right)\right) \bmod 2$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a378578-strip-three-ternary-catalan-parity` (proved) by `D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a378578-strip-three-ternary-catalan-parity","declaration_gid":"D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2025). *OEIS A378578, g.f. obtained by removing all factors of 3 from the coefficients of 1 + x*A(x)^3*. URL: <https://oeis.org/A378578>.

*Commentary.*

The reduced series gives the parity of choose(3n,n). For positive n the exact quotient differs from this binomial coefficient by twice a natural number. At n=0 the quotient and the binomial coefficient are both one. Converting equality in ZMod(2) to integer remainders proves the conjecture for every natural n.

## References

- Truth anchor: `D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity.a`
- Truth anchor: `D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity.choose_three_lucas`
- Truth anchor: `D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity.mod_two_identity`
- Truth anchor: `D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity.strip3`
- Truth anchor: `D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity.strip3Series`
- Truth anchor: `D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity.strip3_mod_two`
- Truth anchor: `D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity.ternary_catalan_div`
