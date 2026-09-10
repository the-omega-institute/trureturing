# Shifted Iterate Fixed Point Congruences

## Abstract

For r and m at least two with m dividing r-1, the shifted compositional fixed point has all positive coefficients equal to one modulo m.

The entries cited in hanna2024a378575 and hanna2024a378576 define A(x)=x+x*iterate(A,r)(x) for r=5 and r=6, respectively. They conjecture that the positive-index coefficients are one modulo four and five. Both follow from the general shifted-iterate theorem below.

All indices and parameters r and m are natural numbers. PowerSeries(R) is the formal power-series ring over R, with indeterminate X. The imported CompositionalIterateCongruence defines iterate(f,0)=X and iterate(f,j+1) by substituting f into iterate(f,j). Its mobius(c) is X times the geometric series with coefficients c^n. Their implicit ring arguments are displayed explicitly. The operator mk constructs a series from its coefficient function. The map operator takes a ring homomorphism followed by a series; intCastRingHom is the canonical homomorphism from the integers to the indicated ring. Subtraction r-1 is natural subtraction. Coefficients a(r,n) and all remainders are integers, with the natural modulus coerced to an integer.

**Definition 1.1 (The integer coefficient family).**

$$\begin{aligned}\forall r: \mathbb{N}, \forall n: \mathbb{N}, \operatorname{a}\left(r, n\right) = \operatorname{coeff}\left(n, \operatorname{approximation}\left(\mathbb{Z}, r, n + 1\right)\right)\\\forall r: \mathbb{N}, \operatorname{approximation}\left(\mathbb{Z}, r, 0\right) = 0\\\forall r: \mathbb{N}, \forall d: \mathbb{N}, \operatorname{approximation}\left(\mathbb{Z}, r, d + 1\right) = X + X \cdot \operatorname{iterate}\left(\mathbb{Z}, \operatorname{approximation}\left(\mathbb{Z}, r, d\right), r\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Parity/ShiftedIterateFixedPointCongruence.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The auxiliary approximation starts at zero and repeatedly applies f mapped to X+X*iterate(f,r). Its coefficients below degree d are stable after d steps. The displayed diagonal defines a(r,n).

**Definition 1.2 (The generating series family).**

$$\forall r: \mathbb{N}, \operatorname{generatingSeries}\left(r\right) = \operatorname{mk}\left(\operatorname{a}\left(r\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/ShiftedIterateFixedPointCongruence.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each r, mk uses the integer coefficient function a(r).

**Theorem 1.3 (Existence and the defining equation).**

$$\forall r: \mathbb{N}, (2 \le r) \implies ((\operatorname{constantCoeff}\left(\operatorname{generatingSeries}\left(r\right)\right) = 0) \land (\operatorname{coeff}\left(1, \operatorname{generatingSeries}\left(r\right)\right) = 1) \land (\operatorname{generatingSeries}\left(r\right) = X + X \cdot \operatorname{iterate}\left(\mathbb{Z}, \operatorname{generatingSeries}\left(r\right), r\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ShiftedIterateFixedPointCongruence.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substitution of zero-constant series preserves agreement below a given degree: powers agree there, and higher powers contribute zero. Induction extends this to every compositional iterate. Multiplication by X improves agreement by one degree. The stabilized diagonal is therefore a fixed point. Its constant coefficient is zero, and its linear coefficient is one because every iterate has constant coefficient zero.

**Theorem 1.4 (Uniqueness of the integer solution).**

$$\forall r: \mathbb{N}, (2 \le r) \implies \forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(B\right) = 0) \implies (B = X + X \cdot \operatorname{iterate}\left(\mathbb{Z}, B, r\right)) \implies B = \operatorname{generatingSeries}\left(r\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ShiftedIterateFixedPointCongruence.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two zero-constant fixed points agree below degree zero. Repeated application of the shifted-iterate contraction gives agreement below every degree, so the coefficient extensionality theorem identifies them.

**Theorem 1.5 (The reduced series is geometric).**

$$\forall r: \mathbb{N}, \forall m: \mathbb{N}, (2 \le r) \implies (2 \le m) \implies (m \mid (r - 1)) \implies \operatorname{map}\left(\operatorname{intCastRingHom}\left(\operatorname{ZMod}\left(m\right)\right), \operatorname{generatingSeries}\left(r\right)\right) = \operatorname{mobius}\left(\operatorname{ZMod}\left(m\right), 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ShiftedIterateFixedPointCongruence.mod_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coefficient mapping commutes with substitution, so the reduced integer series satisfies the same fixed-point equation over ZMod(m). The divisibility hypothesis makes r equal to one in this ring. The imported mobius_iterate identity then gives iterate(mobius(1),r)=mobius(1). The geometric-series identity gives mobius(1)=X+X*mobius(1). The same degree contraction proves uniqueness over ZMod(m), giving the displayed equality.

**Theorem 1.6 (The general congruence).**

$$\forall r: \mathbb{N}, \forall m: \mathbb{N}, (2 \le r) \implies (2 \le m) \implies (m \mid (r - 1)) \implies \forall n: \mathbb{N}, (1 \le n) \implies \operatorname{a}\left(r, n\right) \bmod m = 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ShiftedIterateFixedPointCongruence.shift_iterate_mod` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positive-degree coefficient of mobius(1) is one. Taking a coefficient in the reduced-series identity and using the integer-cast congruence equivalence gives the integer remainder. Since m is at least two, the remainder of one is one.

**Theorem 1.7 (Hanna's A378575 conjecture).**

$$\forall n: \mathbb{N}, (1 \le n) \implies \operatorname{a}\left(5, n\right) \bmod 4 = 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ShiftedIterateFixedPointCongruence.hanna_conjecture_five` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a378575-shifted-iterate-fixed-point-mod-four` (proved) by `D5/S1/Recurrence/Parity/ShiftedIterateFixedPointCongruence.hanna_conjecture_five`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a378575-shifted-iterate-fixed-point-mod-four","declaration_gid":"D5/S1/Recurrence/Parity/ShiftedIterateFixedPointCongruence.hanna_conjecture_five","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2024). *OEIS A378575, g.f. satisfying A(x) = x + x*A^5(x) (5-fold compositional iterate)*. URL: <https://oeis.org/A378575>.

*Commentary.*

Set r=5 and m=4 in the general theorem. Four divides 5-1, proving the conjecture quoted in hanna2024a378575 for every positive index.

**Theorem 1.8 (Hanna's A378576 conjecture).**

$$\forall n: \mathbb{N}, (1 \le n) \implies \operatorname{a}\left(6, n\right) \bmod 5 = 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ShiftedIterateFixedPointCongruence.hanna_conjecture_six` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a378576-shifted-iterate-fixed-point-mod-five` (proved) by `D5/S1/Recurrence/Parity/ShiftedIterateFixedPointCongruence.hanna_conjecture_six`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a378576-shifted-iterate-fixed-point-mod-five","declaration_gid":"D5/S1/Recurrence/Parity/ShiftedIterateFixedPointCongruence.hanna_conjecture_six","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2024). *OEIS A378576, g.f. satisfying A(x) = x + x*A^6(x) (6-fold compositional iterate)*. URL: <https://oeis.org/A378576>.

*Commentary.*

Set r=6 and m=5 in the general theorem. Five divides 6-1, proving the conjecture quoted in hanna2024a378576 for every positive index.

## References

- Truth anchor: `D5/S1/Recurrence/Parity/ShiftedIterateFixedPointCongruence.a`
- Truth anchor: `D5/S1/Recurrence/Parity/ShiftedIterateFixedPointCongruence.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Parity/ShiftedIterateFixedPointCongruence.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Parity/ShiftedIterateFixedPointCongruence.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Parity/ShiftedIterateFixedPointCongruence.hanna_conjecture_five`
- Truth anchor: `D5/S1/Recurrence/Parity/ShiftedIterateFixedPointCongruence.hanna_conjecture_six`
- Truth anchor: `D5/S1/Recurrence/Parity/ShiftedIterateFixedPointCongruence.mod_identity`
- Truth anchor: `D5/S1/Recurrence/Parity/ShiftedIterateFixedPointCongruence.shift_iterate_mod`
- Dependency: [D5/S1/Recurrence/Invariants/CompositionalIterateCongruence](../Invariants/CompositionalIterateCongruence.md)
