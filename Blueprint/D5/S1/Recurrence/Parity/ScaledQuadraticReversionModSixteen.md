# Scaled Quadratic Reversion Modulo Sixteen

## Abstract

The normalized series of OEIS A396844 has alternating dyadic residues modulo sixteen.

The entry cited in hanna2026a396844 specifies A(x*A(x)-4*x*A(x)^2)=x^2 with A(x)=x+.... Its conjecture says that above index eight the residue is twelve exactly at indices 2*4^k+1, and that every other coefficient is divisible by sixteen.

All indices and exponents are natural numbers, and all coefficients are integers. A denotes generatingSeries in PowerSeries(Z), and X is its indeterminate. The operator subst(F,U) substitutes U into F; coeff(n,F) extracts the nth coefficient; mk constructs a series from a coefficient function. The operator map uses the displayed ring homomorphism; IntCast(ZMod(m)) denotes Int.castRingHom into ZMod(m). Remainders are integer remainders. B, F, P, C and q in the construction below name its private unit part, factor, step, approximations and stabilized coefficient function, respectively.

**Definition 1.1 (The integral construction).**

$$\begin{aligned}\forall c: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{B}\left(c\right) = 1 + X \cdot c\\\forall c: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{F}\left(c\right) = \operatorname{B}\left(c\right) \cdot (1 - 4 \cdot X \cdot \operatorname{B}\left(c\right))\\\forall c: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{P}\left(c\right) = 4 \cdot \operatorname{B}\left(c\right)^{2} - X \cdot (\operatorname{F}\left(c\right)^{2} \cdot \operatorname{subst}\left(c, X^{2} \cdot \operatorname{F}\left(c\right)\right))\\\operatorname{C}\left(0\right) = 0\\\forall n: \mathbb{N}, \operatorname{C}\left(n + 1\right) = \operatorname{P}\left(\operatorname{C}\left(n\right)\right)\\\forall n: \mathbb{N}, \operatorname{q}\left(n\right) = \operatorname{coeff}\left(n, \operatorname{C}\left(n + 1\right)\right)\\A = X + X^{2} \cdot \operatorname{mk}\left(q\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Parity/ScaledQuadraticReversionModSixteen.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The normalized form is A=X+X^2*mk(q). If two inputs to P agree below degree d, their outputs agree below degree d+1: B gains one degree through multiplication by X, and the substituted term has an outer factor X. Thus coefficient n stabilizes after n+1 iterations. This gives an integral fixed point without division.

**Definition 1.2 (The coefficient sequence).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, A\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/ScaledQuadraticReversionModSixteen.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The value a(n) is the integer coefficient of degree n in A.

**Theorem 1.3 (The functional equation and normalization).**

$$(\operatorname{constantCoeff}\left(A\right) = 0) \land ((\operatorname{coeff}\left(1, A\right) = 1) \land (\operatorname{subst}\left(A, (X \cdot A - 4 \cdot X \cdot A^{2})\right) = X^{2}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ScaledQuadraticReversionModSixteen.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For A=X+X^2*c, the inner argument is X^2*F(c). Expanding the composition gives X^2+X^3*(c-P(c)). The stabilized fixed point therefore satisfies the OEIS equation, with constant coefficient zero and linear coefficient one.

**Theorem 1.4 (Uniqueness over the integers).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(B\right) = 0) \implies ((\operatorname{coeff}\left(1, B\right) = 1) \implies ((\operatorname{subst}\left(B, (X \cdot B - 4 \cdot X \cdot B^{2})\right) = X^{2}) \implies (B = A)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ScaledQuadraticReversionModSixteen.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every series with the two normalization conditions has a unique form X+X^2*c. Cancellation of X^3 turns its functional equation into c=P(c). Induction on the agreement degree proves that any two fixed points coincide.

**Theorem 1.5 (Reduction modulo four).**

$$\operatorname{map}\left(\operatorname{IntCast}\left(\operatorname{ZMod}\left(4\right)\right), A\right) = X$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ScaledQuadraticReversionModSixteen.mod_four_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mapping the fixed-point equation to ZMod(4) makes c=0 a solution. The same degree-contraction uniqueness gives c=0 and hence A=X.

**Theorem 1.6 (The corrected classification).**

$$\forall n: \mathbb{N}, (2 \le n) \implies ((((\operatorname{a}\left(n\right) \bmod 16 = 4) \iff (\exists k: \mathbb{N}, ((\operatorname{Even}\left(k\right)) \land (n = 2^{k} + 1)))) \land (((\operatorname{a}\left(n\right) \bmod 16 = 12) \iff (\exists k: \mathbb{N}, ((\operatorname{Odd}\left(k\right)) \land (n = 2^{k} + 1)))) \land ((16 \mid \operatorname{a}\left(n\right)) \iff (\neg (\exists k: \mathbb{N}, (n = 2^{k} + 1)))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ScaledQuadraticReversionModSixteen.mod_sixteen_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let R be inverseSeries from AlternatingDyadicReversionModFour. Its inverse_equation is R+R(X^2)=X. Write R=X*T; then T+X*T(X^2)=1. Over ZMod(16), multiplication by four annihilates each perturbation in B(4*T) and F(4*T). An annihilated difference of substitution arguments remains annihilated after taking powers and then after substitution. These facts show P(4*T)=4*T. Uniqueness gives A=X+4*X*R modulo sixteen. Coefficient induction in R+R(X^2)=X gives coefficient (-1)^k at degree 2^k and zero elsewhere, proving all three biconditionals.

**Definition 1.7 (The literature conjecture as a closed proposition).**

$$(\operatorname{hannaClaim}\left(\right)) \iff (\forall n: \mathbb{N}, (8 < n) \implies ((((\operatorname{a}\left(n\right) \bmod 16 = 12) \iff (\exists k: \mathbb{N}, (n = 2 \cdot 4^{k} + 1))) \land ((\neg (\exists k: \mathbb{N}, (n = 2 \cdot 4^{k} + 1))) \implies (16 \mid \operatorname{a}\left(n\right))))))$$

*Formalization.* `D5/S1/Recurrence/Parity/ScaledQuadraticReversionModSixteen.hannaClaim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This proposition quantifies over every natural index greater than eight. It includes both the residue-twelve biconditional and the divisibility assertion at all remaining indices.

**Theorem 1.8 (Refutation of the literature conjecture).**

$$\neg \operatorname{hannaClaim}\left(\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ScaledQuadraticReversionModSixteen.hanna_conjecture_false` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a396844-scaled-quadratic-reversion-mod-sixteen` (refuted) by `D5/S1/Recurrence/Parity/ScaledQuadraticReversionModSixteen.hanna_conjecture_false`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a396844-scaled-quadratic-reversion-mod-sixteen","declaration_gid":"D5/S1/Recurrence/Parity/ScaledQuadraticReversionModSixteen.hanna_conjecture_false","resolution_kind":"refuted"} -->

*Citation.* Paul D. Hanna (2026). *OEIS A396844, g.f. satisfying A(x*A(x) - 4*x*A(x)^2) = x^2*. URL: <https://oeis.org/A396844>.

*Commentary.*

The literature conjecture in hanna2026a396844 is refuted. The corrected classification holds for every n at least two: residue four occurs exactly at n=2^k+1 with even k, residue twelve exactly with odd k, and divisibility by sixteen exactly off this support. In particular, 17=2^4+1 has residue four by the symbolic classification. Since 17 is not 2*4^k+1 for any natural k, the conjecture would require sixteen to divide a(17), a contradiction.

## References

- Truth anchor: `D5/S1/Recurrence/Parity/ScaledQuadraticReversionModSixteen.a`
- Truth anchor: `D5/S1/Recurrence/Parity/ScaledQuadraticReversionModSixteen.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Parity/ScaledQuadraticReversionModSixteen.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Parity/ScaledQuadraticReversionModSixteen.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Parity/ScaledQuadraticReversionModSixteen.hannaClaim`
- Truth anchor: `D5/S1/Recurrence/Parity/ScaledQuadraticReversionModSixteen.hanna_conjecture_false`
- Truth anchor: `D5/S1/Recurrence/Parity/ScaledQuadraticReversionModSixteen.mod_four_identity`
- Truth anchor: `D5/S1/Recurrence/Parity/ScaledQuadraticReversionModSixteen.mod_sixteen_classification`
- Dependency: [D5/S1/Recurrence/Invariants/AlternatingDyadicReversionModFour](../Invariants/AlternatingDyadicReversionModFour.md)
