# Catalan Composition and Hanna's Parity Conjecture

## Abstract

The normalized solution of OEIS A374570 has odd coefficients above degree one exactly at powers of two plus one.

The generating equation and parity conjecture are recorded in hanna2024a374570. Write C for catalanSeries and A for generatingSeries. All coefficient indices and exponents are natural numbers. The series A, C, D, and B(r) have integer coefficients; X is the indeterminate. The operator subst(f,u) means composition f(u).

The operator mk forms a series from its coefficient function. The function catalan is Mathlib's natural Catalan sequence, natCast(Z) is Nat.castRingHom(Z), and intCast(ZMod(2)) is Int.castRingHom(ZMod(2)). The operator map applies the indicated ring homomorphism to every coefficient. Thus the binary Catalan formula is an equality in ZMod(2).

**Definition 1.1 (The shifted Catalan series).**

$$\begin{aligned}D = \operatorname{map}\left(\operatorname{natCast}\left(\mathbb{Z}\right), \operatorname{mk}\left(\operatorname{catalan}\right)\right)\\C = X \cdot D\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity.catalanSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D is Mathlib's Catalan series mapped to integer coefficients, and C is its product with X. This fixes the shift in the OEIS equation.

**Theorem 1.2 (The Catalan equation and normalization).**

$$(\operatorname{constantCoeff}\left(C\right) = 0) \land ((\operatorname{coeff}\left(1, C\right) = 1) \land (C = X + C^{2}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity.catalan_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mapping Mathlib's Catalan identity to the integers and multiplying by X gives the quadratic equation. The shift gives zero constant coefficient and linear coefficient one.

**Theorem 1.3 (Uniqueness of the shifted Catalan series).**

$$\forall f: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(f\right) = 0) \implies (f = X + f^{2}) \implies f = C$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity.catalan_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtract two quadratic equations. Their difference is annihilated by 1-f-C, whose constant coefficient is one. This factor is a unit, so the difference vanishes.

**Definition 1.4 (Construction of the normalized solution).**

$$\begin{aligned}\operatorname{B}\left(0\right) = 1\\\forall r: \mathbb{N}, \operatorname{B}\left(r + 1\right) = D \cdot \operatorname{subst}\left(\operatorname{B}\left(r\right), X^{2} \cdot \operatorname{B}\left(r\right) \cdot D\right)\\A = X \cdot \operatorname{mk}\left((n: \mathbb{N} \mapsto \operatorname{coeff}\left(n, \operatorname{B}\left(n\right)\right))\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed recursion defines the auxiliary approximations B(r). The substitution argument is divisible by X squared. Consequently agreement below degree r, for r at least one, gains a degree under the recursion. The diagonal coefficients stabilize and define A.

**Definition 1.5 (The coefficient sequence).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, A\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer a(n) is the degree-n coefficient of A.

**Theorem 1.6 (The exact OEIS functional equation).**

$$(\operatorname{constantCoeff}\left(A\right) = 0) \land ((\operatorname{coeff}\left(1, A\right) = 1) \land (A^{2} = \operatorname{subst}\left(A, A \cdot C\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stabilized series B satisfies B=D subst(B,X squared times B times D). With A=XB and C=XD, this identity gives A squared equal to subst(A,AC), together with both normalization conditions.

**Theorem 1.7 (Uniqueness of the normalized integer solution).**

$$\forall f: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(f\right) = 0) \implies (\operatorname{coeff}\left(1, f\right) = 1) \implies (f^{2} = \operatorname{subst}\left(f, f \cdot C\right)) \implies f = A$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Factor any normalized solution as Xb. The constant coefficient of b is one, so b is a unit. Cancel X squared and b from the functional equation to obtain the same fixed-point equation. Degree contraction then proves equality with the constructed solution.

**Theorem 1.8 (Binary support of the shifted Catalan series).**

$$\forall n: \mathbb{N}, (\operatorname{coeff}\left(n, \operatorname{map}\left(\operatorname{intCast}\left(\operatorname{ZMod}\left(2\right)\right), C\right)\right) = 1) \iff (\exists k: \mathbb{N}, n = 2^{k})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity.binary_catalan` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In characteristic two, squaring a series substitutes X squared. The Catalan equation therefore sends each even positive index to half that index; odd indices above one have zero coefficient. Strong induction gives coefficient one exactly at powers of two.

**Theorem 1.9 (The A374570 parity conjecture).**

$$\forall n: \mathbb{N}, (1 < n) \implies (\operatorname{Odd}\left(\operatorname{a}\left(n\right)\right) \iff (\exists k: \mathbb{N}, n = 2^{k} + 1))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a374570-catalan-composition-square-parity` (proved) by `D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a374570-catalan-composition-square-parity","declaration_gid":"D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2024). *OEIS A374570, g.f. satisfying A(x)^2 = A(A(x)*C(x)) with C the Catalan function*. URL: <https://oeis.org/A374570>.

*Commentary.*

Reduce the generating equation modulo two. Frobenius gives subst(A,X squared)=subst(A,AC). The compositional inverse of the normalized outer series cancels A, giving AC=X squared. The Catalan identity gives C(1+C)=X. Factoring C as X times a unit permits cancellation, yielding A=X(1+C). Above degree one, the coefficients are therefore odd exactly when the preceding index is a power of two.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity.a`
- Truth anchor: `D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity.binary_catalan`
- Truth anchor: `D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity.catalanSeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity.catalan_equation`
- Truth anchor: `D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity.catalan_unique`
- Truth anchor: `D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity.hanna_conjecture`
