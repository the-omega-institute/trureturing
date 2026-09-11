# Hanna's Cubic Catalan Composition

## Abstract

The coefficients of C(x*C(x)^3) are odd exactly at zero and powers of two.

The generating function and parity conjecture are recorded in hanna2023a363308. Write C for catalanSeries and A for generatingSeries. Both series have integer coefficients, and X is the indeterminate. All coefficient indices and exponents are natural numbers. The operator subst(f,u) denotes formal composition f(u).

The operator mk forms a series from its coefficient function, catalan is Mathlib's natural Catalan sequence, and natCast denotes the coercion from natural numbers to integers. Write K for CatalanCompositionSquareParity.catalanSeries, the integer series XC. The operator map applies a ring homomorphism to every coefficient; intCast(ZMod(2)) denotes Int.castRingHom(ZMod(2)).

**Definition 1.1 (The Catalan generating series).**

$$C = \operatorname{mk}\left((n: \mathbb{N} \mapsto \operatorname{natCast}\left(\operatorname{catalan}\left(n\right)\right))\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/CatalanCubicCompositionParity.catalanSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The degree-n coefficient is the integer cast of catalan(n).

**Theorem 1.2 (The Catalan equation).**

$$C = 1 + X \cdot C^{2}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CatalanCubicCompositionParity.catalan_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Map Mathlib's Catalan generating-series identity from natural coefficients to integer coefficients.

**Definition 1.3 (The cubic composition).**

$$A = \operatorname{subst}\left(C, X \cdot C^{3}\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/CatalanCubicCompositionParity.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compose C with X times C cubed, exactly as in the generating function in hanna2023a363308. The inner series has zero constant coefficient.

**Definition 1.4 (The coefficient sequence).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, A\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/CatalanCubicCompositionParity.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer a(n) is the degree-n coefficient of the composition A.

**Theorem 1.5 (The composition equation and constant term).**

$$(\operatorname{constantCoeff}\left(A\right) = 1) \land (A = 1 + (X \cdot C^{3}) \cdot A^{2})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CatalanCubicCompositionParity.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substitution into the Catalan equation preserves addition, multiplication, and powers. Taking constant coefficients gives one.

**Theorem 1.6 (Reduction to the binary Catalan series).**

$$\operatorname{map}\left(\operatorname{intCast}\left(\operatorname{ZMod}\left(2\right)\right), A\right) = 1 + \operatorname{map}\left(\operatorname{intCast}\left(\operatorname{ZMod}\left(2\right)\right), K\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CatalanCubicCompositionParity.mod_two_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over ZMod(2), put c=map(intCast(ZMod(2)),C), k=map(intCast(ZMod(2)),K), and y=X times c cubed. Then k=Xc and k(1+k)=X. Multiplying y times (1+k) squared by X squared gives k cubed times (1+k) squared, which equals k times (k(1+k)) squared, hence X squared times k. Cancel X squared. Thus 1+k solves F=1+yF squared. Two solutions differ by an element annihilated by 1-y(F+G); this factor has constant coefficient one and is a unit. Uniqueness identifies the reduction of A with 1+k.

**Theorem 1.7 (The A363308 parity conjecture).**

$$\forall n: \mathbb{N}, \operatorname{Odd}\left(\operatorname{a}\left(n\right)\right) \iff (n = 0 \lor (\exists k: \mathbb{N}, n = 2^{k}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CatalanCubicCompositionParity.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a363308-catalan-cubic-composition-parity` (proved) by `D5/S1/Recurrence/Invariants/CatalanCubicCompositionParity.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a363308-catalan-cubic-composition-parity","declaration_gid":"D5/S1/Recurrence/Invariants/CatalanCubicCompositionParity.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2023). *OEIS A363308, expansion of C(x*C(x)^3) with C the Catalan g.f.*. URL: <https://oeis.org/A363308>.

*Commentary.*

The constant coefficient is one. At every positive index the modulo-two identity reduces parity to binary_catalan from CatalanCompositionSquareParity, which gives coefficient one exactly at powers of two.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/CatalanCubicCompositionParity.a`
- Truth anchor: `D5/S1/Recurrence/Invariants/CatalanCubicCompositionParity.catalanSeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/CatalanCubicCompositionParity.catalan_equation`
- Truth anchor: `D5/S1/Recurrence/Invariants/CatalanCubicCompositionParity.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/CatalanCubicCompositionParity.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Invariants/CatalanCubicCompositionParity.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Invariants/CatalanCubicCompositionParity.mod_two_identity`
- Dependency: [D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity](CatalanCompositionSquareParity.md)
