# Double Catalan Composition and Powers of Four

## Abstract

The coefficients of OEIS A374568 are odd exactly at powers of four.

The generating equation and parity conjecture are recorded in hanna2024a374568. Write A for generatingSeries and C for CatalanCompositionSquareParity.catalanSeries, the shifted integer Catalan series satisfying C=X+C squared. The coefficients a(n), the series A and C, and the approximations B(r) are integer-valued. All coefficient indices and exponents are natural numbers.

The operator subst(f,u) denotes composition f(u), and mk forms a power series from its coefficient function. The operator map applies a ring homomorphism coefficientwise; intCast(ZMod(2)) denotes Int.castRingHom(ZMod(2)). In formulas involving this map, X denotes the indeterminate over ZMod(2).

**Definition 1.1 (Construction of the integer series).**

$$\begin{aligned}\operatorname{B}\left(0\right) = 0\\\forall r: \mathbb{N}, \operatorname{B}\left(r + 1\right) = C + \operatorname{subst}\left(\operatorname{B}\left(r\right), \operatorname{subst}\left(X + X^{2}, C\right)\right)^{2}\\A = \operatorname{mk}\left((n: \mathbb{N} \mapsto \operatorname{coeff}\left(n, \operatorname{B}\left(n + 1\right)\right))\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Invariants/CatalanDoubleCompositionPowersOfFour.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The recursion starts at zero. Since every approximation has zero constant coefficient, its squared composition gains one degree of agreement at each step. The diagonal coefficients therefore stabilize and define the integer series A.

**Definition 1.2 (The coefficient sequence).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, A\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/CatalanDoubleCompositionPowersOfFour.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer a(n) is the degree-n coefficient of A.

**Theorem 1.3 (The exact functional equation and normalization).**

$$(\operatorname{constantCoeff}\left(A\right) = 0) \land ((\operatorname{coeff}\left(1, A\right) = 1) \land (X = \operatorname{subst}\left(A, X - X^{2}\right) - \operatorname{subst}\left(A, X + X^{2}\right)^{2}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CatalanDoubleCompositionPowersOfFour.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Catalan series is the compositional inverse of X-X squared. Substituting X-X squared into the stabilized recursion gives the displayed OEIS equation. The constant coefficient is zero, and the square term contributes nothing to degree one.

**Theorem 1.4 (Uniqueness of the integer solution).**

$$\forall f: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(f\right) = 0) \implies (X = \operatorname{subst}\left(f, X - X^{2}\right) - \operatorname{subst}\left(f, X + X^{2}\right)^{2}) \implies f = A$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CatalanDoubleCompositionPowersOfFour.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compose the equation with C to recover the same fixed-point recursion. Induction on coefficient agreement proves that every zero-constant solution equals A. No separate linear-coefficient hypothesis is needed.

**Theorem 1.5 (Identification with the binary Catalan series).**

$$\operatorname{subst}\left(\operatorname{map}\left(\operatorname{intCast}\left(\operatorname{ZMod}\left(2\right)\right), A\right), X + X^{2}\right) = \operatorname{map}\left(\operatorname{intCast}\left(\operatorname{ZMod}\left(2\right)\right), C\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CatalanDoubleCompositionPowersOfFour.mod_two_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After reduction modulo two, both substitution arguments become X+X squared. Thus Y=subst(map(A),X+X squared) satisfies Y=X+Y squared. The reduced Catalan series satisfies the same equation. Subtracting these equations factors their difference by a series with constant coefficient one, so the two solutions coincide.

**Theorem 1.6 (Hanna's powers-of-four parity conjecture).**

$$\forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{Odd}\left(\operatorname{a}\left(n\right)\right) \iff (\exists k: \mathbb{N}, n = 4^{k}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CatalanDoubleCompositionPowersOfFour.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a374568-catalan-double-composition-powers-of-four` (proved) by `D5/S1/Recurrence/Invariants/CatalanDoubleCompositionPowersOfFour.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a374568-catalan-double-composition-powers-of-four","declaration_gid":"D5/S1/Recurrence/Invariants/CatalanDoubleCompositionPowersOfFour.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2024). *OEIS A374568, g.f. satisfying x = A(x-x^2) - A(x+x^2)^2*. URL: <https://oeis.org/A374568>.

*Commentary.*

Write Cbar for the reduction of C. Since Cbar+Cbar squared=X, composing the preceding identity with Cbar gives map(A)=Cbar(Cbar). Put D=Cbar(Cbar). Composing the Catalan equation gives D=Cbar+D squared. Squaring and using characteristic two cancels the middle square, yielding D=X+D to the fourth power. Frobenius identifies the fourth power with substitution of X to the fourth power. Strong induction on the coefficient index now gives coefficient one exactly at powers of four, which is equivalent to oddness of the integer coefficient.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/CatalanDoubleCompositionPowersOfFour.a`
- Truth anchor: `D5/S1/Recurrence/Invariants/CatalanDoubleCompositionPowersOfFour.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/CatalanDoubleCompositionPowersOfFour.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Invariants/CatalanDoubleCompositionPowersOfFour.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Invariants/CatalanDoubleCompositionPowersOfFour.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Invariants/CatalanDoubleCompositionPowersOfFour.mod_two_identity`
- Dependency: [D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity](CatalanCompositionSquareParity.md)
