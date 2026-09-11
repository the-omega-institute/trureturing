# Catalan Inversion and Hanna's Mod-Four Conjecture

## Abstract

The coefficients of OEIS A393172 above degree one are two modulo four exactly at powers of two, and zero otherwise.

The generating equation and conjecture are recorded in hanna2026a393172. Write A for generatingSeries and C for CatalanCompositionSquareParity.catalanSeries, the integer series with zero constant coefficient satisfying C=X+C squared. The auxiliary B(r) are integer series, and all indices and exponents are natural numbers. X is the indeterminate.

The operator subst(f,u) means composition f(u). The operator mk forms a series from its coefficient function. The operator map applies its first argument, a ring homomorphism, to the coefficients of its second argument. Here intCast(ZMod(2)) denotes Int.castRingHom(ZMod(2)). Remainders of a(n) are integer remainders; remainder zero modulo four is equivalent to divisibility by four.

**Definition 1.1 (The stabilized integer coefficients).**

$$\begin{aligned}\operatorname{B}\left(0\right) = 0\\\forall r: \mathbb{N}, \operatorname{B}\left(r + 1\right) = C + \operatorname{subst}\left(\operatorname{B}\left(r\right), C\right)^{2}\\\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, \operatorname{B}\left(n + 1\right)\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Invariants/CatalanShiftSquareModFour.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed B recursion is the auxiliary approximation sequence. Composition with C preserves agreement below a degree, and squaring zero-constant series gains a degree. Thus each diagonal coefficient used to define a(n) has stabilized.

**Definition 1.2 (The generating series).**

$$A = \operatorname{mk}\left(\operatorname{a}\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/CatalanShiftSquareModFour.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The degree-n coefficient of A is a(n).

**Theorem 1.3 (The exact generating equation and normalization).**

$$(\operatorname{constantCoeff}\left(A\right) = 0) \land ((\operatorname{coeff}\left(1, A\right) = 1) \land (\operatorname{subst}\left(A, X - X^{2}\right) = X + A^{2}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CatalanShiftSquareModFour.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stabilized series satisfies A=C+subst(A,C) squared. The Catalan equation identifies C as the compositional inverse of X-X squared. Composing the fixed-point identity with X-X squared gives the OEIS equation. The constant coefficient is zero, and the quadratic term has no linear coefficient, so the linear coefficient is one.

**Theorem 1.4 (Uniqueness among zero-constant integer series).**

$$\forall f: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(f\right) = 0) \implies (\operatorname{subst}\left(f, X - X^{2}\right) = X + f^{2}) \implies f = A$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CatalanShiftSquareModFour.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compose the equation for f with C to obtain f=C+subst(f,C) squared. The difference of two squares factors into a difference times a zero-constant sum. Induction on the degree therefore proves agreement of any two fixed points. No separate linear-coefficient hypothesis is needed.

**Theorem 1.5 (The first reduction).**

$$\operatorname{map}\left(\operatorname{intCast}\left(\operatorname{ZMod}\left(2\right)\right), A\right) = X$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CatalanShiftSquareModFour.mod_two_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reducing the exact generating equation modulo two gives an equation also satisfied by X. If the two series differed, choose their least differing coefficient. Degree contraction forces equality at that coefficient as well, a contradiction. Consequently every coefficient of A-X is even.

**Theorem 1.6 (The A393172 conjecture).**

$$\forall n: \mathbb{N}, (1 < n) \implies (((\operatorname{a}\left(n\right) \bmod 4 = 2) \iff (\exists k: \mathbb{N}, n = 2^{k})) \land ((\operatorname{a}\left(n\right) \bmod 4 = 0) \iff (\neg (\exists k: \mathbb{N}, n = 2^{k}))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CatalanShiftSquareModFour.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a393172-catalan-shift-square-mod-four` (proved) by `D5/S1/Recurrence/Invariants/CatalanShiftSquareModFour.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a393172-catalan-shift-square-mod-four","declaration_gid":"D5/S1/Recurrence/Invariants/CatalanShiftSquareModFour.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2026). *OEIS A393172, g.f. satisfying A(x-x^2) = x + A(x)^2*. URL: <https://oeis.org/A393172>.

*Commentary.*

Define the integer series H coefficientwise by dividing A-X by two. The exact equation becomes subst(H,X-X squared)=X squared+2XH+2H squared. Modulo two, composition with the reduced Catalan series gives H=C squared. Above degree one, C squared and C have the same coefficients. The binary_catalan theorem identifies coefficient one precisely at powers of two. Since a(n) is twice the corresponding coefficient of H, the two stated remainder equivalences follow.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/CatalanShiftSquareModFour.a`
- Truth anchor: `D5/S1/Recurrence/Invariants/CatalanShiftSquareModFour.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/CatalanShiftSquareModFour.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Invariants/CatalanShiftSquareModFour.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Invariants/CatalanShiftSquareModFour.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Invariants/CatalanShiftSquareModFour.mod_two_identity`
- Dependency: [D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity](CatalanCompositionSquareParity.md)
