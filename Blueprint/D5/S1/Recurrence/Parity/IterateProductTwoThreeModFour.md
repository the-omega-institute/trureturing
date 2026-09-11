# Hanna's Two-Three Iterate Product Congruences

## Abstract

The unique integer series of OEIS A396099 satisfies all four congruence conjectures.

The entry cited in hanna2026a396099 defines A(x) by A(x)=x+A^2(x)A^3(x). Its FORMULA and PROG interpret the superscripts as compositional iterates. It conjectures oddness at every positive index, the repeating residues [1,3,3,1] beginning at index three, vanishing coefficients of A(A(x)) modulo four above degree two, and residue two for A(x)-x*A(A(A(x))) above degree two.

PowerSeries(R) is the formal power-series ring over R, X is its indeterminate, coeff extracts a coefficient, and mk constructs a series from its coefficient function. The operations iterate and mobius are those of CompositionalIterateCongruence: iterate(f,0)=X, iterate(f,k+1)=subst(iterate(f,k),f), and mobius(c) is X times the geometric series with coefficients c^n. Ring parameters implicit in Lean are displayed explicitly for these operations. The operation invOfUnit(g,1) is the formal inverse with prescribed constant unit one; the displayed denominator has constant coefficient one. All indices are natural numbers. Remainders of a and integer-series coefficients are integer remainders; the remainder of n is natural remainder.

**Definition 1.1 (The integer coefficient sequence).**

$$\begin{aligned}\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, \operatorname{approx}\left(\mathbb{Z}, n + 1\right)\right)\\\operatorname{approx}\left(\mathbb{Z}, 0\right) = 0\\\forall d: \mathbb{N}, \operatorname{approx}\left(\mathbb{Z}, d + 1\right) = X + (\operatorname{iterate}\left(\mathbb{Z}, \operatorname{approx}\left(\mathbb{Z}, d\right), 2\right)) \cdot (\operatorname{iterate}\left(\mathbb{Z}, \operatorname{approx}\left(\mathbb{Z}, d\right), 3\right))\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Parity/IterateProductTwoThreeModFour.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The local notation approx denotes iteration of the displayed transformation from the zero integer series. Its degree-n coefficient stabilizes by approximation n+1, defining a(n).

**Definition 1.2 (The integer generating series).**

$$\operatorname{generatingSeries} = \operatorname{mk}\left(\operatorname{a}\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/IterateProductTwoThreeModFour.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The generating series has coefficient function a.

**Theorem 1.3 (The equation and normalization).**

$$(\operatorname{constantCoeff}\left(\operatorname{generatingSeries}\right) = 0) \land ((\operatorname{coeff}\left(1, \operatorname{generatingSeries}\right) = 1) \land (\operatorname{generatingSeries} = X + (\operatorname{iterate}\left(\mathbb{Z}, \operatorname{generatingSeries}, 2\right)) \cdot (\operatorname{iterate}\left(\mathbb{Z}, \operatorname{generatingSeries}, 3\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/IterateProductTwoThreeModFour.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substitution preserves agreement below degree d for zero-constant series. The difference of the two iterate products splits into terms divisible by X^(d+1), since both factors have zero constant coefficient. This improvement stabilizes the approximations and proves the equation. The product contributes neither a constant nor a linear coefficient.

**Theorem 1.4 (Uniqueness of the integer solution).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(B\right) = 0) \implies ((B = X + (\operatorname{iterate}\left(\mathbb{Z}, B, 2\right)) \cdot (\operatorname{iterate}\left(\mathbb{Z}, B, 3\right))) \implies (B = \operatorname{generatingSeries}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/IterateProductTwoThreeModFour.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product comparison improves agreement of any two zero-constant fixed points by one degree. Induction proves equality of every coefficient, so every B satisfying the two hypotheses equals generatingSeries.

**Theorem 1.5 (The rational reduction modulo four).**

$$\operatorname{map}\left(\operatorname{intCastRingHom}\left(\operatorname{ZMod}\left(4\right)\right), \operatorname{generatingSeries}\right) = \operatorname{mobius}\left(\operatorname{ZMod}\left(4\right), 1\right) + ((2) \cdot ((X)^{4})) \cdot (\operatorname{invOfUnit}\left((1 - (X)) \cdot (1 + (X)^{2}), 1\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/IterateProductTwoThreeModFour.mod_four_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write D=(1-X)(1+X^2), N=X+X^3+2X^4, and F=N*invOfUnit(D,1). Substitute F into F*D=N, clear the unit denominator D^4, and reduce the polynomial identity in characteristic four. This proves subst(F,F)=X+2X^2; consequently iterate(F,3)=F+2F^2. Clearing D^2 proves F=X+(X+2X^2)(F+2F^2). Mapping commutes with substitution, so degree comparison identifies the reduced integer solution with F. A final unit cancellation gives the displayed rational form.

**Theorem 1.6 (Every positive-index term is odd).**

$$\forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{Odd}\left(\operatorname{a}\left(n\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/IterateProductTwoThreeModFour.all_odd` (`✓ std3`). ∎

*Citation.* Paul D. Hanna (2026). *OEIS A396099, g.f. satisfying A(x) = x + A^2(x)*A^3(x) (compositional iterates)*. URL: <https://oeis.org/A396099>.

*Commentary.*

The rational reduction is also X*mk(1)+2X^4(1+X)*subst(mk(1),X^4). The first two positive coefficients are one. The higher coefficients have residue one or three modulo four, so every positive-index integer coefficient is odd.

**Theorem 1.7 (The period-four coefficient pattern).**

$$\forall n: \mathbb{N}, (2 < n) \implies (\operatorname{a}\left(n\right) \bmod 4 = (\operatorname{if} (n \bmod 4 = 3 \lor n \bmod 4 = 2) \operatorname{then} 1 \operatorname{else} 3))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/IterateProductTwoThreeModFour.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a396099-iterate-product-two-three-mod-four` (proved) by `D5/S1/Recurrence/Parity/IterateProductTwoThreeModFour.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a396099-iterate-product-two-three-mod-four","declaration_gid":"D5/S1/Recurrence/Parity/IterateProductTwoThreeModFour.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2026). *OEIS A396099, g.f. satisfying A(x) = x + A^2(x)*A^3(x) (compositional iterates)*. URL: <https://oeis.org/A396099>.

*Commentary.*

The identity D*(1+X)=1-X^4 rewrites F as X*mk(1)+2X^4(1+X)*subst(mk(1),X^4). The last geometric series has coefficient one exactly at multiples of four. Coefficient extraction gives residue one when n mod 4 is two or three, and three otherwise, for every n greater than two. This is the pattern [1,3,3,1] starting at n=3 in hanna2026a396099.

**Theorem 1.8 (The second iterate above degree two).**

$$\forall n: \mathbb{N}, (2 < n) \implies (\operatorname{coeff}\left(n, \operatorname{iterate}\left(\mathbb{Z}, \operatorname{generatingSeries}, 2\right)\right) \bmod 4 = 0)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/IterateProductTwoThreeModFour.iterate_two_mod_four` (`✓ std3`). ∎

*Citation.* Paul D. Hanna (2026). *OEIS A396099, g.f. satisfying A(x) = x + A^2(x)*A^3(x) (compositional iterates)*. URL: <https://oeis.org/A396099>.

*Commentary.*

Map the second iterate through the canonical integer homomorphism to ZMod(4). Substitution commutes with mapping, and the rational composition identity gives X+2X^2. Every coefficient above degree two therefore has integer remainder zero modulo four.

**Theorem 1.9 (The shifted third-iterate difference).**

$$\forall n: \mathbb{N}, (2 < n) \implies (\operatorname{coeff}\left(n, \operatorname{generatingSeries} - ((X) \cdot (\operatorname{iterate}\left(\mathbb{Z}, \operatorname{generatingSeries}, 3\right)))\right) \bmod 4 = 2)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/IterateProductTwoThreeModFour.shift_mod_four` (`✓ std3`). ∎

*Citation.* Paul D. Hanna (2026). *OEIS A396099, g.f. satisfying A(x) = x + A^2(x)*A^3(x) (compositional iterates)*. URL: <https://oeis.org/A396099>.

*Commentary.*

Clearing D^2 and the unit 1-X gives F-X*(F+2F^2)=X+2X^3*mk(1). The third iterate is F+2F^2, so mapping the integer difference gives this geometric expression. Its coefficient is two in every degree greater than two.

## References

- Truth anchor: `D5/S1/Recurrence/Parity/IterateProductTwoThreeModFour.a`
- Truth anchor: `D5/S1/Recurrence/Parity/IterateProductTwoThreeModFour.all_odd`
- Truth anchor: `D5/S1/Recurrence/Parity/IterateProductTwoThreeModFour.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Parity/IterateProductTwoThreeModFour.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Parity/IterateProductTwoThreeModFour.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Parity/IterateProductTwoThreeModFour.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Parity/IterateProductTwoThreeModFour.iterate_two_mod_four`
- Truth anchor: `D5/S1/Recurrence/Parity/IterateProductTwoThreeModFour.mod_four_identity`
- Truth anchor: `D5/S1/Recurrence/Parity/IterateProductTwoThreeModFour.shift_mod_four`
- Dependency: [D5/S1/Recurrence/Invariants/CompositionalIterateCongruence](../Invariants/CompositionalIterateCongruence.md)
