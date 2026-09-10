# Theta Self-Composition Modulo Four

## Abstract

The positive coefficients of OEIS A378581 are two modulo four exactly at square degrees.

Paul D. Hanna's entry hanna2025a378581 defines the integer series A by A(x*A(x))=theta_3(x), where theta_3(x) is one plus twice the sum of x^(j^2) over positive integers j. It conjectures that positive square degrees have coefficient two modulo four and all other positive degrees have coefficient divisible by four.

All indices are natural numbers. PowerSeries(Z) is the ring of integer formal power series, X is its indeterminate, coeff(n,F) extracts a coefficient, and mk constructs a series from its coefficient function. In the formulas subst(F,U) means F(U), with the outer series first. IsSquare(n) means that n is the square of a natural number. The map operation applies its ring homomorphism to every coefficient; all remainders in the final formula are integer remainders.

**Definition 1.1 (The formal theta series).**

$$\operatorname{thetaSeries} = \operatorname{mk}\left((n: \mathbb{N} \mapsto \operatorname{if} (n = 0) \operatorname{then} 1 \operatorname{else} (\operatorname{if} (\operatorname{IsSquare}\left(n\right)) \operatorname{then} 2 \operatorname{else} 0))\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour.thetaSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient function includes the constant term separately from the positive square degrees.

**Theorem 1.2 (The theta coefficients).**

$$\forall n: \mathbb{N}, \operatorname{coeff}\left(n, \operatorname{thetaSeries}\right) = \operatorname{if} (n = 0) \operatorname{then} 1 \operatorname{else} (\operatorname{if} (\operatorname{IsSquare}\left(n\right)) \operatorname{then} 2 \operatorname{else} 0)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour.coeff_thetaSeries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Extracting a coefficient from mk gives the defining conditional expression.

**Definition 1.3 (The stabilized integer coefficients).**

$$\begin{aligned}\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, \operatorname{approximation}\left(n + 1\right)\right)\\\operatorname{approximation}\left(0\right) = 1\\\forall d: \mathbb{N}, \operatorname{approximation}\left(d + 1\right) = (\operatorname{thetaSeries} + \operatorname{approximation}\left(d\right)) - \operatorname{subst}\left(\operatorname{approximation}\left(d\right), X \cdot \operatorname{approximation}\left(d\right)\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The auxiliary approximation starts at one and applies the displayed correction. Each approximation has constant coefficient one. Agreement below degree d improves to agreement below degree d+1, so the diagonal coefficient defines the sequence.

**Definition 1.4 (The integer generating series).**

$$\operatorname{generatingSeries} = \operatorname{mk}\left(\operatorname{a}\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The generating series has coefficient function a.

**Theorem 1.5 (The defining functional equation).**

$$(\operatorname{constantCoeff}\left(\operatorname{generatingSeries}\right) = 1) \land (\operatorname{subst}\left(\operatorname{generatingSeries}, X \cdot \operatorname{generatingSeries}\right) = \operatorname{thetaSeries})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If F and G agree below degree d and G has constant coefficient one, then at every degree n at most d the difference between F(X*F) and G(X*G) equals the difference between their degree-n coefficients. The substitution arguments agree through degree d. In the remaining outer difference, lower terms vanish and the degree-n term has multiplier one. The correction therefore contracts coefficient agreement. Its stabilized series is a fixed point, giving the equation.

**Theorem 1.6 (Uniqueness of the integer solution).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(B\right) = 1) \implies ((\operatorname{subst}\left(B, X \cdot B\right) = \operatorname{thetaSeries}) \implies (B = \operatorname{generatingSeries}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every solution is a fixed point of the correction. Induction on degree using the same contraction proves equality of all coefficients.

**Theorem 1.7 (The full series identity modulo four).**

$$\operatorname{map}\left(\operatorname{intCastRingHom}\left(\operatorname{ZMod}\left(4\right)\right), \operatorname{generatingSeries}\right) = \operatorname{map}\left(\operatorname{intCastRingHom}\left(\operatorname{ZMod}\left(4\right)\right), \operatorname{thetaSeries}\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour.mod_four_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write the reduced theta series as R=1+2*S. In ZMod(4), twice X*R equals twice X. More generally, c*U=c*V implies c*U^k=c*V^k by induction on k, and the coefficient formula for substitution then gives c*F(U)=c*F(V) for zero-constant U and V. Apply this with c=2 to obtain R(X*R)=R. Mapping the integer equation preserves substitution, and uniqueness over ZMod(4) identifies the two series.

**Theorem 1.8 (Hanna's A378581 conjecture).**

$$\forall n: \mathbb{N}, (0 < n) \implies ((((\operatorname{a}\left(n\right) \bmod 4 = 2) \iff (\operatorname{IsSquare}\left(n\right))) \land ((\operatorname{a}\left(n\right) \bmod 4 = 0) \iff (\neg (\operatorname{IsSquare}\left(n\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a378581-theta-self-composition-mod-four` (proved) by `D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a378581-theta-self-composition-mod-four","declaration_gid":"D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2025). *OEIS A378581, g.f. satisfying A(x*A(x)) = theta_3(x)*. URL: <https://oeis.org/A378581>.

*Commentary.*

At positive degree, the theta coefficient is two at a square and zero otherwise. The series identity and the integer-cast remainder equivalence give both biconditionals, as conjectured in hanna2025a378581.

## References

- Truth anchor: `D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour.a`
- Truth anchor: `D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour.coeff_thetaSeries`
- Truth anchor: `D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour.mod_four_identity`
- Truth anchor: `D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour.thetaSeries`
