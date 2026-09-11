# Signed Catalan Cubic Substitution Modulo Three

## Abstract

The coefficients of OEIS A386666 satisfy Hanna's ternary residue conjecture.

The equation and conjecture are recorded in hanna2025a386666. All indices are natural numbers. A denotes generatingSeries and has integer coefficients a; S denotes signedCatalanSeries over ZMod 3. The function p denotes distinctPowersOfThree. The operation subst(f,u) means composition f(u). All remainders in the conjecture are integer remainders.

**Definition 1.1 (The integral generating series).**

$$(A: \operatorname{PowerSeries}\left(\mathbb{Z}\right)) = \operatorname{choose}\left(\exists f: \operatorname{PowerSeries}\left(\mathbb{Z}\right), ((\operatorname{constantCoeff}\left(f\right) = 0) \land ((\operatorname{coeff}\left(1, f\right) = 1) \land ((f)^{2} = \operatorname{subst}\left(f, ((X)^{2} + 4 \cdot (f)^{3})\right))))\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/SignedCatalanCubicSubstitutionModThree.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Choose an integer series satisfying the displayed normalization and equation. Existence follows by constructing its compositional inverse B=XH. The normalized equation is H(X^2)=H^2+4X with H(0)=1. Frobenius modulo two makes every coefficient correction divisible by two, and each correction improves agreement by one degree.

**Definition 1.2 (The coefficient sequence).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, A\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/SignedCatalanCubicSubstitutionModThree.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sequence consists of the coefficients of A, including a(0)=0.

**Theorem 1.3 (The OEIS equation).**

$$(\operatorname{constantCoeff}\left(A\right) = 0) \land ((\operatorname{coeff}\left(1, A\right) = 1) \land ((A)^{2} = \operatorname{subst}\left(A, ((X)^{2} + 4 \cdot (A)^{3})\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/SignedCatalanCubicSubstitutionModThree.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Composing the equation for B with its two-sided compositional inverse gives A^2=A(X^2+4A^3). Reversion preserves the specified linear coefficient.

**Theorem 1.4 (Uniqueness with the specified normalization).**

$$\forall f: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(f\right) = 0) \implies ((\operatorname{coeff}\left(1, f\right) = 1) \implies (((f)^{2} = \operatorname{subst}\left(f, ((X)^{2} + 4 \cdot (f)^{3})\right)) \implies (f = A)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/SignedCatalanCubicSubstitutionModThree.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two normalized inverse factors, their first differing coefficient contributes twice to the difference of their squares. Substitution by X^2 uses only earlier coefficients. Cancellation of two forces agreement, and composing back proves uniqueness of A.

**Definition 1.5 (Distinct powers of three).**

$$\forall n: \mathbb{N}, \operatorname{p}\left(n\right) = \operatorname{if} \operatorname{all}\left(\operatorname{digits}\left(3, n\right), (d: \mathbb{N} \mapsto d \neq 2)\right) \operatorname{then} 1 \operatorname{else} 0$$

*Formalization.* `D5/S1/Recurrence/Invariants/SignedCatalanCubicSubstitutionModThree.distinctPowersOfThree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Boolean all test excludes the digit two from Nat.digits 3 n. The resulting indicator is the A039966 characterization in hanna2025a386666, including the empty digit list at zero.

**Definition 1.6 (The signed Catalan series).**

$$(S: \operatorname{PowerSeries}\left(\operatorname{ZMod}\left(3\right)\right)) = 1 - (1 + X) \cdot \operatorname{mk}\left((n: \mathbb{N} \mapsto (\operatorname{p}\left(n\right): \operatorname{ZMod}\left(3\right)))\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/SignedCatalanCubicSubstitutionModThree.signedCatalanSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficientwise series with coefficients p(n) is denoted D in the proof. Thus S=1-(1+X)D over ZMod 3.

**Theorem 1.7 (The signed Catalan identity and residues).**

$$\forall n: \mathbb{N}, (0 < n) \implies ((\operatorname{constantCoeff}\left(S\right) = 0) \land ((\operatorname{coeff}\left(1, S\right) = 1) \land ((S + (S)^{2} = X) \land (((S)^{2} = \operatorname{subst}\left(S, ((X)^{2} + (S)^{3})\right)) \land ((\operatorname{coeff}\left(3 \cdot n, S\right) = 2 \cdot (\operatorname{p}\left(n\right): \operatorname{ZMod}\left(3\right))) \land ((\operatorname{coeff}\left(3 \cdot n + 1, S\right) = (\operatorname{p}\left(n\right): \operatorname{ZMod}\left(3\right))) \land (\operatorname{coeff}\left(3 \cdot n + 2, S\right) = 2 \cdot (\operatorname{p}\left(n\right): \operatorname{ZMod}\left(3\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/SignedCatalanCubicSubstitutionModThree.signed_catalan_mod_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Ternary digits give p(3n)=p(n), p(3n+1)=p(n), and p(3n+2)=0. Hence D=(1+X)D(X^3). Frobenius and cancellation of the unit D imply (1+X)D^2=1, which yields S+S^2=X. Quadratic uniqueness then proves the cubic substitution identity. Reading coefficients of 1-(1+X)D gives the three residue formulas for positive n.

**Theorem 1.8 (Hanna's conjecture).**

$$\forall n: \mathbb{N}, (0 < n) \implies ((\operatorname{a}\left(3 \cdot n\right) \bmod 3 = 2 \cdot (\operatorname{p}\left(n\right): \mathbb{Z}) \bmod 3) \land ((2 \cdot \operatorname{a}\left(3 \cdot n + 1\right) \bmod 3 = 2 \cdot (\operatorname{p}\left(n\right): \mathbb{Z}) \bmod 3) \land (\operatorname{a}\left(3 \cdot n + 2\right) \bmod 3 = 2 \cdot (\operatorname{p}\left(n\right): \mathbb{Z}) \bmod 3)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/SignedCatalanCubicSubstitutionModThree.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a386666-signed-catalan-cubic-substitution-mod-three` (proved) by `D5/S1/Recurrence/Invariants/SignedCatalanCubicSubstitutionModThree.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a386666-signed-catalan-cubic-substitution-mod-three","declaration_gid":"D5/S1/Recurrence/Invariants/SignedCatalanCubicSubstitutionModThree.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2025). *OEIS A386666, g.f. satisfying A(x)^2 = A(x^2 + 4*A(x)^3)*. URL: <https://oeis.org/A386666>.

*Commentary.*

Reduction of the integral equation modulo three replaces four by one. Uniqueness identifies this reduction with S. Its coefficient formulas give each of the three asserted integer remainders.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/SignedCatalanCubicSubstitutionModThree.a`
- Truth anchor: `D5/S1/Recurrence/Invariants/SignedCatalanCubicSubstitutionModThree.distinctPowersOfThree`
- Truth anchor: `D5/S1/Recurrence/Invariants/SignedCatalanCubicSubstitutionModThree.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/SignedCatalanCubicSubstitutionModThree.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Invariants/SignedCatalanCubicSubstitutionModThree.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Invariants/SignedCatalanCubicSubstitutionModThree.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Invariants/SignedCatalanCubicSubstitutionModThree.signedCatalanSeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/SignedCatalanCubicSubstitutionModThree.signed_catalan_mod_three`
