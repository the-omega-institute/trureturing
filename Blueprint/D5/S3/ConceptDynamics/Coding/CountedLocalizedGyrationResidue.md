# Signed congruence for the fixed positive-lift cochain

## Abstract

CountedLocalizedGyrationResidue

**Theorem 1.1 (The dyadic cochain recovers the actual forward residue).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedLocalizedGyrationResidue.dyadicGyration_nonnegative`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedLocalizedGyrationResidue.dyadicGyration_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonzero period divisible by three, cast the nonnegative rectangular factors through the integers into the dyadic ring. Their dyadic gyration equals the reduction of the original ranked relative forward gyration. This is the bridge used by the relabel, positive-word and presentation-time comparisons.

**Theorem 1.2 (Signed congruence for the fixed positive-lift cochain).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedLocalizedGyrationResidue.canonicalLocalizedGyration_signed_agreement`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedLocalizedGyrationResidue.canonicalLocalizedGyration_signed_agreement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a commutative ring L equipped with reduction rho to ZMod of three to the power e plus one, each matrix entry is lifted to its natural residue plus that modulus. The canonical cochain is the same signed integer gyration polynomial evaluated at these strictly positive representatives, reduced modulo three. Here e is at least the three-adic valuation of the factorial of twice the period. Any signed integer pair with the same reductions gives the same value, by the explicit accepted integral numerator and the clearing-denominator theorem.

**Theorem 1.3 (One rectangular family satisfies the triangle).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedLocalizedGyrationResidue.canonicalLocalizedGyration_triangle`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedLocalizedGyrationResidue.canonicalLocalizedGyration_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Lift R, U and V separately. Products of their lifts have the correct reductions because rho and integer reduction are ring homomorphisms. Signed agreement compares the cochain on each product with its integer value even when an intermediate dimension vanishes. The nonnegative integer triangle then yields the rectangular localized triangle. The construction is uniform over all dimensions, including zero, and every nonzero period divisible by three.

Agreement with actual primitive-path forward gyration.

Let n and m be arbitrary natural dimensions, d a nonzero period with three dividing d (write hd for this divisibility), L any commutative ring, e a natural exponent at least the three-adic valuation of (2*d)!, and rho a ring homomorphism from L to ZMod of three to the power e plus one. For arbitrary natural counted matrices R of size n by m and S of size m by n, map their entries first to the integers and then to L. The canonicalLocalizedGyration value of this pair equals ZMod.castHom hd (ZMod 3) applied to relativeForwardGyration R S. Zero entries, empty dimensions and singular matrices remain allowed; no inverse or determinant condition is used.

Apply canonicalLocalizedGyration_signed_agreement to those matrices in L and the signed integer pair R.map (Nat.castRingHom ℤ), S.map (Nat.castRingHom ℤ). Entrywise map_intCast for rho supplies both reduction equalities, including zero entries. The accepted relativeForwardGyration_eq_order_types at Sum.elim of the R and S entries identifies the actual primitive-path offset sum with the natural orderTypeGyrationLift in ZMod d. Mapping to ZMod 3 commutes with the integer cast because three divides d. Finally Sum.elim of the integer-cast entries is the pointwise cast of the natural tuple; unfolding integerGyrationValue and using Ring.choose_natCast and Nat.cast_prod identifies signedGyrationLift with orderTypeGyrationLift. This derives the agreement for the same invariant and the full stated parameter range.

**Definition 1.4 (The fixed dyadic specialization).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedLocalizedGyrationResidue.dyadicGyration`

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedLocalizedGyrationResidue.dyadicGyration` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The canonical dyadic value uses the universal localization reduction at the three-adic valuation of the factorial of twice the period. Signed agreement and the rectangular triangle apply to this same specialization. The preceding derivation also identifies its nonnegative integer inputs with actual orbit gyration. The localization's integer embedding agrees with the embedding induced by its ring structure, by uniqueness of ring homomorphisms from the integers. No separate period or square wrapper is needed. These arguments use classical integer-valued polynomial congruences and localization; they assert no novelty, full mod-six law, image exhaustion, or original-h SGCC completion.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedLocalizedGyrationResidue.canonicalLocalizedGyration_signed_agreement`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedLocalizedGyrationResidue.canonicalLocalizedGyration_triangle`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedLocalizedGyrationResidue.dyadicGyration`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedLocalizedGyrationResidue.dyadicGyration_nonnegative`
- Dependency: [D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer](CountedPositiveTriangleLocalizedConsumer.md)
