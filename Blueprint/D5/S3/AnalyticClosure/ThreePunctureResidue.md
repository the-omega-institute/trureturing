# Residues at zero, one and infinity

## Abstract

Three-puncture residue balance and its two coordinate changes.

**Definition 1.1 (Finite principal part).**

Lean statement: `D5/S3/AnalyticClosure/ThreePunctureResidue.principalPart`

*Formalization.* `D5/S3/AnalyticClosure/ThreePunctureResidue.principalPart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The length-n principal part at a is the sum of cⱼ(z − a)^(−j−1) for 0 ≤ j < n, indexed from the simple pole.

**Definition 1.2 (Simple-pole coefficient).**

Lean statement: `D5/S3/AnalyticClosure/ThreePunctureResidue.simpleCoeff`

*Formalization.* `D5/S3/AnalyticClosure/ThreePunctureResidue.simpleCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient of (z − a)⁻¹ is c₀ for a nonempty principal part and zero for the empty part.

**Theorem 1.3 (The linear term of the inverse-coordinate remainder).**

Lean statement: `D5/S3/AnalyticClosure/ThreePunctureResidue.deriv_inverse_remainder`

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/ThreePunctureResidue.deriv_inverse_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G be holomorphic off zero and one and have finite principal parts with analytic remainders at zero, one and in the scalar germ G(u⁻¹) at u = 0. Subtract the two finite principal parts and the polynomial in z determined by the inverse-coordinate principal part. The remainder extends through zero and one and has a limit at infinity, hence is constant by Liouville. In the inverse coordinate, the coefficients of u from the subtracted finite parts are their simple-pole coefficients. Their sum is the derivative at zero of the scalar inverse-coordinate remainder.

**Theorem 1.4 (Residue balance from the scalar inverse germ).**

Lean statement: `D5/S3/AnalyticClosure/ThreePunctureResidue.residue_sum`

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/ThreePunctureResidue.residue_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume G is holomorphic on ℂ ∖ {0, 1} and has finite Laurent expansions with analytic remainders at zero, one and in the scalar germ G(u⁻¹) at zero. For the differential G(z) dz the pullback by z = u⁻¹ multiplies G(u⁻¹) by −u⁻². Its residue at infinity is therefore minus the derivative of the analytic scalar remainder at zero. The three residues sum to zero. `D5/S3/AnalyticClosure/ThreePunctureResidue.deriv_inverse_remainder`

**Theorem 1.5 (Inversion of the differential).**

Lean statement: `D5/S3/AnalyticClosure/ThreePunctureResidue.inverse_differential_principalPart`

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/ThreePunctureResidue.inverse_differential_principalPart` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the scalar germ G(u⁻¹) has a finite Laurent expansion with remainder analytic at u = 0. The inversion Jacobian shifts the scalar principal part by two powers and negates it. The constant term of the scalar remainder then contributes a double pole and the linear term contributes the simple pole.

**Definition 1.6 (Iterate coordinate at one).**

Lean statement: `D5/S3/AnalyticClosure/ThreePunctureResidue.aChart`

*Formalization.* `D5/S3/AnalyticClosure/ThreePunctureResidue.aChart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For u = z − 1 the iterate residue coordinate is t = −u/(1 + u).

**Theorem 1.7 (Simple-pole coefficient in the iterate coordinate).**

Lean statement: `D5/S3/AnalyticClosure/ThreePunctureResidue.aChart_residue_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/ThreePunctureResidue.aChart_residue_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume F has a finite Laurent expansion with remainder analytic at t = 0. Pull back the differential F(t) dt by t = −u/(1 + u). A simple pole becomes u⁻¹ − (1 + u)⁻¹, and each pole of order j ≥ 2 becomes a constant times u^(−j)(1 + u)^(j−2). Its finite expansion has only poles of order at least two. The pulled-back analytic remainder stays analytic, so the simple coefficient is preserved.

**Theorem 1.8 (Independence of the Laurent presentation).**

Lean statement: `D5/S3/AnalyticClosure/ThreePunctureResidue.simpleCoeff_unique`

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/ThreePunctureResidue.simpleCoeff_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two finite Laurent presentations of the same punctured germ, with remainders analytic at zero, have the same simple coefficient. Clear both pole bounds and compare the Taylor coefficients of the resulting analytic germs.

**Theorem 1.9 (Using any Laurent presentation of the inverse differential).**

Lean statement: `D5/S3/AnalyticClosure/ThreePunctureResidue.residue_sum_of_pullback_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/ThreePunctureResidue.residue_sum_of_pullback_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume G is holomorphic on ℂ ∖ {0, 1} and has finite Laurent expansions at zero and one with remainders analytic at their respective centers. Assume both G(u⁻¹) and −u⁻²G(u⁻¹) have finite Laurent expansions with remainders analytic at u = 0. By uniqueness of the simple coefficient, the simple coefficients at zero and one and that of −u⁻²G(u⁻¹) sum to zero. `D5/S3/AnalyticClosure/ThreePunctureResidue.simpleCoeff_unique`

**Theorem 1.10 (Residue balance from three differential expansions).**

Lean statement: `D5/S3/AnalyticClosure/ThreePunctureResidue.residue_sum_of_differential_expansions`

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/ThreePunctureResidue.residue_sum_of_differential_expansions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume G is holomorphic on ℂ ∖ {0, 1}. Supply finite Laurent expansions for G at zero and one and for −u⁻²G(u⁻¹) at u = 0, each with a remainder analytic at its center. Multiplication by −u² shifts the inverse differential coefficients by two exponents and absorbs its simple and double poles into the analytic scalar remainder. The three differential simple coefficients sum to zero. `D5/S3/AnalyticClosure/ThreePunctureResidue.residue_sum_of_pullback_expansion`

## References

- Truth anchor: `D5/S3/AnalyticClosure/ThreePunctureResidue.aChart`
- Truth anchor: `D5/S3/AnalyticClosure/ThreePunctureResidue.aChart_residue_invariant`
- Truth anchor: `D5/S3/AnalyticClosure/ThreePunctureResidue.deriv_inverse_remainder`
- Truth anchor: `D5/S3/AnalyticClosure/ThreePunctureResidue.deriv_inverse_remainder`
- Truth anchor: `D5/S3/AnalyticClosure/ThreePunctureResidue.inverse_differential_principalPart`
- Truth anchor: `D5/S3/AnalyticClosure/ThreePunctureResidue.principalPart`
- Truth anchor: `D5/S3/AnalyticClosure/ThreePunctureResidue.residue_sum`
- Truth anchor: `D5/S3/AnalyticClosure/ThreePunctureResidue.residue_sum_of_differential_expansions`
- Truth anchor: `D5/S3/AnalyticClosure/ThreePunctureResidue.residue_sum_of_pullback_expansion`
- Truth anchor: `D5/S3/AnalyticClosure/ThreePunctureResidue.residue_sum_of_pullback_expansion`
- Truth anchor: `D5/S3/AnalyticClosure/ThreePunctureResidue.simpleCoeff`
- Truth anchor: `D5/S3/AnalyticClosure/ThreePunctureResidue.simpleCoeff_unique`
- Truth anchor: `D5/S3/AnalyticClosure/ThreePunctureResidue.simpleCoeff_unique`
