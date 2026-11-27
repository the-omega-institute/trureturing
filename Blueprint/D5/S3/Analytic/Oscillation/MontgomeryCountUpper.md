# Uniform Montgomery upper bound from the count

## Abstract

A bounded error in the two-term ordinate count gives a uniform upper bound for the Montgomery pair sum.

Write c = 1/(2π) and M(Y) = cY(log(cY)−1). Let N(Y) count the positive ordinates through Y with their multiplicities. In G_Y(t), use every ordered pair through the same inclusive cutoff and the factor 4/(4+(γ_j−γ_k)²) times cos(t(γ_j−γ_k)).

**Theorem 1.1 (The normalized count).**

Lean statement: `D5/S3/Analytic/Oscillation/MontgomeryCountUpper.count_asymptotic_of_bounded_discrepancy`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/MontgomeryCountUpper.count_asymptotic_of_bounded_discrepancy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If |N(Y)−M(Y)| is bounded for all sufficiently large Y, then N(Y)/(Y log Y) tends to c. The linear term in M(Y) vanishes after the normalization.

**Theorem 1.2 (A uniform bound on the leading coefficient).**

Lean statement: `D5/S3/Analytic/Oscillation/MontgomeryCountUpper.pairSum_le_of_bounded_discrepancy`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/MontgomeryCountUpper.pairSum_le_of_bounded_discrepancy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each ε > 0, the same counting hypothesis gives G_Y(t) ≤ (2πc²+ε)Y(log Y)² for all sufficiently large Y and all real t.

Let the count error be bounded by D from a fixed A onward. For an interval of radius r centered at an ordinate through Y, bound the mass above A by a difference of inclusive counts. Move the lower cutoff left by 1/log Y, clamped at A, to include ordinates at the left endpoint. The contribution through A is at most N(A). The difference of the two smooth main terms is at most c log Y times the distance between the cutoffs. Over the level intervals of the Lorentz kernel, this gives a row bound of 2πc log Y + N(A) + 2D + c.

Bound each cosine by one, then sum the row bound with the outer multiplicities. The normalized count makes the resulting leading coefficient 2πc².

## References

- Truth anchor: `D5/S3/Analytic/Oscillation/MontgomeryCountUpper.count_asymptotic_of_bounded_discrepancy`
- Truth anchor: `D5/S3/Analytic/Oscillation/MontgomeryCountUpper.pairSum_le_of_bounded_discrepancy`
- Dependency: [D5/S3/Analytic/Oscillation/MontgomeryWindow](MontgomeryWindow.md)
- Dependency: [D5/S3/Fourier/Concentration/LorentzIntervalMass](../../Fourier/Concentration/LorentzIntervalMass.md)
