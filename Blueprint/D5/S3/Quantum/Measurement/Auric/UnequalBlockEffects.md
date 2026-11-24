# Three effects with ordered missing-support prices

## Abstract

Attained spectral entropy with unequal rank caps

**Theorem 1.1 (Attained maximum for normalized weights).**

Lean statement: `D5/S3/Quantum/Measurement/Auric/UnequalBlockEffects.isGreatest_direct`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Auric/UnequalBlockEffects.isGreatest_direct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take three complex positive semidefinite effects that sum to identity on a finite carrier of dimension d. Each effect has rank at most its own cap mⱼ and real trace τⱼ. Put ℓⱼ = max(d − mⱼ, 0), assume their sum is at most d, and let b be the difference. For positive normalized weights w₀ ≥ w₁ ≥ w₂, put wⱼ on the common column and wⱼ/(1 − wᵢ) on missing-type column i for each j ≠ i. The excluded row i is zero. The trace assumption requires τⱼ to be the weighted row mass with the stated multiplicities.

The total of −x log x over the three spectra has a greatest value. It equals the sum of the scalar entropies of the missing-type columns with multiplicities ℓᵢ, plus b times the entropy of the common column. Diagonal effects realize the allocation.

Select ℓⱼ zero eigenvectors of each effect. Pad the spans of successive prefixes to a nested flag, then take differences of its orthogonal projections. The diagonal overlaps of these layers in each effect eigenbasis give the weights for the scalar supporting lines. Each selected zero eigenvector has all its layer mass in its flag prefix, so the ordered intercepts bound the excluded contribution from below. The linear terms sum using the prescribed traces and the identity sum of the three effects. The bound allows arbitrary intersections among the original kernels and holds when a layer has zero dimension.

**Theorem 1.2 (Attained complementary entropy with ordered scales).**

Lean statement: `D5/S3/Quantum/Measurement/Auric/UnequalBlockEffects.isGreatest_complement`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Auric/UnequalBlockEffects.isGreatest_complement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the same rank caps, real traces, PSD conditions and identity sum. The objective is the sum of φ(x) = −(1 − x) log(1 − x) over the three spectra. Fix a positive multiplier for each row and positive nondecreasing scales for the three missing column types and the common type. Every allowed entry is the maximum of zero and one minus the product of its row multiplier and column scale. An excluded entry is zero. Assume each column sums to one and the weighted row sums are the prescribed traces.

The scalar allocation attains the greatest spectral sum. A supporting line at each allowed entry uses the logarithm of the product plus one as its slope. The zero cutoff supplies the supporting line at an endpoint, including for excluded entries when the product is at least one. Increasing column scales decrease the intercepts, which supplies the ordering used in the same projection argument.

**Theorem 1.3 (Exact maximum for caps 3, 4, 4).**

Lean statement: `D5/S3/Quantum/Measurement/Auric/UnequalBlockEffects.isGreatest_three_four_four`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Auric/UnequalBlockEffects.isGreatest_three_four_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In dimension 5 take rank caps (3, 4, 4) and real traces (15/11, 20/11, 20/11). With φ(x) = −x log x and a = (√565 − 5)/18, the greatest total spectral entropy is 4φ(1/2) + 2[φ(a/(a+1)) + φ(1/(a+1))] + φ(a/(a+2)) + 2φ(1/(a+2)).

The weights proportional to (a, 1, 1) give the required traces. The polynomial equation 9a² + 5a − 15 = 0 verifies the mass of the first row, and the other two masses are equal by symmetry. The layers have multiplicities 2, 1, 1 and 1.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/Auric/UnequalBlockEffects.isGreatest_complement`
- Truth anchor: `D5/S3/Quantum/Measurement/Auric/UnequalBlockEffects.isGreatest_direct`
- Truth anchor: `D5/S3/Quantum/Measurement/Auric/UnequalBlockEffects.isGreatest_three_four_four`
