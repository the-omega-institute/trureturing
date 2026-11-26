# Rational dependence of Robin clock labels

## Abstract

Dependent Robin clock bases admit a coprime common base and a quantitative logarithmic gap.

**Theorem 1.1 (Common-base classification and numerator divisibility).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/JointAxis/RationalClockDependence.clock_dependent_iff_common_base`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/JointAxis/RationalClockDependence.clock_dependent_iff_common_base` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural labels h, p and q with 0 < h, 2h ≤ p and q ≤ 3h, put α = 3p/(p + q) and β = 2p/(p + h) in the rationals. The bases are dependent exactly when α = tᴬ and β = tᴮ for a rational t > 1 and positive coprime A and B, with the B-th power of the reduced numerator of t dividing 2p.

Cancel the common factor of the exponents and take a common rational root using Bézout's identity. Clearing the second denominator then gives the divisor bound by coprimality of the reduced numerator and denominator.

**Theorem 1.2 (Lower bound for a nonzero dependent form).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/JointAxis/RationalClockDependence.dependent_clock_abs_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/JointAxis/RationalClockDependence.dependent_clock_abs_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same label bounds, a nonzero dependent form Ω has |Ω| ≥ log(4/3) log(2) / log(2p). The second base is at least 4/3, and numerator divisibility gives B log(2) ≤ log(2p). The form is the product of log(t) and the nonzero integer hA − qB.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/JointAxis/RationalClockDependence.clock_dependent_iff_common_base`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/JointAxis/RationalClockDependence.dependent_clock_abs_lower`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/JointAxisLogarithm](../JointAxisLogarithm.md)
