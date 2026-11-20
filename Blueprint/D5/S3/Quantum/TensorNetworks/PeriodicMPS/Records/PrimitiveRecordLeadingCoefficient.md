# The leading cross matrix of the primitive periodic collision

## Abstract

The leading cross matrix of the primitive periodic collision.

**Theorem 1.1 (The dominant mixed-transfer eigenvalue).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordLeadingCoefficient.collisionLambda_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordLeadingCoefficient.collisionLambda_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

In the ket-first convention λ = (1+i)(3+√41). The other modes are (1+i)(3−√41), 8i and −8. Their moduli are at most 8 and strictly below |λ|.

**Definition 1.2 (The complex rate per site).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordLeadingCoefficient.collisionPhaseRate`

*Formalization.* `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordLeadingCoefficient.collisionPhaseRate` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The rate γ = λ/√200 has modulus (3+√41)/10 and argument π/4.

**Definition 1.3 (The exact coefficient matrix).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordLeadingCoefficient.Sstar`

*Formalization.* `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordLeadingCoefficient.Sstar` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The 4 by 4 matrix S★ is written in the visible order 00, 01, 10, 11. Its rows are (a,b,b,c), (d,e,f,d), (d,f,e,d), (c,b,b,a). For s = √41, put δ = (25s−123)/656 and β = (697−75s)/1312. Then a = 1/4+iδ, b = 3s/164+is/41, c = β−iδ, d = 3s/164−is/41, e = 1/4−iδ and f = β+iδ.

**Theorem 1.4 (Readout of the dominant spectral projector).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordLeadingCoefficient.Sstar_mul_lambda_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordLeadingCoefficient.Sstar_mul_lambda_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For each visible pair p,q, λ² times S★[p,q] is the dominant insertion weight. The proof reads the trace of the ket-first two-site insertion against the mixed-transfer spectral projector. Splitting into Gaussian-integer and √41 parts gives exact entry checks.

**Theorem 1.5 (The cross reduction with its rate and phase removed).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordLeadingCoefficient.collision_flattening_cross_leading`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordLeadingCoefficient.collision_flattening_cross_leading` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Let Wᵦ be the normalized flattening of label b with two visible sites as rows and m hidden sites as columns. For every visible entry p,q, (W₀W₁†)[p,q]/γⁿ tends to S★[p,q] as m grows, with n = 2+m. Division by γⁿ removes both the decay and the phase. The three other modes vanish after dividing by the dominant mode.

**Theorem 1.6 (Trace of the leading matrix).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordLeadingCoefficient.Sstar_trace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordLeadingCoefficient.Sstar_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The exact matrix has tr S★ = 1. This fixes the leading trace amplitude in the same phase convention.

**Theorem 1.7 (Commutation with the observed density).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordLeadingCoefficient.Sstar_commutes_observed`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordLeadingCoefficient.Sstar_commutes_observed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The common marginal R = collisionMarginal satisfies RS★ = S★R. This equality is checked directly on entries in the visible basis.

**Theorem 1.8 (Exact weighted Hilbert–Schmidt coefficient).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordLeadingCoefficient.collision_weighted_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordLeadingCoefficient.collision_weighted_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The Gaussian-integer and √41 arithmetic gives Re tr(R⁻¹ S★S★†)/2 = (310625−46875√41)/16384, approximately 0.6395600201620616.

**Theorem 1.9 (Strict excess over one half).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordLeadingCoefficient.collision_weighted_coefficient_gt_half`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordLeadingCoefficient.collision_weighted_coefficient_gt_half` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The exact weighted trace exceeds 1/2. The proof compares √41 with 302433/46875 by squaring. The verified scope is the matrix limit and weighted trace. The complementary conditional-entropy and Helstrom prefactors require separate analytic theorems.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordLeadingCoefficient.Sstar`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordLeadingCoefficient.Sstar_commutes_observed`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordLeadingCoefficient.Sstar_mul_lambda_sq`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordLeadingCoefficient.Sstar_trace`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordLeadingCoefficient.collisionLambda_eq`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordLeadingCoefficient.collisionPhaseRate`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordLeadingCoefficient.collision_flattening_cross_leading`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordLeadingCoefficient.collision_weighted_coefficient`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordLeadingCoefficient.collision_weighted_coefficient_gt_half`
