# Rational Coset Energy Bounds and an Attained Minimum

## Abstract

Rational Coset Energy Bounds and an Attained Minimum

For arbitrary rational mu, q_mu(gamma)=(gamma+mu)^T G (gamma+mu)/2 and weight(gamma,d)=oscillatorEnergy(d)+q_mu(gamma). Positive definiteness is imposed only on the original real Gram matrix. A common positive denominator s and integral nu with s mu=nu give the injective map gamma -> s gamma+nu and the exact identity q_mu(gamma)=chargeEnergy(s gamma+nu)/s^2. Existing integral charge sublevels and oscillator sublevels give all rational finite sublevels and exact finite fibers. Minimizing on the nonempty finite sublevel below q_mu(0) constructs an attained nonnegative GLOBAL minimum; no minimizer is assumed and no uniqueness is claimed. These arithmetic statements do not need beta, duality or inverse-Gram data.

Classical construction context: Bakalov-Kac, math/0402315v1, section 4.1. The imported Sugawara architecture retains Kalle Kytola's Apache-2.0 attribution and VirasoroProject revision 5ff4245383b2cdd4eea7a0524bc1274c32041eb4. The finite reductions and actual-action connections are native mathematical proofs; no external novelty is asserted.

**Definition 1.1 (pairing).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy.pairing`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy.pairing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rational bilinear form is the finite sum x_i G_ij y_j.

**Definition 1.2 (chargeWeight).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy.chargeWeight`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy.chargeWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

q_mu(gamma) is one half of the ORIGINAL rational Gram norm of gamma+mu.

**Definition 1.3 (weight).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy.weight`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A complete carrier label has rational weight oscillatorEnergy(d)+q_mu(gamma).

**Theorem 1.4 (common denominator).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy.common_denominator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy.common_denominator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exist s>0 and integral nu with s mu_i=nu_i in every coordinate. The empty product gives s=1 in rank zero.

**Definition 1.5 (clearedCharge).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy.clearedCharge`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy.clearedCharge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integral charge map is phi(gamma)=s gamma+nu.

**Theorem 1.6 (clearedCharge injective).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy.clearedCharge_injective`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy.clearedCharge_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A positive common denominator makes phi injective on the entire integral charge lattice.

**Theorem 1.7 (chargeWeight cleared).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy.chargeWeight_cleared`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy.chargeWeight_cleared` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact denominator clearing gives q_mu(gamma)=chargeEnergy(phi(gamma))/s^2, with no integral-energy evaluation on a nonintegral charge.

**Theorem 1.8 (chargeWeight nonneg).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy.chargeWeight_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy.chargeWeight_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive definiteness of the ORIGINAL real Gram matrix makes every rational shifted charge weight nonnegative.

**Theorem 1.9 (charge sublevel finite).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy.charge_sublevel_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy.charge_sublevel_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every rational charge sublevel is finite by injection into an existing integral charge-energy sublevel.

**Theorem 1.10 (sublevel finite).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy.sublevel_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy.sublevel_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every rational total-energy sublevel is finite by the product of a charge sublevel and the existing oscillator sublevel.

**Theorem 1.11 (attained minimum).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy.attained_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy.attained_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exists an actual charge attaining a nonnegative GLOBAL rational minimum. It is constructed from the nonempty finite sublevel below q_mu(0). No minimum or uniqueness premise is imposed.

**Theorem 1.12 (fiber finite).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy.fiber_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy.fiber_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every exact rational energy fiber of the full charge/oscillator label set is finite under positive original Gram.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy.attained_minimum`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy.chargeWeight`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy.chargeWeight_cleared`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy.chargeWeight_nonneg`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy.charge_sublevel_finite`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy.clearedCharge`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy.clearedCharge_injective`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy.common_denominator`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy.fiber_finite`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy.pairing`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy.sublevel_finite`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy.weight`
- Dependency: [D5/S3/VertexAlgebra/LatticeEnergyGrading](../LatticeEnergyGrading.md)
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeDualCosetModule](LatticeDualCosetModule.md)
