# Tensor Algebra and Behavior Products

## Abstract

An algebra tensor decomposition does not decide whether admitted behavior is a product; constrained and unconstrained residue systems give the contrast.

**Theorem 1.1 (Residue admission is a product exactly for coprime moduli).**

$$\forall m, n \in \mathbb{N},\\\operatorname{BehaviorProduct}(J_{m, n}) \iff \gcd(m, n) = 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Fibers/TensorAlgebraBehaviorSeparation.joint_residue_admission_product_iff_coprime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Behavior product is the named minimal test that the admitted pairs equal the product of their two marginal admission sets. Each marginal of the integer residue readout is the full local factor.

The compatible joint image is therefore a behavior product exactly when it is the full direct product, which the reused FPOD 107.1 criterion identifies with coprimality. No primality is assumed.

**Theorem 1.2 (Tensor algebra decomposition does not force behavior decomposition).**

$$\operatorname{PrimeFactorCount}(6) = 2 \land \operatorname{TensorBijective}(6) \land \operatorname{ProductState}(2, 2) \land \operatorname{FactorwiseUpdate}(2, 2) \land \operatorname{FactorwiseReadout}(2, 2) \land \neg\operatorname{NoCrossConstraint}(J_{2, 2}) \land \neg\operatorname{BehaviorProduct}(J_{2, 2}).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Fibers/TensorAlgebraBehaviorSeparation.tensor_algebra_decomposition_does_not_force_behavior_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The window M=6 has two prime-power factors, and the imported algebra factorization is bijective. Independently, the behavior state is a product and both its update and readout are identity maps.

Its admitted pairs are the repeated modulus-two residue image. FPOD 107.1 makes this a strict compatible subobject, so precisely the no-cross-factor-constraint premise fails and behavior is not a product. FPOD 107.1 itself contains no algebra statement.

**Theorem 1.3 (All four premises yield the product control).**

$$\operatorname{PrimeFactorCount}(6) = 2 \land \operatorname{TensorBijective}(6) \land \operatorname{ProductState}(2, 3) \land \operatorname{FactorwiseUpdate}(2, 3) \land \operatorname{FactorwiseReadout}(2, 3) \land \operatorname{NoCrossConstraint}(J_{2, 3}) \land \operatorname{BehaviorProduct}(J_{2, 3}).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Fibers/TensorAlgebraBehaviorSeparation.all_four_premises_give_behavior_product_control` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Keep the same two-factor M=6 algebra decomposition and use the coprime residue factors two and three. The product state, identity update, and identity readout meet the first three premises, while coprimality makes admission unrestricted.

The behavior admission is consequently a product. The Lean audit also checks empty and singleton carriers, constant, identity, and zero maps, zero moduli, one tensor factor, and the one-by-one matrix algebra.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Fibers/TensorAlgebraBehaviorSeparation.all_four_premises_give_behavior_product_control`
- Truth anchor: `D5/S3/ConceptDynamics/Fibers/TensorAlgebraBehaviorSeparation.joint_residue_admission_product_iff_coprime`
- Truth anchor: `D5/S3/ConceptDynamics/Fibers/TensorAlgebraBehaviorSeparation.tensor_algebra_decomposition_does_not_force_behavior_product`
- Dependency: [D5/S3/Factorization/PrimePowers/CompatibleResidueJointImage](../../Factorization/PrimePowers/CompatibleResidueJointImage.md)
- Dependency: [D5/S3/ObserverMemory/PrimePowerTensorTower](../../ObserverMemory/PrimePowerTensorTower.md)
