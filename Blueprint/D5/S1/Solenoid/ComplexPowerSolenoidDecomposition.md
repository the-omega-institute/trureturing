# Complex Power-Solenoid Decomposition

## Abstract

Compatible nonzero complex power threads split into one real logarithmic charge and one universal-solenoid phase thread.

**Theorem 1.1 (The logarithmic norm charge is conserved).**

$$\forall z: \operatorname{ComplexPowerThread}, m: \operatorname{PositiveNat},\ m \cdot \log(\operatorname{norm}\left(z_{m}\right)) = \operatorname{Q}\left(z\right).$$

*Proof.* Machine-checked in Lean as `D5/S1/Solenoid/ComplexPowerSolenoidDecomposition.logarithmic_charge_conservation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A complex power thread has nonzero coordinates z_m at every positive level and satisfies z_(mn)^n = z_m. Taking norms at the bonding law and applying Real.log_pow proves that m log(norm(z_m)) is independent of m. The conserved value Q(z) is its level-one value log(norm(z_1)). Explicit nonzero coordinates exclude the totalized Real.log zero branch.

Pinned Mathlib supplies Complex.norm_pow and Real.log_pow. Repository, digest, generalized, and in-flight searches found no existing compatible complex power tower or conserved logarithmic charge.

**Definition 1.2 (Complex power threads split into charge and phase).**

$$\operatorname{ComplexPowerThread} \equiv \mathbb{R} \times \mathcal{S},\quad z \mapsto (\operatorname{Q}\left(z\right), \operatorname{phase}\left(z\right)).$$

*Formalization.* `D5/S1/Solenoid/ComplexPowerSolenoidDecomposition.complexPowerThreadEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Normalize each coordinate by its positive norm. The resulting unit complex numbers preserve every bonding power and therefore define a point of the repository's UniversalSolenoid through Mathlib's AddCircle.homeomorphCircle. Conversely, a charge q and a solenoid phase theta assemble level m as exp(q/m) times the circle value of theta_m.

Real.exp_nat_mul proves compatibility of the radial factors, while AddCircle.toCircle_nsmul proves compatibility of the phases. The formal construction proves both inverse laws, so this is a constructive equivalence rather than a cardinality assertion.

The source statement is corrected to this supported algebraic core. It called the first factor R_Q without defining a different real structure and additionally asserted RH, maximal-compact, zero-thread, Gamma-factor, and trivial-zero claims that do not follow from the power-thread data. Those unsupported clauses are not claimed here.

**Theorem 1.3 (Every real charge has an explicit thread witness).**

$$\operatorname{Surjective}(Q).$$

*Proof.* Machine-checked in Lean as `D5/S1/Solenoid/ComplexPowerSolenoidDecomposition.logarithmicCharge_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each real q, assemble q with the zero universal-solenoid phase. Its level-one logarithmic norm is exactly q, giving the required witness and showing that the Archimedean factor is genuinely unrestricted.

**Theorem 1.4 (Zero charge is exactly the unit-norm locus).**

$$\forall z: \operatorname{ComplexPowerThread},\ \operatorname{Q}\left(z\right) = 0 \iff \forall m: \operatorname{PositiveNat},\ \operatorname{norm}\left(z_{m}\right) = 1.$$

*Proof.* Machine-checked in Lean as `D5/S1/Solenoid/ComplexPowerSolenoidDecomposition.logarithmicCharge_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Charge conservation and positivity of every coordinate norm show that zero charge forces log(norm(z_m)) = 0 and hence norm(z_m) = 1 at every level. Conversely, the level-one unit norm makes the charge zero. This supplies both directions of the compact-phase characterization.

## References

- Truth anchor: `D5/S1/Solenoid/ComplexPowerSolenoidDecomposition.complexPowerThreadEquiv`
- Truth anchor: `D5/S1/Solenoid/ComplexPowerSolenoidDecomposition.logarithmicCharge_eq_zero_iff`
- Truth anchor: `D5/S1/Solenoid/ComplexPowerSolenoidDecomposition.logarithmicCharge_surjective`
- Truth anchor: `D5/S1/Solenoid/ComplexPowerSolenoidDecomposition.logarithmic_charge_conservation`
- Dependency: [D5/S1/Dynamics/UniversalSolenoid](../Dynamics/UniversalSolenoid.md)
