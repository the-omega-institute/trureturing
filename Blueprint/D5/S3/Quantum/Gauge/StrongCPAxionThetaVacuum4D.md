# Strong CP vacua and the two-flavor axion potential

## Abstract

The two-flavor strong CP vacuum, the axion mass and quartic coupling, and the winding-number vacuum count.

The leading chiral mass potential reduces to a linear functional on the unit three-sphere of determinant-one unitary matrices. Its two nonzero coordinate coefficients fix the vacuum energy and, if their squared norm is positive, the unique minimizing field. The chiral model and the separate dilute instanton cosine have the same minimizing angle lattice.

**Definition 1.1 (Chiral potential with a theta angle).**

Lean statement: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.thetaChiralPotential`

*Formalization.* `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.thetaChiralPotential` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Grilli di Cortona, Edward Hardy, Javier Pardo Vega, and Giovanni Villadoro (2016). *The QCD axion, precisely*. DOI: [10.1007/JHEP01(2016)034](https://doi.org/10.1007/JHEP01(2016)034). URL: <https://arxiv.org/abs/1511.02867>.

*Commentary.*

Multiply the diagonal mass matrix by the complex phase with angle theta divided by two. The potential is the real trace of its product with the chiral field times minus the chiral constant and the squared pion decay constant.

**Definition 1.2 (Minimized chiral energy).**

Lean statement: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.qcdThetaEnergy`

*Formalization.* `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.qcdThetaEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Grilli di Cortona, Edward Hardy, Javier Pardo Vega, and Giovanni Villadoro (2016). *The QCD axion, precisely*. DOI: [10.1007/JHEP01(2016)034](https://doi.org/10.1007/JHEP01(2016)034). URL: <https://arxiv.org/abs/1511.02867>.

*Commentary.*

The energy is minus the chiral constant and squared pion decay constant times the square root of the sum of squared quark masses and twice their product times the cosine of theta.

**Definition 1.3 (Lifted strong CP angle).**

Lean statement: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.thetaBar`

*Formalization.* `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.thetaBar` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Grilli di Cortona, Edward Hardy, Javier Pardo Vega, and Giovanni Villadoro (2016). *The QCD axion, precisely*. DOI: [10.1007/JHEP01(2016)034](https://doi.org/10.1007/JHEP01(2016)034). URL: <https://arxiv.org/abs/1511.02867>.

*Commentary.*

Add the theta angle to a real lift of the determinant phase of the quark mass matrix.

**Theorem 1.4 (Zero-angle chiral potential).**

Lean statement: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.thetaChiralPotential_zero_eq_chiralPotential`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.thetaChiralPotential_zero_eq_chiralPotential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Grilli di Cortona, Edward Hardy, Javier Pardo Vega, and Giovanni Villadoro (2016). *The QCD axion, precisely*. DOI: [10.1007/JHEP01(2016)034](https://doi.org/10.1007/JHEP01(2016)034). URL: <https://arxiv.org/abs/1511.02867>.

*Commentary.*

At zero angle the complex phase is one, and the theta-dependent potential agrees with the two-flavor chiral potential.

**Theorem 1.5 (Strong CP angle under phase rotations).**

Lean statement: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.thetaBar_chiral_rotation_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.thetaBar_chiral_rotation_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Grilli di Cortona, Edward Hardy, Javier Pardo Vega, and Giovanni Villadoro (2016). *The QCD axion, precisely*. DOI: [10.1007/JHEP01(2016)034](https://doi.org/10.1007/JHEP01(2016)034). URL: <https://arxiv.org/abs/1511.02867>.

*Commentary.*

Phasing the two masses multiplies their determinant by the phase of the sum of the angles. Translating theta by minus this sum preserves the lifted strong CP angle. Multiplying a field on the left by opposite diagonal phases preserves its determinant. A common phase multiplies the determinant by the phase of twice the shared angle, and the corresponding compensating translation preserves the lifted angle.

**Theorem 1.6 (Lower bound over all chiral fields).**

Lean statement: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.thetaChiralPotential_ge_qcdThetaEnergy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.thetaChiralPotential_ge_qcdThetaEnergy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Grilli di Cortona, Edward Hardy, Javier Pardo Vega, and Giovanni Villadoro (2016). *The QCD axion, precisely*. DOI: [10.1007/JHEP01(2016)034](https://doi.org/10.1007/JHEP01(2016)034). URL: <https://arxiv.org/abs/1511.02867>.

*Commentary.*

For positive chiral constant and pion decay constant, every determinant-one unitary field has potential at least the stated vacuum energy. This bound holds for all real masses and angles.

**Theorem 1.7 (Explicit unique diagonal minimizer).**

Lean statement: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.qcdThetaEnergy_attained_on_diagonal_su2`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.qcdThetaEnergy_attained_on_diagonal_su2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Grilli di Cortona, Edward Hardy, Javier Pardo Vega, and Giovanni Villadoro (2016). *The QCD axion, precisely*. DOI: [10.1007/JHEP01(2016)034](https://doi.org/10.1007/JHEP01(2016)034). URL: <https://arxiv.org/abs/1511.02867>.

*Commentary.*

For positive chiral constant and pion decay constant and positive radicand, divide the mass sum times the half-angle cosine and the down-minus-up mass difference times the half-angle sine by the square root of the radicand. These give the real and imaginary parts of the first diagonal entry, with its conjugate in the second entry. Exactly that field attains the vacuum energy.

**Theorem 1.8 (Angle-independent massless-quark vacuum).**

Lean statement: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.massless_quark_theta_unobservable`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.massless_quark_theta_unobservable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Grilli di Cortona, Edward Hardy, Javier Pardo Vega, and Giovanni Villadoro (2016). *The QCD axion, precisely*. DOI: [10.1007/JHEP01(2016)034](https://doi.org/10.1007/JHEP01(2016)034). URL: <https://arxiv.org/abs/1511.02867>.

*Commentary.*

For positive chiral constant, pion decay constant and down-quark mass, the energy at vanishing up-quark mass is minus the chiral constant times the squared pion decay constant times the down-quark mass. The diagonal field with phases plus and minus half the angle in the up and down entries attains this value for every angle.

**Theorem 1.9 (CP-conserving minimum of the chiral energy).**

Lean statement: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.vafa_witten_cp_conserving_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.vafa_witten_cp_conserving_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Grilli di Cortona, Edward Hardy, Javier Pardo Vega, and Giovanni Villadoro (2016). *The QCD axion, precisely*. DOI: [10.1007/JHEP01(2016)034](https://doi.org/10.1007/JHEP01(2016)034). URL: <https://arxiv.org/abs/1511.02867>.

*Commentary.*

When the chiral constant, decay constant and quark masses are positive, the energy at zero angle is a global minimum. Equality holds exactly when the cosine of the angle is one, equivalently at integer multiples of two pi.

**Theorem 1.10 (Evenness, periodicity and the maximum).**

Lean statement: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.qcdThetaEnergy_periodic_and_even`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.qcdThetaEnergy_periodic_and_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Grilli di Cortona, Edward Hardy, Javier Pardo Vega, and Giovanni Villadoro (2016). *The QCD axion, precisely*. DOI: [10.1007/JHEP01(2016)034](https://doi.org/10.1007/JHEP01(2016)034). URL: <https://arxiv.org/abs/1511.02867>.

*Commentary.*

For positive chiral constant, decay constant and quark masses, the vacuum energy is even and has period two pi. At pi it attains its global maximum, which is minus the chiral constant times the squared decay constant and the absolute mass difference.

**Theorem 1.11 (Equal-mass degeneracy and cusp).**

Lean statement: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.dashen_degenerate_cusp_and_spontaneous_cp_breaking`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.dashen_degenerate_cusp_and_spontaneous_cp_breaking` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Grilli di Cortona, Edward Hardy, Javier Pardo Vega, and Giovanni Villadoro (2016). *The QCD axion, precisely*. DOI: [10.1007/JHEP01(2016)034](https://doi.org/10.1007/JHEP01(2016)034). URL: <https://arxiv.org/abs/1511.02867>.

*Commentary.*

For equal positive masses and positive chiral constant and decay constant, the energy is minus twice the chiral constant times the squared decay constant times the common mass and the absolute half-angle cosine. At pi the potential vanishes on the whole field group, including the pair of adjoint diagonal fields with entries plus and minus the imaginary unit. The right derivative at pi is minus the chiral constant times the squared decay constant times the common mass. The left derivative is its opposite, so the energy is nondifferentiable there.

**Theorem 1.12 (Differentiability for unequal positive masses).**

Lean statement: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.nondegenerate_smooth_at_pi`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.nondegenerate_smooth_at_pi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Grilli di Cortona, Edward Hardy, Javier Pardo Vega, and Giovanni Villadoro (2016). *The QCD axion, precisely*. DOI: [10.1007/JHEP01(2016)034](https://doi.org/10.1007/JHEP01(2016)034). URL: <https://arxiv.org/abs/1511.02867>.

*Commentary.*

For unequal positive quark masses the radicand stays positive at every angle. The energy is differentiable everywhere, and its derivative vanishes at pi.

**Theorem 1.13 (Chiral topological susceptibility).**

Lean statement: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.qcd_topological_susceptibility_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.qcd_topological_susceptibility_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Grilli di Cortona, Edward Hardy, Javier Pardo Vega, and Giovanni Villadoro (2016). *The QCD axion, precisely*. DOI: [10.1007/JHEP01(2016)034](https://doi.org/10.1007/JHEP01(2016)034). URL: <https://arxiv.org/abs/1511.02867>.

*Commentary.*

At positive decay constant and positive mass sum, the derivative at angle zero vanishes. The second derivative is the chiral constant times the squared decay constant times the mass product divided by the mass sum. Using the pion mass relation, this equals the mass product divided by the squared mass sum times the squared pion mass and squared decay constant.

**Definition 1.14 (Shifted axion potential).**

Lean statement: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.axionPotential`

*Formalization.* `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.axionPotential` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Grilli di Cortona, Edward Hardy, Javier Pardo Vega, and Giovanni Villadoro (2016). *The QCD axion, precisely*. DOI: [10.1007/JHEP01(2016)034](https://doi.org/10.1007/JHEP01(2016)034). URL: <https://arxiv.org/abs/1511.02867>.

*Commentary.*

Evaluate the chiral vacuum energy at the fixed angle plus the axion field divided by its decay constant.

**Theorem 1.15 (Peccei-Quinn relaxation and axion mass).**

Lean statement: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.peccei_quinn_relaxation_and_axion_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.peccei_quinn_relaxation_and_axion_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Grilli di Cortona, Edward Hardy, Javier Pardo Vega, and Giovanni Villadoro (2016). *The QCD axion, precisely*. DOI: [10.1007/JHEP01(2016)034](https://doi.org/10.1007/JHEP01(2016)034). URL: <https://arxiv.org/abs/1511.02867>.

*Commentary.*

For positive chiral constant, pion decay constant, axion decay constant and quark masses, the global minima are exactly the fields with effective angle in the integer multiples of two pi. The field given by minus the axion decay constant times the angle offset has effective angle zero. The squared axion mass is the second derivative there. Multiplying it by the squared axion decay constant gives the susceptibility, bounded above by a quarter of the squared pion mass times the squared pion decay constant, with equality exactly at equal quark masses. The axion mass times its decay constant equals the square root of the mass product divided by the mass sum, multiplied by the pion mass and its decay constant.

**Theorem 1.16 (Attractive quartic self-coupling).**

Lean statement: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.axion_quartic_self_coupling_exact_and_attractive`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.axion_quartic_self_coupling_exact_and_attractive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Grilli di Cortona, Edward Hardy, Javier Pardo Vega, and Giovanni Villadoro (2016). *The QCD axion, precisely*. DOI: [10.1007/JHEP01(2016)034](https://doi.org/10.1007/JHEP01(2016)034). URL: <https://arxiv.org/abs/1511.02867>.

*Commentary.*

At the relaxed field the fourth derivative is minus the squared axion mass over the squared axion decay constant times the ratio of the sum of squared quark masses minus their product to the squared mass sum. It is negative, strictly above minus the squared axion mass over the squared decay constant, and at most minus one quarter of that positive mass ratio. Equality in the upper bound holds exactly for equal quark masses.

**Definition 1.17 (Dilute instanton potential).**

Lean statement: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.instantonPotential`

*Formalization.* `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.instantonPotential` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Grilli di Cortona, Edward Hardy, Javier Pardo Vega, and Giovanni Villadoro (2016). *The QCD axion, precisely*. DOI: [10.1007/JHEP01(2016)034](https://doi.org/10.1007/JHEP01(2016)034). URL: <https://arxiv.org/abs/1511.02867>.

*Commentary.*

The cosine of topological charge times the theta angle carries a coefficient of minus twice the common weight times the exponential of minus the instanton action divided by the squared coupling.

**Theorem 1.18 (Normalized BPST gas potential).**

Lean statement: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.instanton_dilute_gas_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.instanton_dilute_gas_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Grilli di Cortona, Edward Hardy, Javier Pardo Vega, and Giovanni Villadoro (2016). *The QCD axion, precisely*. DOI: [10.1007/JHEP01(2016)034](https://doi.org/10.1007/JHEP01(2016)034). URL: <https://arxiv.org/abs/1511.02867>.

*Commentary.*

At positive weight, radius and coupling, the BPST action is eight pi squared and its charge is one. The exponential action factor is below one. The resulting cosine potential has period two pi and attains its minimum exactly at integer multiples of two pi.

**Definition 1.19 (Axion potential at integer winding).**

Lean statement: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.pqPotential`

*Formalization.* `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.pqPotential` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Grilli di Cortona, Edward Hardy, Javier Pardo Vega, and Giovanni Villadoro (2016). *The QCD axion, precisely*. DOI: [10.1007/JHEP01(2016)034](https://doi.org/10.1007/JHEP01(2016)034). URL: <https://arxiv.org/abs/1511.02867>.

*Commentary.*

Evaluate the chiral energy at the angle offset plus the field times the winding number divided by the PQ decay constant.

**Theorem 1.20 (Vacuum count on the PQ circle).**

Lean statement: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.domain_wall_vacuum_count_and_fa_invariance`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.domain_wall_vacuum_count_and_fa_invariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Grilli di Cortona, Edward Hardy, Javier Pardo Vega, and Giovanni Villadoro (2016). *The QCD axion, precisely*. DOI: [10.1007/JHEP01(2016)034](https://doi.org/10.1007/JHEP01(2016)034). URL: <https://arxiv.org/abs/1511.02867>.

*Commentary.*

For positive chiral parameters and decay constants and positive integer winding, the PQ potential equals the axion potential with effective decay constant given by the PQ constant divided by the winding. All periods are integer multiples of two pi times that effective constant. In any half-open interval of length two pi times the PQ constant, a finite index of size equal to the winding parametrizes the global minima injectively and surjectively. Beginning the interval at the relaxed field gives the expected consecutive lattice representatives. The product of the axion mass and its effective decay constant depends only on the pion and quark parameters.

## References

- Truth anchor: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.axionPotential`
- Truth anchor: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.axion_quartic_self_coupling_exact_and_attractive`
- Truth anchor: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.dashen_degenerate_cusp_and_spontaneous_cp_breaking`
- Truth anchor: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.domain_wall_vacuum_count_and_fa_invariance`
- Truth anchor: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.instantonPotential`
- Truth anchor: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.instanton_dilute_gas_bridge`
- Truth anchor: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.massless_quark_theta_unobservable`
- Truth anchor: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.nondegenerate_smooth_at_pi`
- Truth anchor: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.peccei_quinn_relaxation_and_axion_mass`
- Truth anchor: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.pqPotential`
- Truth anchor: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.qcdThetaEnergy`
- Truth anchor: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.qcdThetaEnergy_attained_on_diagonal_su2`
- Truth anchor: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.qcdThetaEnergy_periodic_and_even`
- Truth anchor: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.qcd_topological_susceptibility_exact`
- Truth anchor: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.thetaBar`
- Truth anchor: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.thetaBar_chiral_rotation_invariant`
- Truth anchor: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.thetaChiralPotential`
- Truth anchor: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.thetaChiralPotential_ge_qcdThetaEnergy`
- Truth anchor: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.thetaChiralPotential_zero_eq_chiralPotential`
- Truth anchor: `D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.vafa_witten_cp_conserving_minimum`
- Dependency: [D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D](ChiralSymmetrySkyrme4D.md)
- Dependency: [D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D](YangMillsBPSSelfDual4D.md)
