# Monomial insertion energy

## Abstract

Joint occupation energies on the original finite product-activity law.

**Definition 1.1 (The original law).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/MonomialInsertionEnergy.mass`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/MonomialInsertionEnergy.mass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each configuration has the product of its occupied activities divided by the sum over the same finite family. The definition uses total field division. A positive probability interpretation additionally requires nonempty support and positive real activities.

**Definition 1.2 (Joint occupation).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/MonomialInsertionEnergy.monomial`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/MonomialInsertionEnergy.monomial` (`✓ std3`).

*Citation.* Tianshun Miao; Yitong Yin (2026). *Sampling Matchings in Near-linear Time*. URL: <https://arxiv.org/abs/2609.21936v1>.

*Commentary.*

The Boolean monomial is one exactly when every marked site is occupied. Infeasible marked sets give the zero function on the legal carrier.

**Definition 1.3 (Actual joint moment).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/MonomialInsertionEnergy.moment`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/MonomialInsertionEnergy.moment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the moment under the original finite product law. Marking sites does not substitute a new law or a smaller generator.

**Definition 1.4 (Empty insertion endpoints).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/MonomialInsertionEnergy.insertionStates`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/MonomialInsertionEnergy.insertionStates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A permitted edge starts at a configuration lacking the selected site and ends at its insertion in the same family.

**Definition 1.5 (Once-counted heat-bath form).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/MonomialInsertionEnergy.dirichlet`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/MonomialInsertionEnergy.dirichlet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiply the two function increments along every permitted insertion by the original empty-endpoint mass, site weight and activity heat-bath factor. Each site edge is counted once.

**Theorem 1.6 (Every joint occupation energy).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/MonomialInsertionEnergy.monomial_dirichlet`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/MonomialInsertionEnergy.monomial_dirichlet` (`✓ std3`). ∎

*Citation.* Tianshun Miao; Yitong Yin (2026). *Sampling Matchings in Near-linear Time*. URL: <https://arxiv.org/abs/2609.21936v1>.

*Commentary.*

For a finite family closed under erasing occupied sites, the bilinear energy of two monomials is the union moment times the sum of the occupied-site deletion coefficients on their common updated sites. Insertion and erasure identify the same edges, and only a common marked site changes both monomials.

Miao and Yin give the positive downward-closed unit-deletion monomial calculation in Section 3.2, equations (13), (21) and (22). The present identity uses the stipulated site heat-bath coefficients and extends the finite algebra to arbitrary field activities, including zeros under total division. It does not introduce a new general monomial energy principle.

Disjoint marked sets have zero bilinear flip energy even when their covariance is nonzero. For a positive real coherent preparation, the union moments give the tangent Gram matrix and this form gives its parent-energy matrix. This mathematical correspondence supplies neither a physical energy scale, state preparation nor a joint phase-control protocol.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/MonomialInsertionEnergy.dirichlet`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/MonomialInsertionEnergy.insertionStates`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/MonomialInsertionEnergy.mass`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/MonomialInsertionEnergy.moment`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/MonomialInsertionEnergy.monomial`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/MonomialInsertionEnergy.monomial_dirichlet`
