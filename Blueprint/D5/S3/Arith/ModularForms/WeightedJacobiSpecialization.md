# WeightedJacobiSpecialization

## Abstract

The complete integer Jacobi sum equals its actual weighted product limit.

This is the classical Jacobi triple product at t=q^(a+1+r), z=q^r, obtained from the existing InversionSeq207 and CubicThetaJacobi suppliers. The inequality triangularExponent(k)+k >= 0 holds for every integer, including both directions of the quadratic tail. The Laurent support construction therefore transfers the complete sum and all finite factors. The factor weights are positive when r>0; for r=0 the factor 1-X^0 is zero and the product degenerates to zero. No numerical cutoff is a hypothesis. EulerPentagonalTrisection uses the sum; EulerNineDissection uses the same actual finite-product limit.

**Theorem 1.1 (triangular_add_index_nonnegative).**

Lean statement: `D5/S3/Arith/ModularForms/WeightedJacobiSpecialization.triangular_add_index_nonnegative`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/WeightedJacobiSpecialization.triangular_add_index_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The full integer quadratic support lies in the admissible cone.

**Definition 1.2 (weightedExponent).**

Lean statement: `D5/S3/Arith/ModularForms/WeightedJacobiSpecialization.weightedExponent`

*Formalization.* `D5/S3/Arith/ModularForms/WeightedJacobiSpecialization.weightedExponent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The natural degree of the weighted integer Jacobi monomial.

**Theorem 1.3 (twice_weightedExponent).**

Lean statement: `D5/S3/Arith/ModularForms/WeightedJacobiSpecialization.twice_weightedExponent`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/WeightedJacobiSpecialization.twice_weightedExponent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The exact integer quadratic formula, with all casts accounted for.

**Definition 1.4 (J).**

Lean statement: `D5/S3/Arith/ModularForms/WeightedJacobiSpecialization.J`

*Formalization.* `D5/S3/Arith/ModularForms/WeightedJacobiSpecialization.J` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The specialization of the actual normalized Jacobi series.

**Theorem 1.5 (hasSum_J).**

Lean statement: `D5/S3/Arith/ModularForms/WeightedJacobiSpecialization.hasSum_J`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/WeightedJacobiSpecialization.hasSum_J` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

Every integer Jacobi monomial, with its original parity sign, sums to J.

**Definition 1.6 (finiteProduct).**

Lean statement: `D5/S3/Arith/ModularForms/WeightedJacobiSpecialization.finiteProduct`

*Formalization.* `D5/S3/Arith/ModularForms/WeightedJacobiSpecialization.finiteProduct` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The actual three Euler factor families, with positive weights when r>0 and a zero factor when r=0.

**Theorem 1.7 (tendsto_finiteProduct).**

Lean statement: `D5/S3/Arith/ModularForms/WeightedJacobiSpecialization.tendsto_finiteProduct`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/WeightedJacobiSpecialization.tendsto_finiteProduct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The finite products converge coefficientwise to the same complete integer sum.

## References

- Truth anchor: `D5/S3/Arith/ModularForms/WeightedJacobiSpecialization.J`
- Truth anchor: `D5/S3/Arith/ModularForms/WeightedJacobiSpecialization.finiteProduct`
- Truth anchor: `D5/S3/Arith/ModularForms/WeightedJacobiSpecialization.hasSum_J`
- Truth anchor: `D5/S3/Arith/ModularForms/WeightedJacobiSpecialization.tendsto_finiteProduct`
- Truth anchor: `D5/S3/Arith/ModularForms/WeightedJacobiSpecialization.triangular_add_index_nonnegative`
- Truth anchor: `D5/S3/Arith/ModularForms/WeightedJacobiSpecialization.twice_weightedExponent`
- Truth anchor: `D5/S3/Arith/ModularForms/WeightedJacobiSpecialization.weightedExponent`
- Dependency: [D5/S3/Arith/ModularForms/CubicThetaJacobiCube](CubicThetaJacobiCube.md)
- Dependency: [D5/S3/Combinatorics/PowerSeries/LaurentSpecialization](../../Combinatorics/PowerSeries/LaurentSpecialization.md)
