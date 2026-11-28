# Four-dimensional conformal algebra and twistors

## Abstract

Signature (2,4), Minkowski inversion, four-point cross-ratios and the real twistor Lie equivalence.

Rotations of a signed six-dimensional form give the conformal generators. The Minkowski chart exhibits their conformal geometry through distance scaling, while the chiral Dirac matrices give a four-component complex representation.

**Theorem 1.1 (Metric antisymmetry).**

Lean statement: `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.so24_antisym_metric`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.so24_antisym_metric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Philippe Di Francesco, Pierre Mathieu, and David Sénéchal (1997). *Conformal Field Theory*. DOI: [10.1007/978-1-4612-2256-9](https://doi.org/10.1007/978-1-4612-2256-9). URL: <https://doi.org/10.1007/978-1-4612-2256-9>.

*Commentary.*

Each elementary generator is skew with respect to the diagonal form with positive entries in positions zero and five.

**Theorem 1.2 (Elementary generator bracket).**

Lean statement: `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.so24_commutator_universal`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.so24_commutator_universal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Philippe Di Francesco, Pierre Mathieu, and David Sénéchal (1997). *Conformal Field Theory*. DOI: [10.1007/978-1-4612-2256-9](https://doi.org/10.1007/978-1-4612-2256-9). URL: <https://doi.org/10.1007/978-1-4612-2256-9>.

*Commentary.*

The commutator of two elementary generators is the four-term contraction with the signed metric, with signs plus, minus, minus, plus in the displayed index order.

**Theorem 1.3 (Conformal generator brackets).**

Lean statement: `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.conformal_algebra_commutators`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.conformal_algebra_commutators` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Philippe Di Francesco, Pierre Mathieu, and David Sénéchal (1997). *Conformal Field Theory*. DOI: [10.1007/978-1-4612-2256-9](https://doi.org/10.1007/978-1-4612-2256-9). URL: <https://doi.org/10.1007/978-1-4612-2256-9>.

*Commentary.*

Translations commute with one another, as do special conformal generators. Dilatation commutes with Lorentz generators and has weights plus one on translations and minus one on special conformal generators. The special conformal and translation bracket is twice the Lorentz generator minus twice the metric component times dilatation. Lorentz generators act on both vector families by the signed vector action.

**Theorem 1.4 (Linear independence).**

Lean statement: `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.so24_basis15_linearIndependent`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.so24_basis15_linearIndependent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Philippe Di Francesco, Pierre Mathieu, and David Sénéchal (1997). *Conformal Field Theory*. DOI: [10.1007/978-1-4612-2256-9](https://doi.org/10.1007/978-1-4612-2256-9). URL: <https://doi.org/10.1007/978-1-4612-2256-9>.

*Commentary.*

The fifteen generators with increasing index pairs are linearly independent over the reals.

**Theorem 1.5 (Recovery from upper-triangular entries).**

Lean statement: `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.so24_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.so24_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Philippe Di Francesco, Pierre Mathieu, and David Sénéchal (1997). *Conformal Field Theory*. DOI: [10.1007/978-1-4612-2256-9](https://doi.org/10.1007/978-1-4612-2256-9). URL: <https://doi.org/10.1007/978-1-4612-2256-9>.

*Commentary.*

A metric-skew matrix is the sum of the elementary generators weighted by its upper-triangular entries times the sign of the column.

**Theorem 1.6 (Dimension of the orthogonal algebra).**

Lean statement: `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.so24_subspace_finrank_15`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.so24_subspace_finrank_15` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Philippe Di Francesco, Pierre Mathieu, and David Sénéchal (1997). *Conformal Field Theory*. DOI: [10.1007/978-1-4612-2256-9](https://doi.org/10.1007/978-1-4612-2256-9). URL: <https://doi.org/10.1007/978-1-4612-2256-9>.

*Commentary.*

The real subspace of matrices skew with respect to the six-dimensional form has dimension fifteen.

**Theorem 1.7 (Inversion and squared norm).**

Lean statement: `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.conformalInv_involutive`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.conformalInv_involutive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Philippe Di Francesco, Pierre Mathieu, and David Sénéchal (1997). *Conformal Field Theory*. DOI: [10.1007/978-1-4612-2256-9](https://doi.org/10.1007/978-1-4612-2256-9). URL: <https://doi.org/10.1007/978-1-4612-2256-9>.

*Commentary.*

At a non-null point inversion takes the squared norm to its reciprocal. Applying inversion again recovers the point.

**Theorem 1.8 (Inversion rescales squared separations).**

Lean statement: `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.conformalInv_diff_normSq`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.conformalInv_diff_normSq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Philippe Di Francesco, Pierre Mathieu, and David Sénéchal (1997). *Conformal Field Theory*. DOI: [10.1007/978-1-4612-2256-9](https://doi.org/10.1007/978-1-4612-2256-9). URL: <https://doi.org/10.1007/978-1-4612-2256-9>.

*Commentary.*

For two non-null points, the separation after inversion is the original squared separation divided by the product of their squared norms.

**Theorem 1.9 (Fréchet derivative of inversion).**

Lean statement: `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.conformalInv_hasFDerivAt`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.conformalInv_hasFDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Philippe Di Francesco, Pierre Mathieu, and David Sénéchal (1997). *Conformal Field Theory*. DOI: [10.1007/978-1-4612-2256-9](https://doi.org/10.1007/978-1-4612-2256-9). URL: <https://doi.org/10.1007/978-1-4612-2256-9>.

*Commentary.*

At a non-null point the derivative is inverse squared-norm scaling plus the rank-one correction from differentiating that scalar factor.

**Theorem 1.10 (Minkowski metric pullback).**

Lean statement: `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.conformalInv_metric_pullback`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.conformalInv_metric_pullback` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Philippe Di Francesco, Pierre Mathieu, and David Sénéchal (1997). *Conformal Field Theory*. DOI: [10.1007/978-1-4612-2256-9](https://doi.org/10.1007/978-1-4612-2256-9). URL: <https://doi.org/10.1007/978-1-4612-2256-9>.

*Commentary.*

The derivative of inversion rescales the bilinear form by the inverse square of the point squared norm.

**Theorem 1.11 (Special conformal coordinate formula).**

Lean statement: `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.sct_explicit_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.sct_explicit_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Philippe Di Francesco, Pierre Mathieu, and David Sénéchal (1997). *Conformal Field Theory*. DOI: [10.1007/978-1-4612-2256-9](https://doi.org/10.1007/978-1-4612-2256-9). URL: <https://doi.org/10.1007/978-1-4612-2256-9>.

*Commentary.*

At a non-null point with nonzero special conformal denominator, translating between two inversions gives the rational special conformal map.

**Theorem 1.12 (Special conformal separation factor).**

Lean statement: `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.sct_diff_normSq`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.sct_diff_normSq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Philippe Di Francesco, Pierre Mathieu, and David Sénéchal (1997). *Conformal Field Theory*. DOI: [10.1007/978-1-4612-2256-9](https://doi.org/10.1007/978-1-4612-2256-9). URL: <https://doi.org/10.1007/978-1-4612-2256-9>.

*Commentary.*

The transformed squared separation is divided by the product of the special conformal denominators. Nonzero denominators suffice, including for null input points.

**Theorem 1.13 (Invariance of both four-point ratios).**

Lean statement: `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.crossRatios_conformal_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.crossRatios_conformal_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Philippe Di Francesco, Pierre Mathieu, and David Sénéchal (1997). *Conformal Field Theory*. DOI: [10.1007/978-1-4612-2256-9](https://doi.org/10.1007/978-1-4612-2256-9). URL: <https://doi.org/10.1007/978-1-4612-2256-9>.

*Commentary.*

With non-null denominator separations, both ratios are invariant under translation, every metric-preserving Lorentz matrix, nonzero dilation, inversion of non-null points, and special conformal maps with nonzero denominators.

**Theorem 1.14 (Chiral matrices for the conformal generators).**

Lean statement: `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.twistorRep_conformal_generators`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.twistorRep_conformal_generators` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Philippe Di Francesco, Pierre Mathieu, and David Sénéchal (1997). *Conformal Field Theory*. DOI: [10.1007/978-1-4612-2256-9](https://doi.org/10.1007/978-1-4612-2256-9). URL: <https://doi.org/10.1007/978-1-4612-2256-9>.

*Commentary.*

Lorentz generators map to a quarter of the gamma-matrix commutator and dilatation maps to half the chirality matrix. The translation and special conformal generators map to the gamma matrices times the left and right chiral projectors with coefficients plus and minus the imaginary unit, respectively.

**Theorem 1.15 (Preservation of the Hermitian form).**

Lean statement: `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.twistorRep_mem_su22`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.twistorRep_mem_su22` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Philippe Di Francesco, Pierre Mathieu, and David Sénéchal (1997). *Conformal Field Theory*. DOI: [10.1007/978-1-4612-2256-9](https://doi.org/10.1007/978-1-4612-2256-9). URL: <https://doi.org/10.1007/978-1-4612-2256-9>.

*Commentary.*

Every image of the orthogonal subspace is traceless and skew with respect to the Hermitian form represented by the time-like Dirac matrix.

**Theorem 1.16 (Preservation of commutators).**

Lean statement: `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.twistorRep_lie_hom`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.twistorRep_lie_hom` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Philippe Di Francesco, Pierre Mathieu, and David Sénéchal (1997). *Conformal Field Theory*. DOI: [10.1007/978-1-4612-2256-9](https://doi.org/10.1007/978-1-4612-2256-9). URL: <https://doi.org/10.1007/978-1-4612-2256-9>.

*Commentary.*

The representation carries the commutator of two matrices in the orthogonal subspace to the commutator of their four-dimensional complex images.

**Theorem 1.17 (Twistor Lie equivalence).**

Lean statement: `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.twistorRep_bijective_su22`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.twistorRep_bijective_su22` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Philippe Di Francesco, Pierre Mathieu, and David Sénéchal (1997). *Conformal Field Theory*. DOI: [10.1007/978-1-4612-2256-9](https://doi.org/10.1007/978-1-4612-2256-9). URL: <https://doi.org/10.1007/978-1-4612-2256-9>.

*Commentary.*

The real linear representation maps the metric-skew orthogonal subspace bijectively onto the traceless subspace skew for the twistor metric. Together with bracket preservation, this identifies the two Lie algebras.

## References

- Truth anchor: `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.conformalInv_diff_normSq`
- Truth anchor: `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.conformalInv_hasFDerivAt`
- Truth anchor: `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.conformalInv_involutive`
- Truth anchor: `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.conformalInv_metric_pullback`
- Truth anchor: `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.conformal_algebra_commutators`
- Truth anchor: `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.crossRatios_conformal_invariant`
- Truth anchor: `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.sct_diff_normSq`
- Truth anchor: `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.sct_explicit_formula`
- Truth anchor: `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.so24_antisym_metric`
- Truth anchor: `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.so24_basis15_linearIndependent`
- Truth anchor: `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.so24_commutator_universal`
- Truth anchor: `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.so24_expansion`
- Truth anchor: `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.so24_subspace_finrank_15`
- Truth anchor: `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.twistorRep_bijective_su22`
- Truth anchor: `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.twistorRep_conformal_generators`
- Truth anchor: `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.twistorRep_lie_hom`
- Truth anchor: `D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D.twistorRep_mem_su22`
- Dependency: [D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D](DiracCliffordSpinors4D.md)
- Dependency: [D5/S3/Geometry/Lorentz/WeylNullScreen](WeylNullScreen.md)
