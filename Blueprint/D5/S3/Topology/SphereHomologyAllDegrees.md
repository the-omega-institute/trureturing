# Actual sphere homology in every degree

## Abstract

The TauCeti sphere computation and dimension induction cover every positive degree.

**Theorem 1.1 (Reduced sphere homology vanishes off the dimension).**

Lean statement: `D5/S3/Topology/SphereHomologyAllDegrees.isZero_reducedHomology_sphere`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/SphereHomologyAllDegrees.isZero_reducedHomology_sphere` (`✓ std3`). ∎

*Citation.* Allen Hatcher (2002). *Algebraic Topology*. URL: <https://pi.math.cornell.edu/~hatcher/AT/AT.pdf>.

*Commentary.*

For every natural sphere dimension d, real inner-product space E with a supplied orthonormal basis indexed by Fin(d+1), coefficient object R in an abelian category with the required coproducts, and natural q distinct from d, the actual reduced singular homology of the unit sphere in E is zero. Dimension zero uses the actual discrete sphere. In positive dimension, degree zero uses path connectedness; positive degrees use the existing reducedSingularHomologySphereSuccIso and orthogonalLast basis. Thus the induction includes degrees below and above the dimension. This is the classical homology computation of spheres, using the existing TauCeti port at its original general telescope.

**Theorem 1.2 (Every positive-degree sphere homology module is torsion-free).**

Lean statement: `D5/S3/Topology/SphereHomologyAllDegrees.isTorsionFree_singularHomology_sphere`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/SphereHomologyAllDegrees.isTorsionFree_singularHomology_sphere` (`✓ std3`). ∎

*Citation.* Allen Hatcher (2002). *Algebraic Topology*. URL: <https://pi.math.cornell.edu/~hatcher/AT/AT.pdf>.

*Commentary.*

For a ring k and any coefficient module M satisfying Module.IsTorsionFree k M, the actual singular homology of each such sphere satisfies Module.IsTorsionFree in every q>0. On the diagonal, TauCeti.reducedSingularHomologySphereIso identifies the group with M. Off the diagonal, the preceding vanishing theorem makes it a zero module. Over a general ring, this means injectivity of multiplication by regular scalars as specified by Mathlib; injectivity for every nonzero scalar is only asserted at the integral-domain endpoint. No IsDomain assumption is imposed on this generic theorem.

## References

- Truth anchor: `D5/S3/Topology/SphereHomologyAllDegrees.isTorsionFree_singularHomology_sphere`
- Truth anchor: `D5/S3/Topology/SphereHomologyAllDegrees.isZero_reducedHomology_sphere`
