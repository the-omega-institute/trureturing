# Parity-gauged signed axial fold

## Abstract

Parity-gauged signed axial fold

The intended application of the signed Huang equations is the normalized order-ninety cylinder for Hong–Wu–Xia, arXiv:2610.09483 §7, Problem 2. The fold works for any coherently switched induced cubic support of the nine-cube, with the first coordinate taken as the axis.

**Definition 1.1 (Projected parity sign).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedAxialFold.paritySign`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedAxialFold.paritySign` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write P(x) for the sign of the parity of the eight retained bits. It is +1 on even sites and −1 on odd sites. Its square is one.

**Theorem 1.2 (A transverse flip reverses projected parity).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedAxialFold.paritySign_flip`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedAxialFold.paritySign_flip` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Flipping one retained bit reverses P. The fold uses this identity to gauge the transverse row. Q9ConnectorResidual.residual_at_connector uses it to pass from the odd connector to an even neighbour and then to an odd residual site.

**Definition 1.3 (Signed transverse row).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedAxialFold.transverse`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedAxialFold.transverse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The native eight-cube Huang row H sums the values at the eight transverse flips with their signed edge coefficients. Since each flip reverses P, the row of the pointwise product P·v is −P times the row of v.

**Definition 1.4 (Integer switching word).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedAxialFold.signedWord`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedAxialFold.signedWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At a selected vertex x, the integer word is +1 if s(x) = 1 and −1 otherwise. It is zero off the support. For a coherent switching, its real cast is the zero-extended switching vector. The ambient degree-three eigenvector relation therefore gives the signed nine-cube row equation over the integers.

**Definition 1.5 (Parity gauge of the axial layers).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedAxialFold.gaugeLayer`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedAxialFold.gaugeLayer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An axial layer fixes the first bit. The gauge takes the true layer directly and multiplies the false layer by P. The original axial coupling has coefficient one and the transverse terms have opposite signs in the two layers. After the gauge, both transverse operators are H and the coupling is multiplication by P.

**Theorem 1.6 (Complementary equations for the folded modes).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedAxialFold.signed_fold`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedAxialFold.signed_fold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a and b be the gauged true and false layers. The two row equations are Ha + P·b = 3a and Hb + P·a = 3b. Adding and subtracting gives Hg = (3 − P)g for the sum g = a + b and Hh = (3 + P)h for the difference h = a − b. Each folded mode combines both axial layers.

In the majority-even normalization of the order-ninety case, the sum row is 2g at an even projected site and 4g at an odd site. The difference has the complementary coefficients. Thus an actual even singleton has sum value ±1 and contributes a nonzero row of the sum mode.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedAxialFold.gaugeLayer`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedAxialFold.paritySign`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedAxialFold.paritySign_flip`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedAxialFold.signedWord`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedAxialFold.signed_fold`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedAxialFold.transverse`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum](../BalancedCriticalSpectrum.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9IsotropicHuang](Q9IsotropicHuang.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9OccupiedFibreParity](Q9OccupiedFibreParity.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/HuangCubeCovariance](../HuangCubeCovariance.md)
