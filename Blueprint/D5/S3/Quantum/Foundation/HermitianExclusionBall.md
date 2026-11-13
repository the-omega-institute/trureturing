# Entire exclusion balls from full complex frames

## Abstract

A complex orthogonal two-plane gives global affine Bloch coordinates on the entire original mixed-state exclusion.

The carrier is all complex Hermitian three by three matrices, the cone is the full positive semidefinite cone, and the unit is the trace. All original proper real-linear effects remain available. Let v be any unit complex vector and let W be a three by two complex matrix with W*W=I and WW*=I-vv*. These hypotheses identify the whole orthogonal complement of v, rather than a selected subspace of it.

**Theorem 1.1 (Global affine chart of the entire exclusion).**

Lean statement: `D5/S3/Quantum/Foundation/HermitianExclusionBall.chart_of_full_frame`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/HermitianExclusionBall.chart_of_full_frame` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every v of norm one and every W satisfying W*W=I and WW*=I-vv*, there exists a native ExclusionChart for the original exclusion of vv*, with dimension exactly three. Its parameter map is defined on the whole real Euclidean three-space by r |-> W blochMatrix(1,r) W*. It is affine and injective on that entire space. The image of the closed unit ball equals the entire original exclusion, with no rank restriction on mixed states.

Compression by W* inverts the parameter map globally because W*W=I; the existing Bloch coordinate inverse proves injectivity. Conjugation preserves positivity and cyclicity of trace preserves normalization. Conversely, the full proper-functional exclusion identity gives Xv=0. Hermitian symmetry gives v*X=0, so X=(I-vv*)X(I-vv*). Consequently X=W(W*XW)W*. The compression is positive and trace one. The full two by two Bloch ball characterization supplies a coordinate of norm at most one, and reconstruction gives exactly X.

**Theorem 1.2 (Charts for every original pure label).**

Lean statement: `D5/S3/Quantum/Foundation/HermitianExclusionBall.all_pure_charts`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/HermitianExclusionBall.all_pure_charts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual extreme point p of the entire positive semidefinite trace-one qutrit body, there is a native ExclusionChart of its entire original exclusion and its dimension is exactly three. There is no chosen finite family of labels and no rank assumption on excluded mixed states.

The positive semidefinite sum-of-outer-products decomposition gives ROG on the whole Hermitian space; zero terms are removed and the remaining finite index type is reindexed without changing the sum. The existing whole_pure_carrier theorem therefore identifies all actual extreme points with unit outer products. The existing rog_frame theorem extends each such unit vector to a full complex orthonormal basis. Its two other columns form W: orthonormality gives W*W=I and the full frame sum gives WW*=I-vv*. Thus the preceding chart applies to every original pure label. Physical realization and literature priority are not asserted.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/HermitianExclusionBall.all_pure_charts`
- Truth anchor: `D5/S3/Quantum/Foundation/HermitianExclusionBall.chart_of_full_frame`
- Dependency: [D5/S3/Quantum/Foundation/ExclusionBallFaces](ExclusionBallFaces.md)
- Dependency: [D5/S3/Quantum/Foundation/HermitianExclusionKernel](HermitianExclusionKernel.md)
- Dependency: [D5/S3/Quantum/Measurement/FourQubitParentConstruction](../Measurement/FourQubitParentConstruction.md)
