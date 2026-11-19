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

**Theorem 1.3 (Rank one generation of the entire native positive cone).**

Lean statement: `D5/S3/Quantum/Foundation/HermitianExclusionBall.whole_rog`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/HermitianExclusionBall.whole_rog` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite complex index type, ROG holds on the whole real Hermitian carrier. The original proof removes zero terms from the positive semidefinite sum-of-outer-products decomposition. Together with SectionROGFrame.whole_pure_carrier, this identifies every actual pure label in the whole-effect model application of the original state-cover theorem.

The positive semidefinite sum-of-outer-products decomposition gives ROG on the whole Hermitian space; zero terms are removed and the remaining finite index type is reindexed without changing the sum. The existing whole_pure_carrier theorem therefore identifies all actual extreme points with unit outer products. The existing rog_frame theorem extends each such unit vector to a full complex orthonormal basis. Its two other columns form W: orthonormality gives W*W=I and the full frame sum gives WW*=I-vv*. Thus the preceding chart applies to every original pure label. Physical realization and literature priority are not asserted.

The original labels are faithful as a consequence of the full kernel identity. For a unit outer product p=vv*, the trace bound for positive Hermitian matrices gives p<=I. Thus c=(I-p)/2 is positive, has trace one, and annihilates v, so c belongs to the entire original exclusion of p. If that exclusion equals the exclusion of q=ww*, the same kernel identity gives cw=0, hence pw=w and pq=q. Reversing the roles gives qp=p. Taking adjoints gives pq=p, and therefore p=q. The whole pure-carrier characterization makes this argument apply to every actual original pure point. Injectivity is derived without assuming it or reducing the allowed effects.

For the same whole-cone, trace-preserving real-linear Phi used in HermitianExclusionKernel, Phi maps the entire density base onto K. Linear equivalences preserve extreme points (image_extremePoints), so HermitianExclusionBall.whole_rog and SectionROGFrame.whole_pure_carrier give EXACTLY P={Phi(vv*):||v||=1}. This carrier is nonempty in the literal native model: take V=HermitianMat (Fin 3) ℂ, Phi=LinearEquiv.refl, C=HermitianExclusionKernel.cone, u=HermitianExclusionKernel.unit, and v the standard coordinate vector at index zero. Its outer product is PSD with trace one, has rank one, and belongs to the actual extreme-point set by whole_pure_carrier. The unit sphere is compact and the outer-product/Phi map continuous, so the entire original P is compact; this is derived, not a premise restricting the pure labels.

Composition with this same Phi transports every original proper effect and hence the entire exclusion in both directions. Therefore all_pure_charts supplies an original globally injective affine chart of the whole closed three-ball at EVERY p in P, and the preceding equal-exclusion argument gives Inj on ALL P. The positive cone is closed, trace is strictly positive on each nonzero positive Hermitian matrix, and IsSelfAdjoint.neg_algebraMap_norm_le_self writes every Hermitian A as (A+||A||_op I)-||A||_op I, a difference of two positive matrices, proving that the entire cone spans the full real Hermitian carrier. All these facts transport through Phi. Distinct standard basis outer products at indices zero and one give actual pure labels and an actual excluded state in this single native model. Thus closedness, generation, strictness, EB3 and Inj hold together for the same C,u,K,P and the entire effect interval. The common-confirmer, continuity, normal-span and original-cost applications in the corresponding owner narratives use precisely these data; no separately realizable package or stronger classification assumption is inserted.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/HermitianExclusionBall.all_pure_charts`
- Truth anchor: `D5/S3/Quantum/Foundation/HermitianExclusionBall.chart_of_full_frame`
- Truth anchor: `D5/S3/Quantum/Foundation/HermitianExclusionBall.whole_rog`
- Dependency: [D5/S3/Quantum/Foundation/ExclusionBallFaces](ExclusionBallFaces.md)
- Dependency: [D5/S3/Quantum/Foundation/HermitianExclusionKernel](HermitianExclusionKernel.md)
- Dependency: [D5/S3/Quantum/Measurement/FourQubitParentConstruction](../Measurement/FourQubitParentConstruction.md)
