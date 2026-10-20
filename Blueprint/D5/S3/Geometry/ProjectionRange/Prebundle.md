# Smooth complex projection-range bundles over real manifolds

## Abstract

Smooth complex projection-range bundles over real manifolds

The formula packages all quantified input data into q in SmoothProjectionData: arbitrary types E,H,B; a real normed model E; topologies on H and B; a charted-space structure; a model with corners I; an IsManifold I infinity B instance; arbitrary n,r in N; a complex n by n matrix field p; real smoothness of p; and Hermitian, idempotent, constant-rank-r proofs. RealPrebundle(q) means VectorPrebundle R (EuclideanSpace C (Fin r)) (Fiber p), with Fiber p x the actual Euclidean range subtype. No input data are fixed or omitted by this packaging. For a in this type, SmoothAtlas means a.IsContMDiff I infinity. ComplexRank means every Fiber p x has complex finrank r. ComplexBundle and RealSmoothBundle are the complex vector-bundle and real ContMDiffVectorBundle assertions under the let-bound topology, FiberBundle and real VectorBundle supplied by a. AmbientEmbedding and InducedTopology mean respectively IsEmbedding of the actual ambient map and equality of a.totalSpaceTopology with its induced topology from B times C^n. FixedImage means the range of ambient is exactly the pairs (x,v) satisfying p(x)v=v. SmoothAmbient means real ContMDiff of ambient from the total-space product model to the ambient product model. SmoothReconstruction means, for every ColumnChart c, real ContMDiff of (x,w) mapped to (x,c.intoRange hidem x w), using the same topology and bundle instances. All nine predicates in the displayed conjunction have these definitions; together with the quantified a they are the full constructor statement.

Let B be any real smooth manifold modeled by I, and let p be a smooth n by n complex matrix field with p(x)*=p(x), p(x)^2=p(x), and constant rank r. The fiber is the actual range of Matrix.toEuclideanLin(p(x)) inside EuclideanSpace C (Fin n), with its inherited complex linear and normed structures. The model fiber is EuclideanSpace C (Fin r).

At each base point select r independent columns C of p. The local Gram certificate gives an open set on which G=C* C is invertible and the selected columns span the full projection range. Define L=G^(-1) C*. Then LC=1, and CL acts as the identity on the range. No local frame is supplied as an assumption: the columns, their domains, and both inverse maps are constructed.

The actual trivialization sends (x,v) to (x,L(x)v), and reconstruction sends (x,w) to (x,C(x)w). On overlaps the transition from chart a to chart b is L_b(x) C_a(x). Finite-coordinate multiplication and conjugation are real smooth. Inversion is transported through CStarMatrix to use the complete normed algebra inverse theorem on the open unit locus.

The real and complex prebundles use the very same pretrivialization atlas and the same selected chart at each point. Complex linearity is retained while all differentiability is over R. Their generated topologies agree by the shared construction. The real smooth vector bundle provides the real smooth total-space structure.

The ambient map sends (x,v) to the actual pair (x,v) in B times C^n. Its image is exactly the fixed-vector locus p(x)v=v. It is smooth, is an embedding, and induces precisely the constructed total-space topology. The inverse identification with the ambient range subtype is continuous. Every column reconstruction is smooth into the total space; its inverse identities are asserted on its chart domain, while the reconstruction map itself is globally defined.

The parameters n and r are arbitrary natural numbers; zero-dimensional fibers, zero ambient dimension, and an empty base are retained. There is no compactness, positivity of rank, nonempty base, global frame, or assumed bundle hypothesis. The result is a general geometric constructor. The actual Ephys and Fsyn application, the Theta tensor equivalence, positive trace-one sigma and decoder factorization, and global transport remain separate obligations. The constructor alone does not assert vanishing of a curvature integral; the application below uses the additional global transversality hypothesis.

The proof uses the pinned Mathlib vector prebundle construction, finite-dimensional linear maps, matrix rank and Gram positivity, and smooth inversion. This is the classical local-frame construction.

Application: a fixed reference space and a nonzero curvature integral. Let Sigma be a compact, boundaryless, oriented smooth real surface, and let P(x) be a smooth Hermitian idempotent n by n complex matrix of constant rank r, with 1 <= r < n. Write E_x = Ran P(x). Fix any Hermitian rank-r projection P0. The parameter map to this constructor is B = Sigma, p = P, and the same n,r; its Fiber is exactly E_x with the Euclidean norm. Compactness, orientation and real dimension two enter the integral argument below, not the local bundle constructor. No global frame, inverse restriction, curvature identity or vanishing integral is an input.

Choose orthonormal columns W0 spanning Ran P0 and W1 spanning its orthogonal complement. Rank-nullity gives rank(I-P0) = n-r. These frames can be constructed from the existing column-chart existence result applied to the constant projections P0 and I-P0: for independent spanning columns C, replace C by C(C* C)^(-1/2). Positive Gram calculus gives Wj* Wj = I, W0* W1 = 0, W0 W0* = P0 and W1 W1* = I-P0. Thus W0 W0* + W1 W1* = I. Here * denotes conjugate transpose, and every norm below is the induced operator norm between the indicated complex Euclidean spaces.

Say that x is transverse to P0 when P0 restricted to E_x is injective. Its domain and target both have dimension r, so this restriction is an isomorphism. In the coordinates W0, its adjoint is the map a |-> P(x)W0 a; hence G(x) = W0* P(x)W0 is positive definite. Conversely, positivity of this Gram matrix makes that adjoint an isomorphism and gives the same transversality. On a transverse region define U = P W0 G^(-1/2), using the positive Hermitian square root. Then U* U = G^(-1/2) G G^(-1/2) = I. Its r-dimensional range lies in E_x and therefore equals E_x, so U U* = P. The same formulas define the frame used in the connection, obstruction and compression calculations below.

This U is smooth wherever transversality holds. The existing Prebundle smooth multiplication, adjoint and inversion results reduce this to smoothness of the positive square root. For a positive Hermitian Y, the derivative of Y |-> Y^2 is H |-> YH+HY; diagonalizing Y multiplies each matrix entry by a strictly positive eigenvalue sum. This derivative is invertible on the real Hermitian space. The existing Hermitian square-derivative and Jordan-conjugation results, followed by the pinned inverse-function theorem, give a smooth local inverse. The identity (sqrt G)^2 = G and uniqueness of that local inverse identify it with the positive functional-calculus root. Positivity is open, so these neighborhoods give the required smooth root and then its smooth inverse. This is an application of existing calculus, rather than an additional assumed smoothness certificate.

For this actual isometric U, use the physical convention A = i U* dU and F = dA - i A wedge A. The ordinary exterior derivative and product rule give dA = i dU* wedge dU. Differentiating U* U = I and P = U U* then gives F = i dU* (I-P) wedge dU = i U* (dP wedge dP) U. Rectangular cyclicity of trace identifies tr F with i tr(P(dP wedge dP)), so this two-form depends on P, not on the chosen local isometric frame. Evaluated on real tangent vectors, F is Hermitian and tr F is real. These are identities of the same matrices and differential forms, not independent curvature premises.

Define C1 here by the literal physical integral (2 pi)^(-1) times the integral over Sigma of Re(i tr(P(dP wedge dP))). If transversality holds everywhere, U above is a global smooth frame. The trace of A wedge A vanishes: on two tangent vectors it is the trace of a commutator. Consequently tr F = d tr A. Taking real and imaginary parts commutes with d; their smooth primitives have compact support on the compact base. Boundaryless Stokes applied to these real forms makes both integrals zero, and in particular gives C1 = 0. This uses the actual surface integral, not an abstract functional chosen to vanish. The customary identification with an integral Chern class and its integer-valuedness are background facts; neither is needed for the implication from a nonzero value of this integral.

Suppose this C1 is nonzero. The base is nonempty, since integration over the empty base is zero. Global transversality would give the preceding contradiction, so some x admits a nonzero v in E_x with P0 v = 0. Normalize it by its Euclidean norm to get a unit vector w with P(x)w = w and P0 w = 0. Thus (I-P0)P(x)w = w, which gives operator norm at least one. Every orthogonal projection is a contraction, so ||(I-P0)P(y)|| <= 1 for every y. The value one is therefore attained at x and is the maximum over Sigma, for each fixed rank-r P0. This is an actual unit-vector witness and an attained maximum, not just a supremum estimate.

At any single transverse point, set V = P W0 G^(-1) and X = W1* V, an (n-r) by r matrix. From W0* V = I and the complete orthogonal splitting one gets V = W0 + W1 X. Idempotence of P gives V* V = G^(-1), while the splitting gives V* V = I + X* X. Hence the same normalized frame is U = (W0 + W1 X)(I + X* X)^(-1/2), and its compression by the original reference projection is U* P0 U = (I + X* X)^(-1). This calculation is pointwise; transversality elsewhere on Sigma is unnecessary.

For r >= 1, the positive matrix X* X has a largest eigenvalue equal to ||X||^2. Functional calculus sends an eigenvalue t to (1+t)^(-1), a decreasing function on t >= 0. Therefore the actual least eigenvalue of U* P0 U is 1/(1+||X||^2). When X = 0 this gives one without any division by ||X||. Rank zero is permitted by the general bundle constructor, but its empty eigenvalue range has no least member; this least-eigenvalue conclusion is asserted only for positive r. The empty-base and zero-dimensional cases are not silently excluded from the constructor.

These formulas give the classical fixed-reference graph obstruction in original ST23.2. They reuse ProjectionRange.exists_columnChart, ProjectionRange.smooth_mul, ProjectionRange.smooth_adj and ProjectionRange.smooth_inv; the existing HermitianCubeDerivative and HermitianHypersurfaceCalculus square/Jordan calculus; pinned positive spectral calculus and inverse-function results; and the pinned differential-form naturality and boundaryless Stokes results. This is the classical projection-bundle and Stokes argument specialized to a fixed reference subspace. Failure of a single fixed graph chart does not assert closure of a Hamiltonian energy gap. The subspace-loss quantity ||(I-P0)P(x)||^2 is distinct from the leakage of an actual measurement instrument. Finite compatible atlases, the ST24 control bounds and the ST25 examples require their own arguments.

**Remark 1.1 (V).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.V`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.V` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

EuclideanSpace over complex Fin k; no positivity assumption.

**Remark 1.2 (rangeSubmodule).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.rangeSubmodule`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.rangeSubmodule` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

LinearMap.range of Matrix.toEuclideanLin applied to p x.

**Remark 1.3 (Fiber).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.Fiber`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.Fiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subtype of the actual Euclidean range with inherited structures.

**Remark 1.4 (columns).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.columns`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.columns` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Select entries p x i (J j); rectangular matrix n by r.

**Remark 1.5 (gram).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.gram`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.gram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Conjugate transpose of selected columns times selected columns.

**Remark 1.6 (leftMatrix).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.leftMatrix`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.leftMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Inverse Gram times conjugate transpose of columns.

**Remark 1.7 (ColumnChart).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.ColumnChart`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.ColumnChart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Data J,U with injectivity, open set, invertible Gram and spanning equality; constructor builds this data.

**Remark 1.8 (exists_columnChart).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.exists_columnChart`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.exists_columnChart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply unchanged exact_original_local_gram_certificate on univ; PSD from Hermitian idempotence; rank equality from constant matrix rank; unpack U and span witness.

**Remark 1.9 (chartAt).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.chartAt`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.chartAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Classical.choose of pointwise chart existence; the chart can vary with base point.

**Remark 1.10 (mem_chartAt).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.mem_chartAt`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.mem_chartAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Choose_spec of the same chart existence; supplies base-set membership.

**Remark 1.11 (euclidean_range_eq_of_span_eq).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.euclidean_range_eq_of_span_eq`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.euclidean_range_eq_of_span_eq` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use Matrix.range_mulVecLin for function-coordinate ranges and WithLp transport of witnesses in both directions.

**Remark 1.12 (left_mul_columns).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.left_mul_columns`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.left_mul_columns` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Associate inverse Gram times Gram; use Matrix.nonsing_inv_mul via invertible determinant.

**Remark 1.13 (range_columns).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.range_columns`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.range_columns` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply euclidean_range_eq_of_span_eq to the supplier span equality.

**Remark 1.14 (projection_columns).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.projection_columns`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.projection_columns` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Select columns on both sides of p*p=p using congrArg; no new projection theorem.

**Remark 1.15 (intoRange).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.intoRange`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.intoRange` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

codRestrict selected-column Euclidean linear map to actual range, witnessing membership by the same column image and idempotence.

**Remark 1.16 (coordinates).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.coordinates`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.coordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Euclidean linear map of inverse-Gram leftMatrix composed with range subtype inclusion.

**Remark 1.17 (coordinates_intoRange).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.coordinates_intoRange`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.coordinates_intoRange` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Rewrite composed Euclidean maps as matrix product, then left_mul_columns and identity matrix map.

**Remark 1.18 (intoRange_coordinates).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.intoRange_coordinates`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.intoRange_coordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Represent range vector by selected columns using range_columns; reduce to coordinates_intoRange via Subtype.ext.

**Remark 1.19 (equiv).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.equiv`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.equiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Linear equivalence with forward coordinates and inverse intoRange; both inverse laws supplied.

**Remark 1.20 (equivL).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.equivL`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.equivL` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Promote existing finite-dimensional LinearEquiv by toContinuousLinearEquiv.

**Remark 1.21 (pretrivialization).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.pretrivialization`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.pretrivialization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Actual TotalSpace to base-coordinate pair, inverse base-column image; source preimage U and target U times univ; inverse laws above.

**Remark 1.22 (complex_linear).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.complex_linear`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.complex_linear` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use coordinates.isLinear at each base point.

**Remark 1.23 (real_linear).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.real_linear`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.real_linear` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restrict coordinates linear map to real scalars then use isLinear.

**Remark 1.24 (symm_eq).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.symm_eq`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.symm_eq` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply injectivity of local linear equivalence and Pretrivialization.apply_mk_symm; identify bundle inverse with actual intoRange.

**Remark 1.25 (inducing).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.inducing`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.inducing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use isInducing_const_prod and homeomorphism underlying equivL.

**Remark 1.26 (transition).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.transition`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.transition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Matrix leftMatrix for destination b times columns for source a; beta-after-alpha direction.

**Remark 1.27 (transition_apply).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.transition_apply`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.transition_apply` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use symm_eq on source chart and Matrix.toLpLin_mul_same to match transition evaluation with chart change.

**Remark 1.28 (matrixCLE).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.matrixCLE`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.matrixCLE` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compose Matrix.toEuclideanLin and LinearMap.toContinuousLinearMap, then finite-dimensional toContinuousLinearEquiv.

**Remark 1.29 (matrixRealCLM).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.matrixRealCLM`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.matrixRealCLM` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Convert matrix to complex operator, restrict outer map to real scalars, then apply restrictScalarsL to operator values.

**Remark 1.30 (smooth_mul).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.smooth_mul`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.smooth_mul` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Coordinatewise finite sums of scalar products, applying contDiff_mul and manifold product composition.

**Remark 1.31 (smooth_adj).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.smooth_adj`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.smooth_adj` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Coordinatewise Complex.conjCLE smoothness after transposed coordinate projections.

**Remark 1.32 (smooth_inv).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.smooth_inv`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.smooth_inv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Transport to CStarMatrix normed algebra, apply contDiffAt_ringInverse at a unit, then use local unit openness and inverse uniqueness.

**Remark 1.33 (smooth_columns).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.smooth_columns`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.smooth_columns` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Twice use contMDiffAt_pi_space on hp to select coordinate J j.

**Remark 1.34 (smooth_left).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.smooth_left`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.smooth_left` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Combine smooth columns, adjoint, multiplication and unit-locus inversion with gram_unit.

**Remark 1.35 (smooth_transition).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.smooth_transition`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.smooth_transition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiply smooth destination leftMatrix with smooth source columns on chart overlap.

**Remark 1.36 (prebundle).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.prebundle`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.prebundle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Real VectorPrebundle with constructed atlas, selected chartAt and real matrix operators as overlap witnesses; inducing from actual fibers.

**Remark 1.37 (complexPrebundle).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.complexPrebundle`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.complexPrebundle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Same pretrivialization atlas and selected charts; complex operators remain complex-valued, outer CLM is restricted to real scalars for calculus.

**Remark 1.38 (smooth_prebundle).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.smooth_prebundle`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.smooth_prebundle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Supply actual real smooth overlap operators to VectorPrebundle.IsContMDiff.

**Remark 1.39 (ambient).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.ambient`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.ambient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Map actual dependent total-space point to pair of its base and subtype value.

**Remark 1.40 (mem_fiber_iff_fixed).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.mem_fiber_iff_fixed`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.mem_fiber_iff_fixed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply pinned Mathlib LinearMap.IsIdempotentElem.mem_range_iff to Matrix.toEuclideanLin (p x), with idempotence transported from hidem by Matrix.toLpLin_mul_same; the fixed vector then witnesses its own range membership.

**Remark 1.41 (ambient_range).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.ambient_range`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.ambient_range` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two inclusions using mem_fiber_iff_fixed; actual image is fixed-point locus.

**Remark 1.42 (smooth_ambient).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.smooth_ambient`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.smooth_ambient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Bundle total-space criterion yields smooth projection and local coordinates; reconstruct ambient vector by smooth columns, using intoRange_coordinates eventually on chart U.

**Remark 1.43 (smooth_intoRange).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.smooth_intoRange`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.smooth_intoRange` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Bundle total-space criterion reduces to smooth base projection and leftMatrix-times-columns evaluation; typed Eventually.of_forall plus Matrix.toLpLin_mul_same identifies exact coordinates.

**Remark 1.44 (finrank_fiber).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.finrank_fiber`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.finrank_fiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Local actual range linear equivalence gives finrank equality; Euclidean Fin r has complex finrank r.

**Remark 1.45 (AmbientRange).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.AmbientRange`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.AmbientRange` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subtype of ambient B times V n with actual range membership; inherited subtype topology.

**Remark 1.46 (continuous_toAmbientRange).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.continuous_toAmbientRange`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.continuous_toAmbientRange` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take continuity of smooth_ambient then Continuous.subtype_mk with actual membership proof.

**Remark 1.47 (continuous_fromAmbientRange).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.continuous_fromAmbientRange`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.continuous_fromAmbientRange` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

FiberBundle.continuousAt_totalSpace; typed base map from ambient subtype; compose smooth_left operator at z.val.fst with that map using explicit f and x, then clm_apply subtype second projection.

**Remark 1.48 (ambientHomeomorph).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.ambientHomeomorph`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.ambientHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Repackage actual TotalSpace and AmbientRange coordinates, rfl inverse laws; consume both continuity lemmas without re-expanding their proofs.

**Remark 1.49 (ambient_isEmbedding).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.ambient_isEmbedding`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.ambient_isEmbedding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compose ambientHomeomorph.isEmbedding with IsEmbedding.subtypeVal.

**Remark 1.50 (totalTopology_eq_induced).**

Lean statement: `D5/S3/Geometry/ProjectionRange/Prebundle.totalTopology_eq_induced`

*Formalization.* `D5/S3/Geometry/ProjectionRange/Prebundle.totalTopology_eq_induced` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply IsInducing.eq_induced to ambient_isEmbedding.

**Theorem 1.51 (smooth_projection_range_prebundle).**

$$\forall q\in SmoothProjectionData, \exists a\in RealPrebundle\left(q\right), {SmoothAtlas\left(q, a\right) \land ComplexRank\left(q\right) \land ComplexBundle\left(q, a\right) \land RealSmoothBundle\left(q, a\right) \land AmbientEmbedding\left(q, a\right) \land InducedTopology\left(q, a\right) \land FixedImage\left(q\right) \land SmoothAmbient\left(q, a\right) \land SmoothReconstruction\left(q, a\right)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ProjectionRange/Prebundle.smooth_projection_range_prebundle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Return prebundle hp hstar hidem hrank as existential witness; consume smooth_prebundle, finrank_fiber, complexPrebundle.toVectorBundle, contMDiffVectorBundle, embedding, induced topology, fixed-point image, smooth ambient map and every chart reconstruction.

## References

- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.AmbientRange`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.ColumnChart`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.Fiber`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.V`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.ambient`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.ambientHomeomorph`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.ambient_isEmbedding`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.ambient_range`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.chartAt`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.columns`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.complexPrebundle`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.complex_linear`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.continuous_fromAmbientRange`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.continuous_toAmbientRange`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.coordinates`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.coordinates_intoRange`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.equiv`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.equivL`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.euclidean_range_eq_of_span_eq`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.exists_columnChart`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.finrank_fiber`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.gram`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.inducing`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.intoRange`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.intoRange_coordinates`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.leftMatrix`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.left_mul_columns`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.matrixCLE`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.matrixRealCLM`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.mem_chartAt`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.mem_fiber_iff_fixed`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.prebundle`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.pretrivialization`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.projection_columns`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.rangeSubmodule`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.range_columns`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.real_linear`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.smooth_adj`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.smooth_ambient`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.smooth_columns`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.smooth_intoRange`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.smooth_inv`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.smooth_left`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.smooth_mul`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.smooth_prebundle`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.smooth_projection_range_prebundle`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.smooth_transition`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.symm_eq`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.totalTopology_eq_induced`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.transition`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/Prebundle.transition_apply`
- Dependency: [D5/S3/Geometry/ProjectionRange/LocalGramCertificate](LocalGramCertificate.md)
