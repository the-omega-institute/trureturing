using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.ProjectionRange;

internal sealed class PrebundleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/ProjectionRange/Prebundle.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Smooth complex projection-range bundles over real manifolds",
        H("Smooth complex projection-range bundles over real manifolds"),
        Blocks(
            Paragraph(Text("The formula packages all quantified input data into q in SmoothProjectionData: arbitrary types E,H,B; a real normed model E; topologies on H and B; a charted-space structure; a model with corners I; an IsManifold I infinity B instance; arbitrary n,r in N; a complex n by n matrix field p; real smoothness of p; and Hermitian, idempotent, constant-rank-r proofs. RealPrebundle(q) means VectorPrebundle R (EuclideanSpace C (Fin r)) (Fiber p), with Fiber p x the actual Euclidean range subtype. No input data are fixed or omitted by this packaging. For a in this type, SmoothAtlas means a.IsContMDiff I infinity. ComplexRank means every Fiber p x has complex finrank r. ComplexBundle and RealSmoothBundle are the complex vector-bundle and real ContMDiffVectorBundle assertions under the let-bound topology, FiberBundle and real VectorBundle supplied by a. AmbientEmbedding and InducedTopology mean respectively IsEmbedding of the actual ambient map and equality of a.totalSpaceTopology with its induced topology from B times C^n. FixedImage means the range of ambient is exactly the pairs (x,v) satisfying p(x)v=v. SmoothAmbient means real ContMDiff of ambient from the total-space product model to the ambient product model. SmoothReconstruction means, for every ColumnChart c, real ContMDiff of (x,w) mapped to (x,c.intoRange hidem x w), using the same topology and bundle instances. All nine predicates in the displayed conjunction have these definitions; together with the quantified a they are the full constructor statement.")),
            Paragraph(Text("Let B be any real smooth manifold modeled by I, and let p be a smooth n by n complex matrix field with p(x)*=p(x), p(x)^2=p(x), and constant rank r. The fiber is the actual range of Matrix.toEuclideanLin(p(x)) inside EuclideanSpace C (Fin n), with its inherited complex linear and normed structures. The model fiber is EuclideanSpace C (Fin r).")),
            Paragraph(Text("At each base point select r independent columns C of p. The local Gram certificate gives an open set on which G=C* C is invertible and the selected columns span the full projection range. Define L=G^(-1) C*. Then LC=1, and CL acts as the identity on the range. No local frame is supplied as an assumption: the columns, their domains, and both inverse maps are constructed.")),
            Paragraph(Text("The actual trivialization sends (x,v) to (x,L(x)v), and reconstruction sends (x,w) to (x,C(x)w). On overlaps the transition from chart a to chart b is L_b(x) C_a(x). Finite-coordinate multiplication and conjugation are real smooth. Inversion is transported through CStarMatrix to use the complete normed algebra inverse theorem on the open unit locus.")),
            Paragraph(Text("The real and complex prebundles use the very same pretrivialization atlas and the same selected chart at each point. Complex linearity is retained while all differentiability is over R. Their generated topologies agree by the shared construction. The real smooth vector bundle provides the real smooth total-space structure.")),
            Paragraph(Text("The ambient map sends (x,v) to the actual pair (x,v) in B times C^n. Its image is exactly the fixed-vector locus p(x)v=v. It is smooth, is an embedding, and induces precisely the constructed total-space topology. The inverse identification with the ambient range subtype is continuous. Every column reconstruction is smooth into the total space; its inverse identities are asserted on its chart domain, while the reconstruction map itself is globally defined.")),
            Paragraph(Text("The parameters n and r are arbitrary natural numbers; zero-dimensional fibers, zero ambient dimension, and an empty base are retained. There is no compactness, positivity of rank, nonempty base, global frame, or assumed bundle hypothesis. The result is a general geometric constructor. The actual Ephys and Fsyn application, the Theta tensor equivalence, positive trace-one sigma and decoder factorization, and global transport remain separate obligations. The constructor alone does not assert vanishing of a curvature integral; the application below uses the additional global transversality hypothesis.")),
            Paragraph(Text("The proof uses the pinned Mathlib vector prebundle construction, finite-dimensional linear maps, matrix rank and Gram positivity, and smooth inversion. This is the classical local-frame construction.")),
            Paragraph(Text("Application: a fixed reference space and a nonzero curvature integral. Let Sigma be a compact, boundaryless, oriented smooth real surface, and let P(x) be a smooth Hermitian idempotent n by n complex matrix of constant rank r, with 1 <= r < n. Write E_x = Ran P(x). Fix any Hermitian rank-r projection P0. The parameter map to this constructor is B = Sigma, p = P, and the same n,r; its Fiber is exactly E_x with the Euclidean norm. Compactness, orientation and real dimension two enter the integral argument below, not the local bundle constructor. No global frame, inverse restriction, curvature identity or vanishing integral is an input.")),
            Paragraph(Text("Choose orthonormal columns W0 spanning Ran P0 and W1 spanning its orthogonal complement. Rank-nullity gives rank(I-P0) = n-r. These frames can be constructed from the existing column-chart existence result applied to the constant projections P0 and I-P0: for independent spanning columns C, replace C by C(C* C)^(-1/2). Positive Gram calculus gives Wj* Wj = I, W0* W1 = 0, W0 W0* = P0 and W1 W1* = I-P0. Thus W0 W0* + W1 W1* = I. Here * denotes conjugate transpose, and every norm below is the induced operator norm between the indicated complex Euclidean spaces.")),
            Paragraph(Text("Say that x is transverse to P0 when P0 restricted to E_x is injective. Its domain and target both have dimension r, so this restriction is an isomorphism. In the coordinates W0, its adjoint is the map a |-> P(x)W0 a; hence G(x) = W0* P(x)W0 is positive definite. Conversely, positivity of this Gram matrix makes that adjoint an isomorphism and gives the same transversality. On a transverse region define U = P W0 G^(-1/2), using the positive Hermitian square root. Then U* U = G^(-1/2) G G^(-1/2) = I. Its r-dimensional range lies in E_x and therefore equals E_x, so U U* = P. The same formulas define the frame used in the connection, obstruction and compression calculations below.")),
            Paragraph(Text("This U is smooth wherever transversality holds. The existing Prebundle smooth multiplication, adjoint and inversion results reduce this to smoothness of the positive square root. For a positive Hermitian Y, the derivative of Y |-> Y^2 is H |-> YH+HY; diagonalizing Y multiplies each matrix entry by a strictly positive eigenvalue sum. This derivative is invertible on the real Hermitian space. The existing Hermitian square-derivative and Jordan-conjugation results, followed by the pinned inverse-function theorem, give a smooth local inverse. The identity (sqrt G)^2 = G and uniqueness of that local inverse identify it with the positive functional-calculus root. Positivity is open, so these neighborhoods give the required smooth root and then its smooth inverse. This is an application of existing calculus, rather than an additional assumed smoothness certificate.")),
            Paragraph(Text("For this actual isometric U, use the physical convention A = i U* dU and F = dA - i A wedge A. The ordinary exterior derivative and product rule give dA = i dU* wedge dU. Differentiating U* U = I and P = U U* then gives F = i dU* (I-P) wedge dU = i U* (dP wedge dP) U. Rectangular cyclicity of trace identifies tr F with i tr(P(dP wedge dP)), so this two-form depends on P, not on the chosen local isometric frame. Evaluated on real tangent vectors, F is Hermitian and tr F is real. These are identities of the same matrices and differential forms, not independent curvature premises.")),
            Paragraph(Text("Define C1 here by the literal physical integral (2 pi)^(-1) times the integral over Sigma of Re(i tr(P(dP wedge dP))). If transversality holds everywhere, U above is a global smooth frame. The trace of A wedge A vanishes: on two tangent vectors it is the trace of a commutator. Consequently tr F = d tr A. Taking real and imaginary parts commutes with d; their smooth primitives have compact support on the compact base. Boundaryless Stokes applied to these real forms makes both integrals zero, and in particular gives C1 = 0. This uses the actual surface integral, not an abstract functional chosen to vanish. The customary identification with an integral Chern class and its integer-valuedness are background facts; neither is needed for the implication from a nonzero value of this integral.")),
            Paragraph(Text("Suppose this C1 is nonzero. The base is nonempty, since integration over the empty base is zero. Global transversality would give the preceding contradiction, so some x admits a nonzero v in E_x with P0 v = 0. Normalize it by its Euclidean norm to get a unit vector w with P(x)w = w and P0 w = 0. Thus (I-P0)P(x)w = w, which gives operator norm at least one. Every orthogonal projection is a contraction, so ||(I-P0)P(y)|| <= 1 for every y. The value one is therefore attained at x and is the maximum over Sigma, for each fixed rank-r P0. This is an actual unit-vector witness and an attained maximum, not just a supremum estimate.")),
            Paragraph(Text("At any single transverse point, set V = P W0 G^(-1) and X = W1* V, an (n-r) by r matrix. From W0* V = I and the complete orthogonal splitting one gets V = W0 + W1 X. Idempotence of P gives V* V = G^(-1), while the splitting gives V* V = I + X* X. Hence the same normalized frame is U = (W0 + W1 X)(I + X* X)^(-1/2), and its compression by the original reference projection is U* P0 U = (I + X* X)^(-1). This calculation is pointwise; transversality elsewhere on Sigma is unnecessary.")),
            Paragraph(Text("For r >= 1, the positive matrix X* X has a largest eigenvalue equal to ||X||^2. Functional calculus sends an eigenvalue t to (1+t)^(-1), a decreasing function on t >= 0. Therefore the actual least eigenvalue of U* P0 U is 1/(1+||X||^2). When X = 0 this gives one without any division by ||X||. Rank zero is permitted by the general bundle constructor, but its empty eigenvalue range has no least member; this least-eigenvalue conclusion is asserted only for positive r. The empty-base and zero-dimensional cases are not silently excluded from the constructor.")),
            Paragraph(Text("These formulas give the classical fixed-reference graph obstruction in original ST23.2. They reuse ProjectionRange.exists_columnChart, ProjectionRange.smooth_mul, ProjectionRange.smooth_adj and ProjectionRange.smooth_inv; the existing HermitianCubeDerivative and HermitianHypersurfaceCalculus square/Jordan calculus; pinned positive spectral calculus and inverse-function results; and the pinned differential-form naturality and boundaryless Stokes results. This is the classical projection-bundle and Stokes argument specialized to a fixed reference subspace. Failure of a single fixed graph chart does not assert closure of a Hamiltonian energy gap. The subspace-loss quantity ||(I-P0)P(x)||^2 is distinct from the leakage of an actual measurement instrument. Finite compatible atlases, the ST24 control bounds and the ST25 examples require their own arguments.")),
            Describe.Remark(
                DescribeId.Create("projectionrange-v"),
                DeclarationHandle.Create(Prefix + "V"),
                H("V"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("EuclideanSpace over complex Fin k; no positivity assumption.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-rangesubmodule"),
                DeclarationHandle.Create(Prefix + "rangeSubmodule"),
                H("rangeSubmodule"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("LinearMap.range of Matrix.toEuclideanLin applied to p x.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-fiber"),
                DeclarationHandle.Create(Prefix + "Fiber"),
                H("Fiber"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Subtype of the actual Euclidean range with inherited structures.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-columns"),
                DeclarationHandle.Create(Prefix + "columns"),
                H("columns"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Select entries p x i (J j); rectangular matrix n by r.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-gram"),
                DeclarationHandle.Create(Prefix + "gram"),
                H("gram"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Conjugate transpose of selected columns times selected columns.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-leftmatrix"),
                DeclarationHandle.Create(Prefix + "leftMatrix"),
                H("leftMatrix"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Inverse Gram times conjugate transpose of columns.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-columnchart"),
                DeclarationHandle.Create(Prefix + "ColumnChart"),
                H("ColumnChart"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Data J,U with injectivity, open set, invertible Gram and spanning equality; constructor builds this data.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-exists-columnchart"),
                DeclarationHandle.Create(Prefix + "exists_columnChart"),
                H("exists_columnChart"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Apply unchanged exact_original_local_gram_certificate on univ; PSD from Hermitian idempotence; rank equality from constant matrix rank; unpack U and span witness.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-chartat"),
                DeclarationHandle.Create(Prefix + "chartAt"),
                H("chartAt"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Classical.choose of pointwise chart existence; the chart can vary with base point.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-mem-chartat"),
                DeclarationHandle.Create(Prefix + "mem_chartAt"),
                H("mem_chartAt"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Choose_spec of the same chart existence; supplies base-set membership.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-euclidean-range-eq-of-span-eq"),
                DeclarationHandle.Create(Prefix + "euclidean_range_eq_of_span_eq"),
                H("euclidean_range_eq_of_span_eq"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use Matrix.range_mulVecLin for function-coordinate ranges and WithLp transport of witnesses in both directions.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-columnchart-left-mul-columns"),
                DeclarationHandle.Create(Prefix + "left_mul_columns"),
                H("left_mul_columns"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Associate inverse Gram times Gram; use Matrix.nonsing_inv_mul via invertible determinant.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-columnchart-range-columns"),
                DeclarationHandle.Create(Prefix + "range_columns"),
                H("range_columns"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Apply euclidean_range_eq_of_span_eq to the supplier span equality.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-columnchart-projection-columns"),
                DeclarationHandle.Create(Prefix + "projection_columns"),
                H("projection_columns"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Select columns on both sides of p*p=p using congrArg; no new projection theorem.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-columnchart-intorange"),
                DeclarationHandle.Create(Prefix + "intoRange"),
                H("intoRange"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("codRestrict selected-column Euclidean linear map to actual range, witnessing membership by the same column image and idempotence.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-columnchart-coordinates"),
                DeclarationHandle.Create(Prefix + "coordinates"),
                H("coordinates"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Euclidean linear map of inverse-Gram leftMatrix composed with range subtype inclusion.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-columnchart-coordinates-intorange"),
                DeclarationHandle.Create(Prefix + "coordinates_intoRange"),
                H("coordinates_intoRange"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Rewrite composed Euclidean maps as matrix product, then left_mul_columns and identity matrix map.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-columnchart-intorange-coordinates"),
                DeclarationHandle.Create(Prefix + "intoRange_coordinates"),
                H("intoRange_coordinates"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Represent range vector by selected columns using range_columns; reduce to coordinates_intoRange via Subtype.ext.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-columnchart-equiv"),
                DeclarationHandle.Create(Prefix + "equiv"),
                H("equiv"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Linear equivalence with forward coordinates and inverse intoRange; both inverse laws supplied.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-columnchart-equivl"),
                DeclarationHandle.Create(Prefix + "equivL"),
                H("equivL"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Promote existing finite-dimensional LinearEquiv by toContinuousLinearEquiv.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-columnchart-pretrivialization"),
                DeclarationHandle.Create(Prefix + "pretrivialization"),
                H("pretrivialization"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual TotalSpace to base-coordinate pair, inverse base-column image; source preimage U and target U times univ; inverse laws above.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-columnchart-complex-linear"),
                DeclarationHandle.Create(Prefix + "complex_linear"),
                H("complex_linear"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use coordinates.isLinear at each base point.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-columnchart-real-linear"),
                DeclarationHandle.Create(Prefix + "real_linear"),
                H("real_linear"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Restrict coordinates linear map to real scalars then use isLinear.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-columnchart-symm-eq"),
                DeclarationHandle.Create(Prefix + "symm_eq"),
                H("symm_eq"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Apply injectivity of local linear equivalence and Pretrivialization.apply_mk_symm; identify bundle inverse with actual intoRange.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-columnchart-inducing"),
                DeclarationHandle.Create(Prefix + "inducing"),
                H("inducing"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use isInducing_const_prod and homeomorphism underlying equivL.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-columnchart-transition"),
                DeclarationHandle.Create(Prefix + "transition"),
                H("transition"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Matrix leftMatrix for destination b times columns for source a; beta-after-alpha direction.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-columnchart-transition-apply"),
                DeclarationHandle.Create(Prefix + "transition_apply"),
                H("transition_apply"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use symm_eq on source chart and Matrix.toLpLin_mul_same to match transition evaluation with chart change.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-matrixcle"),
                DeclarationHandle.Create(Prefix + "matrixCLE"),
                H("matrixCLE"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Compose Matrix.toEuclideanLin and LinearMap.toContinuousLinearMap, then finite-dimensional toContinuousLinearEquiv.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-matrixrealclm"),
                DeclarationHandle.Create(Prefix + "matrixRealCLM"),
                H("matrixRealCLM"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Convert matrix to complex operator, restrict outer map to real scalars, then apply restrictScalarsL to operator values.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-smooth-mul"),
                DeclarationHandle.Create(Prefix + "smooth_mul"),
                H("smooth_mul"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Coordinatewise finite sums of scalar products, applying contDiff_mul and manifold product composition.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-smooth-adj"),
                DeclarationHandle.Create(Prefix + "smooth_adj"),
                H("smooth_adj"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Coordinatewise Complex.conjCLE smoothness after transposed coordinate projections.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-smooth-inv"),
                DeclarationHandle.Create(Prefix + "smooth_inv"),
                H("smooth_inv"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Transport to CStarMatrix normed algebra, apply contDiffAt_ringInverse at a unit, then use local unit openness and inverse uniqueness.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-smooth-columns"),
                DeclarationHandle.Create(Prefix + "smooth_columns"),
                H("smooth_columns"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Twice use contMDiffAt_pi_space on hp to select coordinate J j.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-smooth-left"),
                DeclarationHandle.Create(Prefix + "smooth_left"),
                H("smooth_left"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Combine smooth columns, adjoint, multiplication and unit-locus inversion with gram_unit.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-smooth-transition"),
                DeclarationHandle.Create(Prefix + "smooth_transition"),
                H("smooth_transition"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Multiply smooth destination leftMatrix with smooth source columns on chart overlap.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-prebundle"),
                DeclarationHandle.Create(Prefix + "prebundle"),
                H("prebundle"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Real VectorPrebundle with constructed atlas, selected chartAt and real matrix operators as overlap witnesses; inducing from actual fibers.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-complexprebundle"),
                DeclarationHandle.Create(Prefix + "complexPrebundle"),
                H("complexPrebundle"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Same pretrivialization atlas and selected charts; complex operators remain complex-valued, outer CLM is restricted to real scalars for calculus.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-smooth-prebundle"),
                DeclarationHandle.Create(Prefix + "smooth_prebundle"),
                H("smooth_prebundle"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Supply actual real smooth overlap operators to VectorPrebundle.IsContMDiff.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-ambient"),
                DeclarationHandle.Create(Prefix + "ambient"),
                H("ambient"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Map actual dependent total-space point to pair of its base and subtype value.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-mem-fiber-iff-fixed"),
                DeclarationHandle.Create(Prefix + "mem_fiber_iff_fixed"),
                H("mem_fiber_iff_fixed"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Apply pinned Mathlib LinearMap.IsIdempotentElem.mem_range_iff to Matrix.toEuclideanLin (p x), with idempotence transported from hidem by Matrix.toLpLin_mul_same; the fixed vector then witnesses its own range membership.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-ambient-range"),
                DeclarationHandle.Create(Prefix + "ambient_range"),
                H("ambient_range"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two inclusions using mem_fiber_iff_fixed; actual image is fixed-point locus.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-smooth-ambient"),
                DeclarationHandle.Create(Prefix + "smooth_ambient"),
                H("smooth_ambient"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Bundle total-space criterion yields smooth projection and local coordinates; reconstruct ambient vector by smooth columns, using intoRange_coordinates eventually on chart U.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-smooth-intorange"),
                DeclarationHandle.Create(Prefix + "smooth_intoRange"),
                H("smooth_intoRange"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Bundle total-space criterion reduces to smooth base projection and leftMatrix-times-columns evaluation; typed Eventually.of_forall plus Matrix.toLpLin_mul_same identifies exact coordinates.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-finrank-fiber"),
                DeclarationHandle.Create(Prefix + "finrank_fiber"),
                H("finrank_fiber"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Local actual range linear equivalence gives finrank equality; Euclidean Fin r has complex finrank r.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-ambientrange"),
                DeclarationHandle.Create(Prefix + "AmbientRange"),
                H("AmbientRange"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Subtype of ambient B times V n with actual range membership; inherited subtype topology.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-continuous-toambientrange"),
                DeclarationHandle.Create(Prefix + "continuous_toAmbientRange"),
                H("continuous_toAmbientRange"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Take continuity of smooth_ambient then Continuous.subtype_mk with actual membership proof.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-continuous-fromambientrange"),
                DeclarationHandle.Create(Prefix + "continuous_fromAmbientRange"),
                H("continuous_fromAmbientRange"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("FiberBundle.continuousAt_totalSpace; typed base map from ambient subtype; compose smooth_left operator at z.val.fst with that map using explicit f and x, then clm_apply subtype second projection.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-ambienthomeomorph"),
                DeclarationHandle.Create(Prefix + "ambientHomeomorph"),
                H("ambientHomeomorph"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Repackage actual TotalSpace and AmbientRange coordinates, rfl inverse laws; consume both continuity lemmas without re-expanding their proofs.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-ambient-isembedding"),
                DeclarationHandle.Create(Prefix + "ambient_isEmbedding"),
                H("ambient_isEmbedding"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Compose ambientHomeomorph.isEmbedding with IsEmbedding.subtypeVal.")))),
            Describe.Remark(
                DescribeId.Create("projectionrange-totaltopology-eq-induced"),
                DeclarationHandle.Create(Prefix + "totalTopology_eq_induced"),
                H("totalTopology_eq_induced"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Apply IsInducing.eq_induced to ambient_isEmbedding.")))),
            Describe.Lean(
                DescribeId.Create("projectionrange-smooth-projection-range-prebundle"),
                DeclarationHandle.Create(Prefix + "smooth_projection_range_prebundle"),
                H("smooth_projection_range_prebundle"),
                StatementSource.FromAuthor(ConstructorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Return prebundle hp hstar hidem hrank as existential witness; consume smooth_prebundle, finrank_fiber, complexPrebundle.toVectorBundle, contMDiffVectorBundle, embedding, induced topology, fixed-point image, smooth ambient map and every chart reconstruction."))),
                DescribeRole.Theorem)),
        []));

    private static Formula ConstructorFormula()
    {
        Formula q = F.Id("q"), a = F.Id("a");
        Formula[] clauses = [
            Call("SmoothAtlas", q, a), Call("ComplexRank", q),
            Call("ComplexBundle", q, a), Call("RealSmoothBundle", q, a),
            Call("AmbientEmbedding", q, a), Call("InducedTopology", q, a),
            Call("FixedImage", q), Call("SmoothAmbient", q, a),
            Call("SmoothReconstruction", q, a)];
        return F.Disp(F.Seq(F.Forall, F.Sp, q, F.InMacro, F.Sp, F.Id("SmoothProjectionData"),
            F.Comma, F.Sp, F.Exists, F.Sp, a, F.InMacro, F.Sp, Call("RealPrebundle", q),
            F.Comma, F.Sp, Conjunction(clauses), F.Dot));
    }

    private static Formula Conjunction(Formula[] clauses)
    {
        var result = clauses[0];
        for (var i = 1; i < clauses.Length; i++)
            result = F.Seq(result, F.Sp, F.Land, F.Sp, clauses[i]);
        return F.Grp(result);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
}
