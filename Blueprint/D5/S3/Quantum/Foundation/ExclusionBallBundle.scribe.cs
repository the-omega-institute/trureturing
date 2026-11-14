using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class ExclusionBallBundleDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/ExclusionBallBundle.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unique continuous affine ellipsoids and actual metric range bundles of the entire original Q1 family.",
        H("The original exclusion ellipsoids and metric range bundles"), Blocks(
        Paragraph(Text("V is an arbitrary nonzero finite dimensional real normed space. C is the entire closed pointed generating convex cone, u is strictly positive away from zero on C, K is the entire section u equal to one, and P is the entire extreme locus of K. Exclusion uses every effect between zero and u on the original cone and every state, including mixed states. Q1 means that every original pure label has an injective affine parametrization of its entire exclusion by the Euclidean closed three-ball and that every such exclusion has original whole-effect width one.")),
        Describe.Lean(DescribeId.Create("whole-exclusion"),
            DeclarationHandle.Create(Owner + "wholeExclusion"), H("The whole compact exclusion"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("The carrier is the original exclusion subset of V, equipped with its derived compactness and nonemptiness. Its hyperspace topology is the Hausdorff topology of nonempty compact subsets of the original normed carrier. No pure-only replacement or selected zero set is used."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("whole-exclusion-continuous"),
            DeclarationHandle.Create(Owner + "whole_exclusion_continuous"),
            H("Q1 implies whole-family continuity"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("The mapping from every original pure label to its entire exclusion is continuous. Its only premises are the cone and unit assumptions and Q1. Pure closedness follows because all labels lie in the compact saturated-label locus. The positive lower bound for every direction of every chart is reused directly from ExclusionUniformNoncollapse.all_label_uniform_noncollapse.")),
            Paragraph(Text("Choose an entire affine three-ball chart at each label without asserting that the choice is continuous. Compactness of K bounds all centers and all chart operators. Along any convergent label sequence and any subsequence, a further subsequence of center and operator pairs converges. The paid uniform lower estimate passes to the limit and makes its linear part injective. Closedness of P puts its entire sphere in the extreme locus of K. Original upper incidence puts its entire mixed ball inside the exclusion of the limiting label. AffineBallRigidity.eq_of_subset_of_extreme_sphere upgrades this containment to equality because both balls have the same injective three-dimensional source. Continuous images in the compact hyperspace then give the desired limit for each subsequence, hence continuity.")),
            Paragraph(Text("This continuity statement does not assume Pair, weakPair, PR, edge lifting, a continuous selection of charts, a common physical metric, or a matrix-model identification. Hausdorff continuity alone does not assert the shape-operator or vector-bundle conclusions.")))),
        Describe.Lean(DescribeId.Create("chart-center"),
            DeclarationHandle.Create(Owner + "chartCenter"), H("The original affine center"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("The value at zero of an entire affine ball chart is regarded as a point of V. Its unit reading is one. It is not a vector in the kernel of u; only differences from this center are kernel vectors."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("original-center-continuous"),
            DeclarationHandle.Create(Owner + "original_center_continuous"),
            H("Continuous chart-independent centers"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("Under the same original cone assumptions and Q1, the centers vary continuously, lie in K, and agree with the value at zero of every entire affine ball chart of the corresponding exclusion. Equality of compact affine balls gives equality of their centers by AffineBallRigidity.center_eq_of_ball_eq. Once whole-ball convergence is known, ExclusionIncidence.parameter_subsequence extracts convergent chart parameters with precisely that compact limit. Every resulting center limit is therefore the center at the limiting label. This establishes continuity without choosing charts continuously.")),
            Paragraph(Text("Only differences from the affine center are transported to the actual kernel. The auxiliary Euclidean realization below is supplied by a typed linear equivalence; its norm and topology correspondence is derived by finite dimensional automatic continuity.")))),
        Describe.Lean(DescribeId.Create("kernel-inclusion"),
            DeclarationHandle.Create("D5/S3/Quantum/Foundation/ExclusionBallBundle.kernelInclusion"), H("The typed actual kernel inclusion"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("For any Euclidean realization e from the actual kernel of u to H, this is the actual subtype inclusion composed with the inverse of e. The affine center remains a V-valued point of the unit plane."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("auxiliary-linear"),
            DeclarationHandle.Create("D5/S3/Quantum/Foundation/ExclusionBallBundle.auxiliaryLinear"), H("Every chart in the auxiliary metric"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("The linear part of every original affine chart has unit reading zero. It therefore lands in the actual kernel and is transported through e."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("auxiliary-metric-uniform-charts"),
            DeclarationHandle.Create("D5/S3/Quantum/Foundation/ExclusionBallBundle.auxiliary_metric_uniform_charts"), H("Metric-dependent uniform bounds"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("The original and auxiliary norms induce the same topology by finite dimensional automatic continuity of e and its inverse. For each fixed e there are common positive constants eta at most R, before every original pure label and every entire three-ball chart. Every source direction has auxiliary image norm between eta and R times its norm. The same constants bound every one of the three singular semiaxes, using the existing right singular basis and Gram orthogonality owner directly. The original frozen noncollapse bound is applied directly, and compactness of K gives the upper bound. No metric-independent constants are asserted under rescaling.")))),
        Describe.Lean(DescribeId.Create("shape-operator"),
            DeclarationHandle.Create("D5/S3/Quantum/Foundation/ExclusionBallBundle.shapeOperator"), H("The auxiliary positive shape"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("An arbitrary original entire three-ball chart gives A A adjoint in the chosen Euclidean realization. The subsequent theorem proves that the result is independent of every original chart."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("actual-kernel-shape"),
            DeclarationHandle.Create("D5/S3/Quantum/Foundation/ExclusionBallBundle.actualKernelShape"), H("The actual kernel endomorphism"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("The auxiliary shape is conjugated through the explicitly supplied e to an endomorphism of the actual kernel of u. This transport does not move the affine center into the kernel."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("original-shape-continuous"),
            DeclarationHandle.Create("D5/S3/Quantum/Foundation/ExclusionBallBundle.original_shape_continuous"), H("Continuous actual rank-three shape"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("Under the unchanged original cone assumptions and Q1, the positive shape is continuous, has actual image dimension three, and agrees with the Gram operator of every original chart. Uniform boundedness extracts convergent chart operators along subsequences. Whole-exclusion continuity and actual affine-center continuity identify their entire limiting balls. Ball-image shape uniqueness then identifies the operator limit.")))),
        Describe.Lean(DescribeId.Create("shape-dagger"),
            DeclarationHandle.Create("D5/S3/Quantum/Foundation/ExclusionBallBundle.shapeDagger"), H("The actual Moore-Penrose inverse"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("This is exactly the frozen FiniteMoorePenroseInverse of the actual positive shape, converted to a continuous linear map."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("fiber-metric"),
            DeclarationHandle.Create("D5/S3/Quantum/Foundation/ExclusionBallBundle.fiberMetric"), H("The inverse-shape form"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("The form is inner(v,Q dagger w) in the chosen auxiliary metric. Its positive definiteness belongs to the actual range of Q."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("original-inverse-continuous"),
            DeclarationHandle.Create("D5/S3/Quantum/Foundation/ExclusionBallBundle.original_inverse_continuous"), H("Continuous inverse, projection and form"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("The common metric-dependent lower bound controls the actual inverse norm. The actual inverse family is continuous. Q composed with its inverse is the actual auxiliary orthogonal projection onto its image, so those projections are continuous. Evaluation and the inner product give joint continuity of the form.")))),
        Describe.Lean(DescribeId.Create("original-metric-disc"),
            DeclarationHandle.Create("D5/S3/Quantum/Foundation/ExclusionBallBundle.original_metric_disc"), H("The actual disc and its boundary"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("The inverse-shape form is positive definite on the actual image. Center plus actual kernel inclusion of v belongs to the entire original exclusion exactly when v belongs to that image and its metric square is at most one. Membership in the actual intrinsic frontier is exactly image membership and metric square equal to one. Thus an ambient semidefinite cylinder is excluded.")))),
        Describe.Lean(DescribeId.Create("shape-sqrt"),
            DeclarationHandle.Create("D5/S3/Quantum/Foundation/ExclusionBallBundle.shapeSqrt"), H("The whole ambient square root"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("This is the unique positive square root of the positive shape on all H, including its kernel."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("original-ellipsoid-unique"),
            DeclarationHandle.Create("D5/S3/Quantum/Foundation/ExclusionBallBundle.original_ellipsoid_unique"), H("Unique actual affine ellipsoid"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("The actual affine center has unit reading one. The shape is positive of rank three, its full ambient positive square root is continuous, and its entire ambient closed-ball image translated by that actual center is exactly the original exclusion. Any affine center and positive operator with the same entire representation equal these values. The center is compared in V, and the shape comparison takes place only after the typed kernel identification.")))),
        Describe.Lean(DescribeId.Create("original-range-bundle"),
            DeclarationHandle.Create("D5/S3/Quantum/Foundation/ExclusionBallBundle.original_range_bundle"), H("The actual real rank-three vector bundle"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("Under the original Q1 telescope, the actual images of the shape operators form a genuine real VectorPrebundle with Euclidean three-space model. Its generated VectorBundle topology is exactly the topology induced by the range graph in P times H. Projection continuity and rank are derived outputs, not new assumptions. The conjugated endomorphism on the literal kernel has continuous operator family, rank three, and self-adjoint positive form for the pulled-back auxiliary inner product. Its actual range graph is homeomorphic, preserving the original label and via the supplied e, to the displayed Euclidean realization. The fiber identification is an actual linear equivalence of the ranges.")))),
        Describe.Lean(DescribeId.Create("original-normalized-local-products"),
            DeclarationHandle.Create("D5/S3/Quantum/Foundation/ExclusionBallBundle.original_normalized_local_products"), H("Actual normalized local disc and sphere products"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("At every original pure label there is a continuous local linear chart of the actual image bundle that preserves the actual inverse-shape metric. Its neighborhood of the entire original centered exclusions is homeomorphic to the neighborhood times the closed Euclidean three-ball. The actual intrinsic boundaries have the sphere product. Both inverse maps are continuous and both directions of every overlap transition are continuous. No global frame or continuous choice of the original ball charts is assumed."))))) ));
}
