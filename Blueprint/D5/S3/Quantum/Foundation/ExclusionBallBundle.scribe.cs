using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class ExclusionBallBundleDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/ExclusionBallBundle.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hausdorff continuity of the entire original saturated three-ball exclusion family.",
        H("Continuity of the original exclusion balls"), Blocks(
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
            Paragraph(Text("The shape operators for every auxiliary Euclidean metric on the kernel of u, their actual Moore-Penrose inverses and orthogonal image projections, and the real rank-three range bundle with normalized local disc and sphere charts remain separate mathematical conclusions."))))) ));
}
