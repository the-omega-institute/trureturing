using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Probability;

internal sealed class LiCurvatureSchoenbergSemigroupDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/Probability/LiCurvatureSchoenbergSemigroup.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The constructed Li probability evolution closes the specific forward Schoenberg connection.",
        H("LiCurvatureSchoenbergSemigroup"), Blocks(
            Describe.Lean(DescribeId.Create("reconstructed-li-probability-semigroup"),
                DeclarationHandle.Create(Prefix + "reconstructed_li_probability_semigroup"), H("Actual probability evolution from the original energy"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The integrated geometric Gram and forward Schoenberg prove every exponential matrix condition needed by the existing circle semigroup constructor."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("semigroup-nsmul-convolution"),
                DeclarationHandle.Create(Prefix + "semigroup_nsmul_convolution"), H("Natural multiples are iterated convolution"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every natural multiple of a time is the actual repeated multiplicative convolution beginning with delta at the identity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("semigroup-probability-roots"),
                DeclarationHandle.Create(Prefix + "semigroup_probability_roots"), H("Probability roots of every positive order"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The root is the same probability family at time t divided by the positive integer order; the iterated convolution is proved equal to the original marginal."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normalized-curvature-conditionally-negative"),
                DeclarationHandle.Create(Prefix + "normalized_curvature_conditionally_negative"), H("Negative type from the original curvature data"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The representing measure is constructed from the normalized positive curvature and original recurrence. All finite integer samples and zero-sum real vectors are covered."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normalized-curvature-quadratic-bound"),
                DeclarationHandle.Create(Prefix + "normalized_curvature_quadratic_bound"), H("Control the entire original coefficient growth"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The constructed probability representation gives zero-to-L1-times-n-squared bounds at every index. This supplies a concrete bound for a subsequent canonical generating-function continuation."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normalized-curvature-probability-evolution"),
                DeclarationHandle.Create(Prefix + "normalized_curvature_probability_evolution"), H("Full normalized-curvature probability evolution"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same original Li-type sequence determines a unique weakly continuous probability semigroup and all convolution roots. No representing measure, negative-type property or exponential positivity is supplied as an additional premise."))), DescribeRole.Theorem))));
}
