using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Probability;

internal sealed class FiniteGaussianSchoenbergDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/Probability/FiniteGaussianSchoenberg.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Classical finite Gram Schoenberg positivity with the actual entrywise exponential.",
        H("FiniteGaussianSchoenberg"), Blocks(
            Describe.Lean(DescribeId.Create("entrywise-exp-possemidef"),
                DeclarationHandle.Create(Prefix + "entrywise_exp_posSemidef"), H("Entrywise exponential is positive"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Schur powers with nonnegative factorial weights converge entrywise to the scalar exponential. Every finite real quadratic inequality passes to the limit."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gram-distance-zero-sum"),
                DeclarationHandle.Create(Prefix + "gram_distance_zero_sum"), H("Exact zero-sum distance identity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every zero-sum real vector the squared Gram-distance form is minus twice its original Gram quadratic form."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gram-distance-conditionally-negative"),
                DeclarationHandle.Create(Prefix + "gram_distance_conditionally_negative"), H("Squared Gram distance has negative type"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact zero-sum identity and Gram positivity give conditional negative definiteness; singular matrices and repeated points are retained."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("real-gram-gaussian-possemidef"),
                DeclarationHandle.Create(Prefix + "real_gram_gaussian_posSemidef"), H("Real Gaussian positivity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exponential of negative squared Gram distance factors as positive diagonal congruence of the entrywise exponential of twice the time-scaled Gram matrix."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ofreal-possemidef"),
                DeclarationHandle.Create(Prefix + "ofReal_posSemidef"), H("Retain complex coefficient tests"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A real Gram factorization is mapped to complex scalars, proving positivity against every complex vector."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gram-gaussian-possemidef"),
                DeclarationHandle.Create(Prefix + "gram_gaussian_posSemidef"), H("Complex Gaussian positivity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The forward finite Gram form of Schoenberg is proved for all nonnegative real times, including zero time. No exponential positivity premise is supplied."))), DescribeRole.Theorem))));
}
