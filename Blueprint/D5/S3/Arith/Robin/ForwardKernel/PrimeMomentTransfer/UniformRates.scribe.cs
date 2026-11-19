using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class UniformRatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/UniformRates.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The error rates in cubic and fourth moment transfer vanish uniformly over polynomial length bands.",
        H("Uniform transfer rates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("transfer-epsilon-exists"),
                DeclarationHandle.Create(Prefix + "transfer_epsilon_exists"),
                H("A positive transfer exponent"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every beta less than one quarter, there is a positive epsilon less than one half minus twice beta."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sqrt-rate"),
                DeclarationHandle.Create(Prefix + "sqrt_rate"),
                H("The sampling square-root rate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive alpha and positive tolerance delta, sqrt(log(N)/H) is at most delta for all sufficiently large real N, uniformly over every real H at least N to the power alpha."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("arithmetic-rate-three"),
                DeclarationHandle.Create(Prefix + "arithmetic_rate_three"),
                H("The cubic arithmetic rate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If beta and epsilon are positive and epsilon is less than one half minus three halves times beta, then N to the power minus one half plus epsilon, times H to the power three halves, times log(N) to the power minus three halves, tends to zero uniformly for real H between one and N to the power beta."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("arithmetic-rate-four"),
                DeclarationHandle.Create(Prefix + "arithmetic_rate_four"),
                H("The fourth arithmetic rate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive epsilon less than one half minus twice beta, N to the power minus one half plus epsilon, times H squared, times log(N) to the power minus two, tends to zero uniformly for real H between zero and N to the power beta."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("inverse-log-rate"),
                DeclarationHandle.Create(Prefix + "inverse_log_rate"),
                H("The inverse logarithm rate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive delta, the reciprocal of log(N) is at most delta for all sufficiently large real N."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("antitone-modulus-rate"),
                DeclarationHandle.Create(Prefix + "antitone_modulus_rate"),
                H("An antitone error modulus"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If eta is antitone on the real numbers at least two and tends to zero at infinity, then for positive alpha and delta, eta(H) is at most both eta(N to the power alpha) and delta, uniformly for H at least N to the power alpha once N is sufficiently large."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cell-rate"),
                DeclarationHandle.Create(Prefix + "cell_rate"),
                H("The cell quadrature rate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For nonnegative beta less than one half and every natural k at most four, (H log(N)) to the power k/2 divided by N tends to zero uniformly for real H between one and N to the power beta."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("range-geometry"),
                DeclarationHandle.Create(Prefix + "range_geometry"),
                H("The eventual length window"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive alpha and M and beta less than one, all sufficiently large real N satisfy N at least two and log(N) at least one. Every real H between N to the power alpha and N to the power beta then satisfies H at least two, H at most N, and M times H at most N."))),
                DescribeRole.Theorem))));
}
