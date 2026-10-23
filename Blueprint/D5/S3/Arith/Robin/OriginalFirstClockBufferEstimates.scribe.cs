using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class OriginalFirstClockBufferEstimatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/OriginalFirstClockBufferEstimates.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Consumed estimates for the original first-clock prime buffer",
        H("OriginalFirstClockBufferEstimates"),
        Blocks(
            Paragraph(Text(
                "These estimates support OriginalFirstClockTransport.good_edge_prime_buffer. "
                + "The density is ActualRobinClockCovariance.activationDensity "
                + "w(x)=(log(x)+1)/(x^2*log(x)^2). The logarithm window bound is stated in LogarithmBounds.")),
            Describe.Lean(
                DescribeId.Create("original-first-clock-buffer-density-left"),
                DeclarationHandle.Create(Prefix + "buffer_density_left"),
                H("Backward density comparison"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real x>=256 and 0<h<=x/20, (81/100)*w(x-h)<=w(x). "
                    + "The original lower-end deletion argument consumes this comparison."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-first-clock-buffer-density-right"),
                DeclarationHandle.Create(Prefix + "buffer_density_right"),
                H("Strict forward density comparison"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real x>=256 and 0<h<=x/20, (81/100)*w(x)<w(x+h). "
                    + "The original upper-end insertion argument consumes the strict inequality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-first-clock-buffer-integer-removal"),
                DeclarationHandle.Create(Prefix + "buffer_integer_removal_comparison"),
                H("Integer removal from a literal nonlinear objective comparison"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let M>=1, q be prime, and M*q=N. Assume the literal inequality "
                    + "log(sigma(M)/M)-log(log(log(M))) <= "
                    + "log(sigma(N)/N)-log(log(log(N))). Then "
                    + "log(log(log(N)))-log(log(log(M)))<=log(1+1/q). "
                    + "The existing exact single-layer delta and decrease of Euler marginals "
                    + "prove the estimate with arbitrary multiplicity of q. The original "
                    + "consumer supplies this input inequality from full maximality on the "
                    + "5040*p class and its legal competitor M; no forced divisibility "
                    + "condition is removed from the good-edge theorem."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The density comparisons and integer removal estimate support the endpoint "
                + "exclusions with the full GoodEdge hypotheses and the 5040 threshold.")))));
}
