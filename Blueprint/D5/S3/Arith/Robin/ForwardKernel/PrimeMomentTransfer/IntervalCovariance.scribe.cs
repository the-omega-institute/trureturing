using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class IntervalCovarianceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/IntervalCovariance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A linear square-sum error bound gives a uniform covariance estimate for scaled intervals.",
        H("Conditional interval covariance"),
        Blocks(
            Describe.Lean(DescribeId.Create("interval-overlap"), DeclarationHandle.Create(Prefix + "overlap"), H("Overlap length"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The overlap length of the ordered intervals (a,b] and (c,d] is the nonnegative part of min(b,d) minus max(a,c)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("interval-sum"), DeclarationHandle.Create(Prefix + "intervalSum"), H("Scaled interval kernel sum"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Sum the kernel over the integer intervals with endpoints given by the natural floors of aH, bH, cH and dH."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("interval-covariance-bound"), DeclarationHandle.Create(Prefix + "interval_covariance_bound"), H("Uniform interval covariance bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every M at least one and every nonnegative square-sum error constant C₀, there is a nonnegative constant C depending only on M and C₀. For every symmetric translation-invariant kernel whose square prefix sum differs from minus m log m by at most C₀ times m for all positive integers m, the absolute difference between each scaled interval sum and minus H log H times the overlap length is at most C times H, uniformly for H at least one and all ordered endpoints in [0,M], including empty intervals."))), DescribeRole.Theorem))));
}
