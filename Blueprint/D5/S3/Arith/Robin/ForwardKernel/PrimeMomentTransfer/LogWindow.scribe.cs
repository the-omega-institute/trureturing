using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class LogWindowDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/LogWindow.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform logarithmic variance and interval overlap bounds.",
        H("Logarithmic dyadic window"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("log-square-error"),
                DeclarationHandle.Create(Prefix + "log_square_error"),
                H("Variation of the squared logarithmic ratio"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For N at least two, one at most H at most N, and x in [N,2N], the squared ratio log(x/H)/log N differs from the squared ratio log(N/H)/log N by at most 3 log 2 divided by log N."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("variance-ratio-bounds"),
                DeclarationHandle.Create(Prefix + "variance_ratio_bounds"),
                H("Bounds for the logarithmic variance ratio"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For N at least two and one at most H at most N, the ratio log(N/H)/log N lies between zero and one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("w4-bound"),
                DeclarationHandle.Create(Prefix + "w4_bound"),
                H("Bounds for the fourth overlap pairing"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For four ordered intervals in [0,M] with nonnegative M, the sum of the three products of overlap lengths lies between zero and 3 M squared."))),
                DescribeRole.Theorem))));
}
