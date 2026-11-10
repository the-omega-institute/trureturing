using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.FourthTransfer;

internal sealed class FourthMomentBlockTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentBlockTransfer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed-scale mixed moments pass to finite frozen blocks, whose exact logarithmic weights approximate integration.",
        H("Logarithmically weighted frozen blocks"),
        Blocks(
            Paragraph(Text(
                "The cells have endpoints u_j=1+j/n. Each cell receives its exact "
                + "logarithmic probability log(u_(j+1)/u_j)/log(2), rather than its "
                + "Lebesgue length 1/n. Closed and left-open position indicators "
                + "agree almost everywhere by the position law and null endpoints.")),
            Describe.Lean(
                DescribeId.Create("fixed-block-moments-tendsto"),
                DeclarationHandle.Create(Prefix + "fixed_block_moments_tendsto"),
                H("Finite frozen block convergence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume interval-weighted fixed-scale mixed moment convergence "
                    + "for a kernel W. Fix a positive number of cells and frozen "
                    + "lengths in a common bounded nonnegative interval. The finite "
                    + "sum of cell moments weighted by w at the left endpoints "
                    + "converges to the same weighted sum of W times the exact "
                    + "logarithmic cell masses. This uses the fixed-scale hypothesis "
                    + "separately on each cell, followed by convergence of a finite sum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("logarithmic-block-riemann"),
                DeclarationHandle.Create(Prefix + "logarithmic_block_riemann"),
                H("Riemann sums with exact logarithmic masses"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every continuous real function f on [1,2], the sum of "
                    + "f(u_j) times the logarithmic probability of [u_j,u_(j+1)] "
                    + "converges to its integral against du/(u log(2)). Translate "
                    + "f(u)/(u log(2)) to [0,1] and apply the continuous left "
                    + "Riemann sum theorem. On each cell, the difference between "
                    + "its rectangular density weight and its exact mass is at "
                    + "most 1/(n^2 log(2)). A compact bound for f makes the "
                    + "total difference tend to zero."))),
                DescribeRole.Theorem))));
}
