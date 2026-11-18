using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.OmegaTail;

internal sealed class LogisticGridDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite grid sampled at its right endpoints controls logistic cost and binary entropy simultaneously.",
        H("Right-endpoint logistic grids"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("right-endpoint-bounds"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTail/LogisticGrid.rightEndpoint_bounds"),
                H("Cost and entropy on a finite logistic grid"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Take a strictly increasing grid from zero to U with at least one bin and maximum width at most delta. Write q(u) = 1/(1+exp(u)) and f(u) for the binary entropy of q(u). Each bin of width w and right endpoint b contributes 2*w*b*q(b) to the cost and 2*w*f(b) to the entropy.")),
                    Paragraph(Text("The cost is at most twice the integral of u*q(u) on [0,U] plus twice delta times the integral of q. The deficit of the grid entropy from twice the integral of f lies between zero and 2*delta*(log(2)-f(U)), which is at most 2*delta*log(2).")),
                    Paragraph(Text("For a point u in a bin, the right-endpoint occupancy is at most q(u) and the right endpoint is at most u+delta. The entropy rectangles are ordered by monotonicity on the nonnegative axis. The error in each bin is bounded by delta times the drop of f across that bin. Summing cancels the intermediate endpoint values.")),
                    Paragraph(Text("The two sums use the cost and entropy inputs of the fixed-grid exchange argument. Their finite-interval bounds allow the integrated cost and missing entropy tail to be estimated before the prime-counting limit."))),
                DescribeRole.Theorem))));
}
