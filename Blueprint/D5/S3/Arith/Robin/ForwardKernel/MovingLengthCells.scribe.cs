using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class MovingLengthCellsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal-cell limits determine the moving-length constant.",
        H("Equal-cell limits determine the moving-length constant"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cell-point-mem"),
                DeclarationHandle.Create(Prefix + "cellPoint_mem"),
                H("Cell endpoints lie in the dyadic interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For n positive and j between zero and n, the point 1+j/n lies in [1,2]."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cell-point-step"),
                DeclarationHandle.Create(Prefix + "cellPoint_step"),
                H("Equal cell widths"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two consecutive endpoints 1+j/n and 1+(j+1)/n differ by 1/n."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cell-point-lt"),
                DeclarationHandle.Create(Prefix + "cellPoint_lt"),
                H("Ordered cell endpoints"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive n each endpoint is strictly smaller than the next."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cell-mean-square-tendsto"),
                DeclarationHandle.Create(Prefix + "cell_mean_square_tendsto"),
                H("The frozen-cell mean square"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let E be measurable and bounded on compact intervals, with the short-interval mean-square bound and uniform cumulative variance band asymptotic. These imply the fixed-length triangular mean-square limit on every interval [aX,bX] with 1<=a<b<=2 and every positive length factor c. For fixed positive n, summing the square integrals with length frozen at (a_j X)^(4/5) and dividing by X^(1/5) log X tends to the sum of a_j^(-4/5)/(15n), where a_j=1+j/n. The fixed-length normalizer divided by X^(1/5) log X tends to 1/(5c)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cell-constant-tendsto"),
                DeclarationHandle.Create(Prefix + "cell_constant_tendsto"),
                H("The limiting rectangle constant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The constants (15n)^(-1) times the sum of (1+j/n)^(-4/5) for 0<=j<n tend to (2^(1/5)-1)/3. Since v^(-4/5) decreases on [1,2], its left and right rectangle sums bound its integral. Their difference is (1-2^(-4/5))/n, so the normalized upper sum differs from the limiting constant by at most 1/(15n)."))),
                DescribeRole.Theorem))));
}
