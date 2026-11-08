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
                DescribeId.Create("fixed-normalizer-ratio"),
                DeclarationHandle.Create(Prefix + "fixed_normalizer_ratio"),
                H("The fixed-length normalization ratio"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For c>0 and any real theta, the ratio of (X/(c*X^theta))*log(X/(c*X^theta)) to X^(1-theta)*log(X) tends to (1-theta)/c as X tends to infinity."))),
                DescribeRole.Theorem),
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
                    "Let E be a Borel real function bounded on compact intervals, assume 0<alpha<theta<beta<1 and the uniform cumulative variance band asymptotic, and let g be integrable on [0,1]. For fixed positive n, sum the profile square integrals on [a_j X,a_(j+1) X] with length frozen at (a_j X)^theta, where a_j=1+j/n. Dividing by X^(1-theta) log X gives the limit ((1-theta)Q(g)/n) times the sum of a_j^(-theta). The fixed-length normalizer divided by this scale tends to (1-theta)/c."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cell-constant-tendsto"),
                DeclarationHandle.Create(Prefix + "cell_constant_tendsto"),
                H("The limiting rectangle constant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For 0<theta<1 and any real profile g, the constants ((1-theta)Q(g)/n) times the sum of (1+j/n)^(-theta) for 0<=j<n tend to Q(g)*(2^(1-theta)-1). Since v^(-theta) decreases on [1,2], its left and right rectangle sums bound its integral and differ by (1-2^(-theta))/n. Multiplying the resulting rectangle-sum limit by (1-theta)Q(g) proves the conclusion without a sign assumption on Q(g)."))),
                DescribeRole.Theorem))));
}
