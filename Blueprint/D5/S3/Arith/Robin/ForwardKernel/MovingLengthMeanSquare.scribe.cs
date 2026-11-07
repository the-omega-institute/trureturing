using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class MovingLengthMeanSquareDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/MovingLengthMeanSquare.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal-cell freezing gives the moving-length triangular mean square.",
        H("Equal-cell freezing gives the moving-length triangular mean square"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("moving-length-mean-square-tendsto"),
                DeclarationHandle.Create(Prefix + "moving_length_mean_square_tendsto"),
                H("Moving-length mean square from fixed-length limits"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let E be measurable and bounded on compact intervals. Assume the short-interval mean-square bound and uniform cumulative variance band asymptotic. They give the fixed-length triangular mean-square limit with value (b-a)/3 for every 1<=a<b<=2 and c>0. Then the square integral of P_(x^(4/5))(x) over [X,2X], divided by X^(1/5) log X, tends to (2^(1/5)-1)/3. Freeze the length at each left endpoint of n equal cells. Write Q_n(X)=cellMeanSquare E n X, the sum over the n cells of the integrals of the square of the triangular average at the frozen cell length. The total square error is at most 18 Q_n(X)/n^2 + 64 X^(1/5) log X/n, with constants independent of n. The interval L squared reverse triangle inequality and Young’s inequality compare the two square integrals. First choose n so that both the rectangle constant and the normalized error are small, then choose X for this fixed n. The short-interval upper bound controls the small lengths in the fixed-length limit, and the variance band controls the strip estimate with one logarithm."))),
                DescribeRole.Theorem))));
}
