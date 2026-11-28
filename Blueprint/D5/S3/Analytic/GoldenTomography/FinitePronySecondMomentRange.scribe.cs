using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GoldenTomography;

internal sealed class FinitePronySecondMomentRangeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Which second moments can agree with the same mass and mean?",
        H("Attainable second moments of positive Prony families"),
        Blocks(Describe.Lean(DescribeId.Create("second-moment-range"),
            DeclarationHandle.Create(
                "D5/S3/Analytic/GoldenTomography/FinitePronySecondMomentRange.finite_prony_second_moment_range"),
            H("The second-moment interval and the minimum pole count"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Work over a linearly ordered field. Fix a positive mass M "
                    + "and a mean x strictly between a and b. Consider finite families of "
                    + "distinct nodes in the open interval with strictly positive weights "
                    + "and moments of orders zero and one equal to M and M times x. Their "
                    + "second moments range from M times x squared, inclusive, to M times "
                    + "the quantity (a + b) x minus a b, exclusive. A realizing family has "
                    + "one node exactly at the included endpoint. Each interior second "
                    + "moment admits a two-node family.")),
                Paragraph(Text("The weighted sum of squared distances from the mean gives "
                    + "the lower slack. If it vanishes, positivity forces every node to "
                    + "equal the mean. The upper slack is the weighted sum of the products "
                    + "of the two distances from each node to the interval endpoints. "
                    + "Every summand is positive, and the positive mass implies there is "
                    + "at least one node.")),
                Paragraph(Text("For positive variance v, choose the left distance d halfway "
                    + "between v divided by b minus x and x minus a. The right distance e "
                    + "is v divided by d. Weights proportional to e and d center the two "
                    + "nodes at x and give variance d times e. Both nodes lie strictly "
                    + "inside the interval. The upper variance bound is the strict form "
                    + "of Bhatia and Davis, A Better Bound on the Variance "
                    + "(doi:10.1080/00029890.2000.12005203)."))),
            DescribeRole.Theorem)),
        []));
}
