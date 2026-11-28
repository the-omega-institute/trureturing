using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GoldenTomography;

internal sealed class FinitePronySecondMomentRangeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Which means and second moments can a positive Prony family realize?",
        H("Attainable second moments of positive Prony families"),
        Blocks(Describe.Lean(DescribeId.Create("second-moment-range"),
            DeclarationHandle.Create(
                "D5/S3/Analytic/GoldenTomography/FinitePronySecondMomentRange.finite_prony_second_moment_range"),
            H("The second-moment interval and the minimum node count"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Over a linearly ordered field, let distinct nodes in the open interval (a, b) "
                    + "have positive weights of total mass M. Their first moment M times x "
                    + "forces a < x < b. For each such x, the feasible second moments run "
                    + "from M times x squared, inclusive, to M times the quantity "
                    + "(a + b) x minus a b, exclusive. A realizing family "
                    + "has one node if and only if its second moment equals the lower "
                    + "endpoint. Each interior second moment admits a two-node family. "
                    + "The minimum number of nodes realizing the full moment triple "
                    + "is one at the lower endpoint and two in the interior.")),
                Paragraph(Text("The weighted sums of distances to the left and right endpoints "
                    + "are M times (x − a) and M times (b − x). Positive mass supplies at "
                    + "least one node, so these sums are strictly positive. The weighted "
                    + "sum of squared distances from the mean gives "
                    + "the lower slack. If it vanishes, positivity forces every node to "
                    + "equal the mean. The upper slack is the weighted sum of the products "
                    + "of the two distances from each node to the interval endpoints. "
                    + "Every summand is positive.")),
                Paragraph(Text("For positive variance v, choose the left distance d halfway "
                    + "between v/(b − x) and x − a. The right distance e "
                    + "is v divided by d. Weights proportional to e and d center the two "
                    + "nodes at x and give variance d times e. Both nodes lie strictly "
                    + "inside the interval. The upper variance bound is the strict form "
                    + "of Bhatia and Davis, A Better Bound on the Variance "
                    + "(doi:10.1080/00029890.2000.12005203)."))),
            DescribeRole.Theorem)),
        []));
}
