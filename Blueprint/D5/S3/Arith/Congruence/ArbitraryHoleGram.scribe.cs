using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class ArbitraryHoleGramDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual row and column hole degrees give a common quadratic bound for every finite surviving grid, including deleted full rows or columns.",
        H("Degree Weights for Arbitrary Holes in a Finite Grid"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-incidence-weighted-square-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Congruence/ArbitraryHoleGram.degree_reweighted_grid_second_moment_le"),
                H("A common four-block diagonal follows from the actual hole relation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The row and column carriers have finite sizes m and n, both at least three. "
                        + "The relation E specifies arbitrary deleted cells, k is its actual cardinality, "
                        + "and every surviving cell has weight one plus epsilon times the sum of "
                        + "its row and column hole counts. The parameter is nonnegative and satisfies "
                        + "9 epsilon k C0 at most one, where C0 is the maximum of m+n+1, "
                        + "2(m-1), 2(n-1), and 4. No matching condition or supplied degree budget is used.")),
                    Paragraph(Text(
                        "For any selected row, column, surviving point, and four real coefficients, "
                        + "the load is the constant coefficient plus the selected row, column, "
                        + "and point indicators with their respective coefficients. Its actual "
                        + "weighted squared sum is bounded by the diagonal with entries "
                        + "Z+m+n+1+2 epsilon k, 2(n+1+epsilon k), "
                        + "2(m+1+epsilon k), and 4; Z is the sum of the same cell weights.")),
                    Paragraph(Text(
                        "The proof derives incident-hole disjointness and the row derivative "
                        + "bounds directly from E. In every nonexceptional case, the unweighted "
                        + "Gram difference has gap at least one ninth, with missing star edges "
                        + "restored from actual diagonal slack when an entire selected row or "
                        + "column is deleted. The perturbation is bounded using the existing "
                        + "symmetric absolute-row-sum theorem. In the remaining aligned case, "
                        + "the perturbation is itself a nonnegative Laplacian. A direct finite "
                        + "sum expansion connects these bounds to the stated actual weighted load.")),
                    Paragraph(Text(
                        "This theorem is an arbitrary finite symbolic inequality. It supplies "
                        + "the unnormalized four-block grid estimate used in the odd-covering "
                        + "head argument. The normalized probability construction, its common "
                        + "denominator bound, arithmetic head integration, and tail noncoverage "
                        + "are separate obligations and are not conclusions of this declaration."))),
                DescribeRole.Theorem))));
}
