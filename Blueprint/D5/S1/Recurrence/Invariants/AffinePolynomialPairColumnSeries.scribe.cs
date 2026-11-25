using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class AffinePolynomialPairColumnSeriesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/AffinePolynomialPairColumnSeries.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mazhang2026a208509pair");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The affine polynomial pair has generating function (1 + z)/(1 − 2z + (1 − x)z²), and its "
            + "coefficient columns have generating functions z^a(1 + z)/(1 − z)^b.",
        H("Generating functions of the affine polynomial pair and its columns"),
        Blocks(
            Describe.Lean(DescribeId.Create("a208509-column-series-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Row and column generating functions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Write v_n = second(pair(n − 1)) and u_n = first(pair(n − 1)). In Z[x][[z]], "
                    + "(∑_{n≥1} v_n z^{n−1})(1 − 2z + (1 − x)z²) = 1 + z. In Z[[z]], for every "
                    + "k ≥ 0 the series ∑_{n≥1} ([x^k] v_n) z^{n−1} times (1 − z)^{2k+2} is "
                    + "z^{2k}(1 + z); for every k ≥ 1 the series ∑_{n≥1} ([x^k] u_n) z^{n−1} times "
                    + "(1 − z)^{2k+1} is z^{2k−1}(1 + z); and the constant u-column times (1 − z) "
                    + "is 1. The row identity follows from v_{n+2} = 2v_{n+1} − (1 − x)v_n with "
                    + "v_1 = 1, v_2 = 3. For the columns, A_d = ∑ C(n, d) z^n satisfies "
                    + "A_d(1 − z)^{d+1} = z^d by the negative binomial series, and each column "
                    + "series is A_d plus its one-step shift, by the coefficient formulas of "
                    + "pair_coeff. This is Corollary 4 of H. Ma and W. Zhang's note on A208509 "
                    + "(DOI 10.5281/zenodo.24211281)."))),
                DescribeRole.Theorem))));
}
