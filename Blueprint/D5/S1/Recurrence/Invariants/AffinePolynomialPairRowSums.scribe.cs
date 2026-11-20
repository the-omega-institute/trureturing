using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class AffinePolynomialPairRowSumsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/AffinePolynomialPairRowSums.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mazhang2026a208509pair");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The affine polynomial pair has row sums v_n(1) = 3 · 2^{n−2} and u_n(1) = 3 · 2^{n−2} − 1 "
            + "for n ≥ 2, and alternating row sums with a quadratic generating denominator.",
        H("Row sums and alternating row sums of the affine polynomial pair"),
        Blocks(
            Describe.Lean(DescribeId.Create("a208509-row-sums-w"),
                DeclarationHandle.Create(Prefix + "w"),
                H("The alternating row sums"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "w_n = v_n(−1) = second(pair(n − 1)) evaluated at −1, for the source index "
                    + "n ≥ 1."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a208509-row-sums-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Row sums and the alternating recurrence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every n ≥ 2, v_n(1) = 3 · 2^{n−2} and u_n(1) = 3 · 2^{n−2} − 1, while "
                    + "v_1(1) = u_1(1) = 1. In Z[[z]], (∑_{n≥1} w_n z^{n−1})(1 − 2z + 2z²) = 1 + z; "
                    + "w_{n+2} = 2w_{n+1} − 2w_n for n ≥ 1, w_1 = 1 and w_2 = 3. Evaluating the "
                    + "recursion at x = 1 gives u' = u + v and v' = u + v + 1, and induction from "
                    + "u_2(1) = 2, v_2(1) = 3 gives the doubling. At x = −1, eliminating u from "
                    + "u' = u − v and v' = u + v + 1 gives the second-order recurrence, which "
                    + "fixes every coefficient of the series product. This is Corollary 5 of "
                    + "H. Ma and W. Zhang's note on A208509 (DOI 10.5281/zenodo.24211281)."))),
                DescribeRole.Theorem))));
}
