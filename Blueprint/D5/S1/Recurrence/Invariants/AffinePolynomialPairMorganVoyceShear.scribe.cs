using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class AffinePolynomialPairMorganVoyceShearDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/AffinePolynomialPairMorganVoyceShear.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mazhang2026a208509pair");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Morgan–Voyce polynomials P_m have coefficients C(m + k, 2k) + 2C(m + k, 2k + 1), "
            + "the sheared coefficients b_{m+k+1,k} of the affine pair.",
        H("The Morgan–Voyce shear of the affine pair"),
        Blocks(
            Describe.Lean(DescribeId.Create("a208509-morgan-voyce-p"),
                DeclarationHandle.Create(Prefix + "P"),
                H("The Morgan–Voyce polynomials"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "P_0 = 1, P_1 = 3 + x and P_m = (x + 2)P_{m−1} − P_{m−2} for m ≥ 2, in Z[x]."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a208509-morgan-voyce-shear"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The shear identity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For all m and k, [x^k]P_m = b_{m+k+1,k} = C(m + k, 2k) + 2C(m + k, 2k + 1), "
                    + "where b_{n,k} = [x^k] v_n is the coefficient of second(pair(n − 1)). Beyond "
                    + "k = m all three sides vanish, so the source range 0 ≤ k ≤ m is included. "
                    + "The binomial side satisfies the coefficient recurrence of P_m after two "
                    + "Pascal expansions, and Werner's formula with one Pascal step identifies it "
                    + "with b_{m+k+1,k}. This is Corollary 2 of H. Ma and W. Zhang's note on "
                    + "A208509 (DOI 10.5281/zenodo.24211281), André-Jeannin's r = 2 coefficient "
                    + "theorem."))),
                DescribeRole.Theorem))));
}
