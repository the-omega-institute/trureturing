using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class AffinePolynomialPairBinomialColumnFamilyDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Invariants/AffinePolynomialPairBinomialColumnFamily.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mazhang2026a208509pair");

    private static DocumentBlock Def(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The column family h_d(m) = [z^m](1 + z)/(1 − z)^d has binomial closed forms, partial sums, "
            + "a finite-difference recurrence and a reflection-symmetric polynomial extension.",
        H("The binomial column family of the affine pair"),
        Blocks(
            Def("a208509-column-family-h", "h", "The column family",
                "h_d(m) is the integer coefficient of z^m in (1 + z)/(1 − z)^d, using Mathlib's "
                + "inverse of (1 − z)^d."),
            Def("a208509-column-family-poly", "H", "The polynomial extension",
                "H_d(t) = (2/(d − 1)!) (t + (d − 1)/2) ∏_{i=1}^{d−2} (t + i) in Q[t]."),
            Describe.Lean(DescribeId.Create("a208509-column-family-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Closed forms, sums, recurrence and symmetry"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For d ≥ 2 and every m, h_d(m) = C(m + d − 1, d − 1) + C(m + d − 2, d − 1) = "
                    + "2C(m + d − 1, d − 1) − C(m + d − 2, d − 2) = (2m + d − 1)/(d − 1) · "
                    + "C(m + d − 2, d − 2). For every d and m, h_{d+1}(m) = ∑_{j=0}^{m} h_d(j). "
                    + "For every d and every m ≥ 2, h_d(m) = ∑_{j=1}^{min(d, m)} (−1)^{j+1} "
                    + "C(d, j) h_d(m − j); the source states d ≥ 2 and m ≥ d, where min(d, m) = d. "
                    + "The bound m ≥ 2 is needed: h_1(1) = 2 while the right side is h_1(0) = 1. "
                    + "The condition d ≥ 2 is needed for the closed forms and for H_d: h_1(0) = 1 "
                    + "while the first closed form gives 2, and h_1 = 1, 2, 2, … is not a "
                    + "polynomial in m. For d ≥ 2, H_d agrees "
                    + "with h_d on every natural m, has degree d − 1 and leading coefficient "
                    + "2/(d − 1)!, and H_d(−t − d + 1) = (−1)^{d−1} H_d(t) for every rational t. "
                    + "The partial sums come from 1/(1 − z)^{d+1} = 1/(1 − z)^d · 1/(1 − z), and the "
                    + "recurrence from (1 − z)^d (1 + z)/(1 − z)^d = 1 + z. The polynomial value "
                    + "uses C(m + d − 2, d − 2)(d − 2)! = (m + 1)⋯(m + d − 2), and the reflection "
                    + "reverses this product. This is Corollary 6 of H. Ma and W. Zhang's note on "
                    + "A208509 (DOI 10.5281/zenodo.24211281)."))),
                DescribeRole.Theorem))));
}
