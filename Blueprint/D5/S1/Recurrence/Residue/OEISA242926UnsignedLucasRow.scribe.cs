using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class OEISA242926UnsignedLucasRowDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Residue/OEISA242926UnsignedLucasRow.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mazhang2026a189733siblings");

    private static DocumentBlock Def(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The unsigned companion of Curtz's array has first row u_n = (L_{n+1} − 1)/(n + 1), and "
            + "satisfies the A175385/A175386, inverse-binomial and antidiagonal identities.",
        H("The unsigned array and its Lucas first row"),
        Blocks(
            Def("a242926-upper", "Ut", "The upper entries",
                "Ut m d is U(m, m + d): zero on the diagonal, 1/(m + 1) on the first "
                + "superdiagonal, and U(m, n) = U(m, n − 1) + U(m + 1, n − 1) for n ≥ m + 2."),
            Def("a242926-array", "U", "The full unsigned array",
                "U(m, n) is the upper entry for m ≤ n and follows the lower branch "
                + "U(m, n) = U(m − 1, n + 1) − U(m − 1, n) for m > n."),
            Def("a242926-row", "u", "The first row", "u_n = U(0, n)."),
            Def("a242926-a175385", "A175385", "A175385",
                "A175385(n) is the reduced numerator of ∑_{i=1}^{n} C(2n − i − 1, i − 1)/i."),
            Def("a242926-a175386", "A175386", "A175386",
                "A175386(n) is the reduced denominator of ∑_{i=1}^{n} C(2n − i − 1, i − 1)/i."),
            Describe.Lean(DescribeId.Create("a242926-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Lucas row, odd-index fractions, inverse binomial and antidiagonal identities"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "U(m, m + d) is the upper entry Ut m d. For every n ≥ 0, "
                    + "u_n = (L_{n+1} − 1)/(n + 1), where L is the Lucas sequence with "
                    + "L_0 = 2 and L_1 = 1. For every r ≥ 0, the reduced numerator and "
                    + "denominator of u_{2r+1} are A175385(r + 1) and A175386(r + 1), while the "
                    + "reduced denominator of u_3 differs from A175386(1). For every n, "
                    + "∑_{j=0}^{n} (−1)^{n−j} C(n, j) u_j = (−1)^{n+1} u_n. For every r, "
                    + "∑_{m=0}^{r} U(m, 2r + 1 − m) = u_{2r+2}. The upper entries are the "
                    + "unsigned binomial sums ∑_j C(d − 1 − j, j)/(m + j + 1). The identity "
                    + "(n + 1)C(n − 1 − j, j)/(j + 1) = C(n − j, j + 1) + C(n − 1 − j, j) and the "
                    + "Fibonacci diagonal sums turn (n + 1)u_n into F_{n+2} + F_n − 1. The "
                    + "reflection U(m, n) = (−1)^{m+n+1} U(n, m) and the difference identity "
                    + "give the inverse binomial identity. Telescoping the upper recurrence "
                    + "along the antidiagonal gives the last identity. This is Corollary 9 of "
                    + "H. Ma and W. Zhang's note (DOI 10.5281/zenodo.23957584)."))),
                DescribeRole.Theorem))));
}
