using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class OEISA242926AntidiagonalLcmDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Residue/OEISA242926AntidiagonalLcm.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mazhang2026a189733siblings");

    private static DocumentBlock Def(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "On every strict upper antidiagonal of Curtz's signed and unsigned arrays, the reduced "
            + "denominators have lcm lcm(1, …, ⌊(s + 1)/2⌋) = A139550(s + 1).",
        H("Antidiagonal denominator lcm of the zero-diagonal arrays"),
        Blocks(
            Def("antidiagonal-lcm-seeded", "V", "Upper entries with arbitrary seeds",
                "V w m d is V(m, m + d) for the zero-diagonal array with first-superdiagonal "
                + "seeds w m = V(m, m + 1) and V(m, n) = V(m, n − 1) + V(m + 1, n − 1)."),
            Def("antidiagonal-lcm-def", "antiLcm", "The antidiagonal lcm",
                "antiLcm A s is the lcm of the reduced denominators of A(m, s − m) over "
                + "m < s − m, with the empty lcm equal to one."),
            Def("antidiagonal-lcm-a139550", "A139550", "A139550",
                "A139550(r) = lcm(1, …, ⌊r/2⌋)."),
            Describe.Lean(DescribeId.Create("antidiagonal-lcm-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The antidiagonal lcm"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every s ≥ 0 and for both the signed array B and the unsigned array U, "
                    + "the antidiagonal lcm equals lcm(1, …, ⌊(s + 1)/2⌋) = A139550(s + 1). "
                    + "For arbitrary seeds and d ≥ 1, V(m, m + d) = ∑_{j=0}^{d−1} C(d − 1 − j, j) "
                    + "w_{m+j}. The "
                    + "entries of the antidiagonal are therefore a unit upper-triangular "
                    + "integer combination of w_0, …, w_{h−1} with h = ⌊(s + 1)/2⌋. An integer "
                    + "N makes every N·V(m, s − m) an integer exactly when it makes every N·w_k "
                    + "an integer; passing from cleared entries to cleared seeds is a downward "
                    + "induction on the seed index. For "
                    + "both arrays the seeds are ±1/(k + 1), so N clears them exactly when "
                    + "1, …, h all divide N. Two natural numbers with the same multiples are "
                    + "equal, which gives the lcm identity. This is Corollary 11 of H. Ma and "
                    + "W. Zhang's note (DOI 10.5281/zenodo.23957584)."))),
                DescribeRole.Theorem))));
}
