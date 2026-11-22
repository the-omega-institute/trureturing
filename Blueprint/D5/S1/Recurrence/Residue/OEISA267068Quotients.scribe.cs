using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class OEISA267068QuotientsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Residue/OEISA267068Quotients.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mazhang2026a189733siblings");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The quotients c_n = (n + 1)/a_n of Curtz's denominators are integers with six affine "
            + "residue formulas, Barker's recurrence and generating function, and the three "
            + "sequence identifications of A267068.",
        H("The A267068 quotient formulas"),
        Blocks(
            Def("c", "The quotient sequence",
                "For the reduced denominators a_n of the zeroth row of Curtz's triangle, c_n is "
                + "the natural-number quotient (n + 1)/a_n; the theorem shows the division is "
                + "exact."),
            Def("A130196", "A130196",
                "A130196 has offset 0 and repeats the period [1, 2, 2]."),
            Def("A047245", "A047245",
                "A047245 has offset 1 and lists the numbers congruent to 1, 2 or 3 modulo 6; "
                + "its n-th term is 6⌊(n − 1)/3⌋ + ((n − 1) mod 3) + 1."),
            Def("A052901", "A052901",
                "A052901 has offset 0, period 3, value 3 at multiples of 3 and value 2 "
                + "elsewhere."),
            Def("A047238", "A047238",
                "A047238 has offset 1 and lists the numbers congruent to 0 or 2 modulo 6; its "
                + "n-th term is 6⌊(n − 1)/2⌋ + 2((n − 1) mod 2)."),
            Describe.Lean(DescribeId.Create("a267068-quotients"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Quotient values, recurrence and series"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every n, a_n divides n + 1, and for every k ≥ 0 "
                    + "(c_{6k}, …, c_{6k+5}) = (6k + 1, 2, 3, 2, 6k + 5, 1). For n ≥ 12, "
                    + "c_n = 2c_{n−6} − c_{n−12}. In the integer formal power series ring, "
                    + "(∑ c_n z^n)(1 − z⁶)² = 1 + 2z + 3z² + 2z³ + 5z⁴ + z⁵ + 5z⁶ − 2z⁷ − 3z⁸ − "
                    + "2z⁹ + z¹⁰ − z¹¹. Since (1 − z⁶)² has constant term one, this is "
                    + "Barker's generating function. Moreover c_{2n+1} = A130196(n + 1), "
                    + "c_{A047245(n+1)} = A052901(n + 2) and c_{3n} + c_{3n+1} + c_{3n+2} = "
                    + "A047238(n + 3) for every n ≥ 0. The residue values come from dividing "
                    + "n + 1 by the frozen six denominator formulas. The recurrence follows "
                    + "because each residue subsequence is affine, and the series follows by "
                    + "comparing coefficients. The identifications are checked on residues "
                    + "modulo 6. This is Corollary 6 of H. Ma and W. Zhang's note "
                    + "(DOI 10.5281/zenodo.23957584)."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Def(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("a267068-def-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))),
            DescribeRole.Definition);
}
