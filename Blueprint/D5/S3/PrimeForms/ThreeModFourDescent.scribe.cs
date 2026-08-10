using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms;

internal sealed class ThreeModFourDescentDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Grosswald =
        LibraryNoteRef.Create("D5/L/Arith/grosswald1985representations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/PrimeForms/ThreeModFourDescent",
            "A prime congruent to three modulo four dividing a sum of two squares"
            + " divides both bases."),
        H("Descent at Primes Three Modulo Four"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("three-mod-four-descent"),
                H("A prime congruent to three modulo four dividing a sum of two"
                  + " squares divides both bases"),
                LeanTheorem(
                    "D5/S3/PrimeForms/ThreeModFourDescent."
                    + "prime_dvd_dvd_of_dvd_sq_add_sq"),
                Disp(Seq(
                    F.Id("q"), Sp, F.Text, Grp(F.Id("prime")), Comma, Esc,
                    F.Id("q"), Equiv, Sp, D(3), Esc,
                    Open, Operatorname, Grp(F.Id("mod")), Esc, D(4), Close, Comma, Esc,
                    F.Id("q"), Esc, Mid, Esc,
                    F.Id("a"), Caret, D(2), Plus, F.Id("b"), Caret, D(2),
                    Quad, Rightarrow, Quad, Sp,
                    F.Id("q"), Esc, Mid, Esc, F.Id("a"), Sp, Land, Sp,
                    F.Id("q"), Esc, Mid, Esc, F.Id("b"))),
                DescribeProvenance.LiteratureAttested(Grosswald),
                Blocks(Paragraph(Text(
                    "If a prime q congruent to three modulo four divides a sum of two "
                    + "natural squares, then q divides both bases: otherwise the "
                    + "quotient of the two residues would be a square root of minus "
                    + "one modulo q, which is impossible for q congruent to three "
                    + "modulo four. The statement is the descent engine of the "
                    + "classical two-squares theory and forces the exponent of q in "
                    + "any sum of two squares to be even. The formal proof is thin "
                    + "but not a wrapper: pinned Mathlib carries the modular tool "
                    + "(nonzero squares are never negatives of each other modulo such "
                    + "a prime) yet not the descent implication itself, which is "
                    + "proved here by casting into the residue field and splitting on "
                    + "whether the second base vanishes. The source lemma's "
                    + "parenthetical consequence that the q-adic valuation of a sum "
                    + "of two squares is always even is not part of this deposit. "
                    + "Original numerical-certificate disposition: the source lemma "
                    + "is purely universal and contains no numerical certificate.")))
            ))));
}
