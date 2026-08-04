using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Axis;

internal sealed class PrimeAxisEscapeDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Apostol =
        LibraryNoteRef.Create("D5/L/apostol1976introduction");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Axis/PrimeAxisEscape",
            "A finite prime axis is escaped by a prime divisor of the product plus one."),
        H("Prime-Axis Escape"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("a-finite-prime-axis-has-an-external-prime-divisor"),
                H("A finite prime axis has an external prime divisor"),
                LeanTheorem(
                    "D5/S3/Axis/PrimeAxisEscape.prime_axis_escape"),
                PrimeAxisEscapeFormula(),
                DescribeProvenance.LiteratureAttested(Apostol),
                Blocks(Paragraph(Text(
                    "For a finite set S consisting only of natural primes, its product plus one "
                    + "is congruent to one modulo every prime in S. The same number has a prime "
                    + "divisor q outside S, supplied as an explicit existential witness together "
                    + "with primality, divisibility, and non-membership. This is the finite-set "
                    + "escape form of Euclid's classical argument; the formal theorem does not "
                    + "assert any later PZG encoding or tail interpretation. The proof uses "
                    + "Mathlib's existence of a prime divisor for a natural different from one, "
                    + "then rules out membership in S because a common divisor of the product and "
                    + "the product plus one would divide one. No numerical certificate is "
                    + "asserted.")))
            ))));

    private static Formula PrimeAxisEscapeFormula()
    {
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula finiteSubset = new Formula.Subscript(
            Subset,
            Seq(Operatorname, Grp(F.Id("fin"))));
        Formula productPlusOne = Seq(
            new Formula.Subscript(
                Prod,
                Seq(F.Id("r"), InMacro, F.Id("S"))),
            F.Id("r"),
            Plus,
            D(1));

        return Disp(Seq(
            Forall, Sp, F.Id("S"), finiteSubset, naturals, Comma, Esc,
            Open,
            Forall, Sp, F.Id("p"), InMacro, F.Id("S"), Comma, Esc,
            F.Id("p"), Esc, F.Text, Grp(F.Id("prime")),
            Close, Sp, Rightarrow, Sp,
            Open, Open,
            Forall, Sp, F.Id("p"), InMacro, F.Id("S"), Comma, Esc,
            productPlusOne, Equiv, Sp, D(1), Esc,
            Open, Operatorname, Grp(F.Id("mod")), Esc, F.Id("p"), Close,
            Close, Sp, Land, Sp,
            Exists, Sp, F.Id("q"), InMacro, naturals, Comma, Esc,
            F.Id("q"), Esc, F.Text, Grp(F.Id("prime")),
            Land, Sp, F.Id("q"), Mid, Sp, productPlusOne,
            Land, Sp, Neg, Open, F.Id("q"), InMacro, F.Id("S"), Close,
            Close));
    }
}
