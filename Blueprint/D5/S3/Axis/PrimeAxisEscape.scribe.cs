using static StrataLint.Scribe.DefinitionDsl;

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
                LatexStatement.Create(
                    @"$$\forall S\subset_{\operatorname{fin}}\mathbb{N},\ "
                    + @"(\forall p\in S,\ p\ \text{prime}) \Rightarrow "
                    + @"((\forall p\in S,\ \prod_{r\in S}r+1\equiv 1\ "
                    + @"(\operatorname{mod}\ p)) \land \exists q\in\mathbb{N},\ "
                    + @"q\ \text{prime}\land q\mid \prod_{r\in S}r+1\land q\notin S)$$"),
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
}
