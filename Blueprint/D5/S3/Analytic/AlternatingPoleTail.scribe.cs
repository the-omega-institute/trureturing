using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class AlternatingPoleTailDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Analytic/AlternatingPoleTail",
            "A pole at minus one has an exact alternating binomial coefficient tail."),
        H("Alternating Pole Tails"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("pole-at-minus-one-has-an-alternating-binomial-tail"),
                H("A pole at minus one generates an alternating binomial tail"),
                LeanTheorem(
                    "D5/S3/Analytic/AlternatingPoleTail.alternating_pole_tail_coeff"),
                Disp(Seq(
                    Operatorname, Grp(F.Id("coeff")), Open, F.Id("n"), Comma, Sp,
                    Operatorname, Grp(F.Id("rescale")), Open, Minus, D(1), Comma, Sp,
                    Open, D(1), Minus, F.Id("X"), Close, Caret,
                    Grp(Minus, Open, F.Id("k"), Plus, D(1), Close), Close, Close,
                    Eq,
                    Open, Minus, D(1), Close, Caret, F.Id("n"), Sp,
                    Operatorname, Grp(F.Id("choose")), Open,
                    F.Id("k"), Plus, F.Id("n"), Comma, F.Id("k"), Close)),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "For nonnegative k and n, rescaling the inverse power series of "
                        + "one minus X by minus one gives coefficient n equal to minus one "
                        + "to the n times choose k plus n over k. Thus a pole of order k "
                        + "plus one at minus one has an exact alternating tail whose "
                        + "magnitudes are polynomial in n.")),
                    Paragraph(Text(
                        "The proof is a thin honest wrapper over pinned Mathlib's negative-"
                        + "binomial power series and coefficient-rescaling declarations. "
                        + "Mathlib has no named theorem for the source atom's full row-family "
                        + "specialization. This declaration proves the exact algebraic pole-"
                        + "tail mechanism; it does not assert that every row function in the "
                        + "source atom has already been identified with this model.")))
            ))));
}
