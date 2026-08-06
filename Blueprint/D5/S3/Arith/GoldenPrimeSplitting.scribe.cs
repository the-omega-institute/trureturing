using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class GoldenPrimeSplittingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Arith/GoldenPrimeSplitting",
            "The rational prime five is the square of its ramifying golden integer."),
        H("Ramification at Five"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("five-is-the-square-of-the-ramifying-golden-integer"),
                H("Five is a ramified square"),
                LeanTheorem("D5/S3/Arith/GoldenPrimeSplitting.golden_five_eq_ramified_square"),
                Disp(Seq(D(5), Sp, Eq, Sp, Open, Minus, D(1), Plus, D(2), Varphi, Close, Caret, D(2))),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "In the golden integer ring, five equals the square of -1 + 2 phi. This is the exact ramified-square identity; it asserts neither a choice of associates nor an additional factorization convention.")))
            ))));
}
