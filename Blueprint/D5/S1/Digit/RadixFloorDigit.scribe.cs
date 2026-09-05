using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class RadixFloorDigitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Successive floors define an exact bounded radix digit.",
        H("Radix Floor Digits"),
        Blocks(Describe.Lean(
            DescribeId.Create("radix-floor-digit-bounds-and-decomposition"),
            DeclarationHandle.Create(
                "D5/S1/Digit/RadixFloorDigit.radix_floor_digit_bounds_and_decomposition"),
            H("The floor carry is a bounded radix digit"),
            StatementSource.FromAuthor(Disp(Seq(
                D(0), Sp, Leq, Sp, Seq(F.Id("d"), Underscore, Grp(F.Id("b"))), Open, F.Id("x"), Close,
                Sp, Lt, Sp, F.Id("b"), Sp, Land, Sp,
                F.Id("floor"), Open, F.Id("b"), F.Id("x"), Close, Sp, Eq, Sp,
                F.Id("b"), F.Id("floor"), Open, F.Id("x"), Close, Sp, Plus, Sp,
                Seq(F.Id("d"), Underscore, Grp(F.Id("b"))), Open, F.Id("x"), Close, Dot))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The remainder floor(b x) minus b floor(x) lies between zero and b minus one and gives the exact radix decomposition."))),
            DescribeRole.Theorem))));
}
