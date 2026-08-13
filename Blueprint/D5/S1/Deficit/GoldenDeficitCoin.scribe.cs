using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit;

internal sealed class GoldenDeficitCoinDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Twice the square of the real golden ratio exceeds its cube by exactly one.",
        H("Golden Deficit Coin Identity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-deficit-coin-identity"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/GoldenDeficitCoin.golden_deficit_coin_identity"),
                H("The quadratic-cubic deficit is one"),
                StatementSource.FromAuthor(Disp(Seq(
                    D(2), Sp, Cdot, Sp, Varphi, Caret, Grp(D(2)), Sp, Minus, Sp,
                    Varphi, Caret, Grp(D(3)), Sp, Eq, Sp, D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The library quadratic identity phi squared equals phi plus one first "
                        + "reduces the cube to phi times phi plus one. A second use of the same "
                        + "identity leaves the exact deficit one.")),
                    Paragraph(Text(
                        "This is an honest partial closure of only the algebraic identity in the "
                        + "source proposition. The critical-line pullback, structural zero-line "
                        + "interpretation, derivative and slope formula, and all numerical window "
                        + "certificates remain unresolved, so the source atom remains partial and "
                        + "open."))),
                DescribeRole.Theorem)),
        []));
}
