using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Carrier.Powers;

internal sealed class IntegerPowerNormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden norm of every integral power of the distinguished unit is the corresponding signed unit power.",
        H("Integer-Power Golden Norm"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("norm-of-phi-unit-integer-power"),
                DeclarationHandle.Create("D5/S0/Carrier/Powers/IntegerPowerNorm.norm_phiUnit_zpow"),
                H("Norm of an integral power of phiUnit"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("Z")), Comma, Esc,
                    Operatorname, Grp(F.Id("norm")), Open, Open, F.Id("phiUnit"), Caret, F.Id("n"), Colon,
                    Operatorname, Grp(F.Id("GoldenInt")), Caret, Grp(Times), Close,
                    Dot, F.Id("val"), Close, Sp, Eq, Sp,
                    Open, Open, Minus, D(1), Close, Caret, F.Id("n"), Colon,
                    Mathbb, Grp(F.Id("Z")), Caret, Grp(Times), Close,
                    Dot, F.Id("val"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The distinguished golden unit phiUnit has value phi. The strict golden power "
                        + "uses phi for nonnegative exponents and its inverse for negative exponents. "
                        + "Both bases have norm -1.")),
                    Paragraph(Text(
                        "The proof applies natural-power norm multiplicativity in each integer case. "
                        + "It raises -1 to the absolute exponent because -1 is its own inverse.")),
                    Paragraph(Text(
                        "This closes the integer-power extension clause of remark 27.722. The even-power "
                        + "positivity and cone-selection consequences remain unresolved."))),
                DescribeRole.Theorem)),
        []));
}
