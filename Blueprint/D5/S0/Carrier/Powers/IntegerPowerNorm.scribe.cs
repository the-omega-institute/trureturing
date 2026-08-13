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
                        "The distinguished golden unit phiUnit has value phi. Mapping its integer powers "
                        + "through the frozen norm monoid homomorphism gives the corresponding power of "
                        + "the unit -1 in the integer units; the displayed `.val` extracts the integer.")),
                    Paragraph(Text(
                        "The proof uses Units.map and MonoidHom.map_zpow, so negative exponents are handled "
                        + "by the unit inverse rather than by a new norm definition.")),
                    Paragraph(Text(
                        "This closes the integer-power extension clause of remark 27.722. The even-power "
                        + "positivity and cone-selection consequences remain unresolved."))),
                DescribeRole.Theorem)),
        []));
}
