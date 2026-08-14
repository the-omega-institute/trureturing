using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Eigenstructure;

internal sealed class GoldenPowerLogDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create(
            "The logarithmic scale of every natural golden power is integral.",
            H("Golden Power Logarithmic Scale"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("golden-power-logb-natural"),
                    DeclarationHandle.Create(
                        "D5/S1/Eigenstructure/GoldenPowerLog.golden_power_logb_nat"),
                    H("Natural golden powers have integral logarithmic scale"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Operatorname, Grp(F.Id("logb")), Open, Varphi, Comma,
                        Varphi, Caret, Grp(F.Id("n")), Close, Sp, Eq, Sp,
                        F.Id("n")))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For every natural number n, the pinned logarithm-power "
                                + "identity and the golden-ratio base identity reduce "
                                + "logb(phi, phi^n) to n.")),
                        Paragraph(Text(
                            "This is a partial closure of the source bundle's first "
                                + "scale clause only. Its Zeckendorf-addition and "
                                + "three-gap clauses remain unresolved."))),
                    DescribeRole.Theorem))));
}
