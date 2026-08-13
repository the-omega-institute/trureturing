using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Eigenstructure;

internal sealed class ContractingAxisSignDepthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Contracting-axis powers split into parity sign and inverse-golden depth.",
        H("Contracting Axis Sign and Depth"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("contracting-axis-power-sign-depth"),
                DeclarationHandle.Create(
                    "D5/S1/Eigenstructure/ContractingAxisSignDepth."
                    + "contracting_axis_power_sign_depth"),
                H("Contracting powers separate sign and depth"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Operatorname, Grp(F.Id("contractingEigenvalue")), Caret, Grp(F.Id("n")),
                    Sp, Eq, Sp,
                    Open, Minus, D(1), Close, Caret, Grp(F.Id("n")), Sp,
                    Varphi, Caret, Grp(Minus, F.Id("n"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The contracting eigenvalue is minus the reciprocal golden ratio. "
                        + "Its nth power therefore factors into the parity sign (-1)^n "
                        + "and inverse-golden magnitude phi^(-n).")),
                    Paragraph(Text(
                        "The proof is a thin normalization wrapper over the standard power "
                        + "lemmas for negation, inverses, and integer exponents.")),
                    Paragraph(Text(
                        "This is a partial closure of the contracting-axis sign-reversal clause. "
                        + "The expanding-axis assignment and global spiral interpretation remain open."))),
                DescribeRole.Theorem))));
}
