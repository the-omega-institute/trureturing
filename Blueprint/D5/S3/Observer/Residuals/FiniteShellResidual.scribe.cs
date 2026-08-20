using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Residuals;

internal sealed class FiniteShellResidualDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite shell compression can vanish while its complementary defect remains nonzero.",
        H("Finite Shell Residual"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-shell-check-does-not-close-residual"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Residuals/FiniteShellResidual."
                        + "finite_shell_check_does_not_close_residual"),
                H("A finite shell check does not close the residual"),
                StatementSource.FromAuthor(FiniteShellFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every finite shell size, the constructed defect vanishes after "
                            + "compression to the listed coordinates while its compression to "
                            + "the complementary residual coordinate remains nonzero.")),
                    Paragraph(Text(
                        "The two explicit compressions therefore witness that the finite-shell "
                            + "vanishing assertion alone does not imply residual vanishing."))),
                DescribeRole.Theorem))));

    private static Formula FiniteShellFormula()
    {
        Formula size = F.Id("N");
        Formula shell = Seq(
            Operatorname, Grp(F.Id("shellProjection")), Open, size, Close);
        Formula residual = Seq(
            Operatorname, Grp(F.Id("residualProjection")), Open, size, Close);
        Formula defect = Seq(
            Operatorname, Grp(F.Id("defectOperator")), Open, size, Close);
        Formula shellCompression = Seq(
            shell, Sp, Cdot, Sp, defect, Sp, Cdot, Sp, shell);
        Formula residualCompression = Seq(
            residual, Sp, Cdot, Sp, defect, Sp, Cdot, Sp, residual);

        return Disp(Seq(
            Forall, Sp, size, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            shellCompression, Sp, Eq, Sp, D(0), Sp, Land, RowBreak,
            residualCompression, Sp, Neq, Sp, D(0), Sp, Land, RowBreak,
            Neg, Sp, Open,
            shellCompression, Sp, Eq, Sp, D(0), Sp, Rightarrow, Sp,
            residualCompression, Sp, Eq, Sp, D(0), Close, Dot));
    }
}
