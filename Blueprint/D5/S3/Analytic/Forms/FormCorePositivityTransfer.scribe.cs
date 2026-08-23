using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Forms;

internal sealed class FormCorePositivityTransferDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A continuous real form that is nonnegative on a form core is nonnegative on its domain.",
        H("Positivity Transfer from a Form Core"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("form-core-positivity-transfer"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Forms/FormCorePositivityTransfer.nonnegative_of_formCore"),
                H("Nonnegativity on a form core extends to the full domain"),
                StatementSource.FromAuthor(NonnegativeOnFormCoreFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let D be a real normed linear domain, let C be a form-norm dense subset "
                            + "of D, and let q from D to the reals be continuous for that norm. If q "
                            + "is nonnegative at every point of C, then it is nonnegative throughout D.")),
                    Paragraph(Text(
                        "Continuity makes the inverse image of the closed nonnegative real ray a "
                            + "closed subset of D. That subset contains the dense core C, so it must "
                            + "contain every point of D."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula NonnegativeOnFormCoreFormula()
    {
        Formula domain = F.Id("D");
        Formula core = F.Id("C");
        Formula form = F.Id("q");
        Formula point = F.Id("f");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));

        return Disp(Seq(
            Forall, Sp, domain, Comma, Sp, core, Comma, Sp, form, Comma, Sp,
            core, Sp, Subseteq, Sp, domain, Comma, Sp,
            form, Colon, Sp, domain, Sp, To, Sp, real, Comma, Sp,
            Call("Continuous", form), Sp, Land, Sp,
            Call("IsFormCore", domain, core), Sp, Land, Sp,
            Open, Forall, Sp, point, Sp, InMacro, Sp, core, Comma, Sp,
            D(0), Sp, Leq, Sp, Apply(form, point), Close, Sp,
            Rightarrow, Sp, Forall, Sp, point, Sp, InMacro, Sp, domain, Comma, Sp,
            D(0), Sp, Leq, Sp, Apply(form, point), Dot));
    }
}
