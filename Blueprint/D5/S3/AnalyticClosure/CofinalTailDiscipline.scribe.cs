using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure;

internal sealed class CofinalTailDisciplineDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cofinal finite windows and a vanishing certified tail budget close an exact reading.",
        H("Cofinal Windows and Tail Closure"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cofinal-windows-and-vanishing-budget-close"),
                DeclarationHandle.Create(
                    "D5/S3/AnalyticClosure/CofinalTailDiscipline."
                    + "cofinal_windows_and_vanishing_budget_close"),
                H("Cofinal windows and a vanishing budget close"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("Atom"), Comma, Sp, F.Id("Window"), Colon, Sp,
                    Operatorname, Grp(F.Id("Type")), Comma, Sp,
                    Forall, Sp, F.Id("family"), Colon, Sp,
                    Call("CofinalWindowFamily", F.Id("Atom"), F.Id("Window")), Comma, Sp,
                    Forall, Sp, F.Id("control"), Colon, Sp,
                    Call("TailControl", F.Id("Window")), Comma, Sp,
                    Forall, Sp, F.Id("value"), Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, Sp,
                    Forall, Sp, F.Id("certificate"), Colon, Sp,
                    Call("Certificate", F.Id("family"), F.Id("control"), F.Id("value")),
                    Comma, Sp,
                    Forall, Sp, F.Id("windows"), Colon, Sp,
                    Call("Filter", F.Id("Window")), Comma, Sp,
                    Forall, Sp, F.Id("finite"), Colon, Sp,
                    Call("Finset", F.Id("Atom")), Comma, Sp,
                    Operatorname, Grp(F.Id("Tendsto")), Open,
                    Call("budget", F.Id("certificate")), Comma, Sp,
                    F.Id("windows"), Comma, Sp, D(0), Close,
                    Sp, Rightarrow, Sp, Open,
                    Exists, Sp, F.Id("window"), Comma, Sp,
                    F.Id("finite"), Sp, Subseteq, Sp,
                    Call("contents", F.Id("family"), F.Id("window")),
                    Close, Sp, Land, Sp,
                    Operatorname, Grp(F.Id("Tendsto")), Open,
                    Call("reading", F.Id("certificate")), Comma, Sp,
                    F.Id("windows"), Comma, Sp,
                    F.Id("value"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every finite set of source atoms, cofinality supplies a finite "
                        + "window containing it. A certificate assigns each window a reading "
                        + "and a nonnegative tail budget that bounds the reading error. When "
                        + "the budget converges to zero along the chosen window filter, the "
                        + "certified readings converge to the exact value.")),
                    Paragraph(Text(
                        "The proof is a thin wrapper over the cofinality field of the window "
                        + "family and the existing certified tail-closure theorem. It packages "
                        + "the finite-window and tail-budget clauses into the single closure "
                        + "statement asserted by the source atom."))),
                DescribeRole.Theorem))));
}
