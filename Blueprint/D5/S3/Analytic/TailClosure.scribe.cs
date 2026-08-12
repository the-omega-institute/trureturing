using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class TailClosureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Vanishing tail budgets force certified readings to converge to the exact value.",
        H("Vanishing Tail Budgets Close"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("vanishing-tail-budget-closes"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/TailClosure.vanishing_tail_budget_closes"),
                H("A vanishing tail budget closes the certified readings"),
                StatementSource.FromAuthor(Disp(Seq(
                    Vert, Sp, F.Id("v"), Minus, F.Id("r"), Open, F.Id("W"), Close,
                    Sp, Vert,
                    Sp, Le, Sp, F.Id("b"), Open, F.Id("W"), Close,
                    Comma, Sp, F.Id("b"), Open, F.Id("W"), Close,
                    Sp, To, Sp, D(0),
                    Sp, Rightarrow, Sp,
                    F.Id("r"), Open, F.Id("W"), Close,
                    Sp, To, Sp, F.Id("v")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A certificate on a cofinal family of finite windows gives an exact "
                        + "value, a reading at every window, and a nonnegative budget bounding "
                        + "the absolute reading error. When those budgets converge to zero "
                        + "along a chosen window filter, the readings converge to the exact "
                        + "value. This is the closure step asserted by the source atom: the "
                        + "infinite object is handled through finite readings and a budget "
                        + "whose disappearance is itself machine checked.")),
                    Paragraph(Text(
                        "The library search found the exact analytic core in pinned Mathlib. "
                        + "The Lean declaration is therefore a thin honest wrapper: "
                        + "Certificate.error_le supplies the pointwise distance bound, "
                        + "squeeze_zero makes that distance converge to zero, and "
                        + "tendsto_iff_dist_tendsto_zero converts the distance statement into "
                        + "convergence of the certified readings. No independent convergence "
                        + "argument is re-proved here."))),
                DescribeRole.Theorem))));
}
