using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Isolation;

internal sealed class AnalyticZeroDichotomyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A complex-analytic relation either vanishes identically or has isolated zeros.",
        H("The Analytic Zero Dichotomy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("analytic-relations-vanish-identically-or-have-isolated-zeros"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Isolation/AnalyticZeroDichotomy."
                    + "analytic_zero_dichotomy"),
                H("Analytic relations vanish identically or have isolated zeros"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("AnalyticOnNhd")),
                    Open, Mathbb, Grp(F.Id("C")), Comma, Sp,
                    F.Id("f"), Comma, Sp, F.Id("U"), Close,
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("IsPreconnected")),
                    Open, F.Id("U"), Close,
                    Sp, Rightarrow, Sp, RowBreak,
                    Open,
                    F.Id("f"), Eq, D(0), Sp,
                    Operatorname, Grp(F.Id("on")), Sp, F.Id("U"),
                    Close,
                    Sp, Lor, Sp,
                    Operatorname, Grp(F.Id("Eventually")), Underscore,
                    Grp(Operatorname, Grp(F.Id("codiscreteWithin")),
                        Open, F.Id("U"), Close),
                    Sp, F.Id("f"), Open, F.Id("z"), Close, Neq, D(0), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let f be complex analytic on a preconnected set U. Exactly the "
                        + "rigidity needed by the source follows: either f is zero throughout "
                        + "U, or f is nonzero codiscretely within U. In one complex variable, "
                        + "the latter is the filter formulation that the zeros are isolated.")),
                    Paragraph(Text(
                        "Consequently, zeros accumulating at an interior point cannot occur in "
                        + "the nonzero branch. Mathlib also exposes this consequence directly as "
                        + "`AnalyticOnNhd.eqOn_zero_of_preconnected_of_mem_closure`; the displayed "
                        + "dichotomy retains both alternatives of the source atom instead of only "
                        + "that consequence.")),
                    Paragraph(Text(
                        "Mathlib was searched before proving. Local searches of pinned "
                        + "`Mathlib/Analysis/Analytic/IsolatedZeros.lean` found the exact theorem "
                        + "`AnalyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected` and the "
                        + "accumulation-point identity theorem. The Lean proof imports and applies "
                        + "the exact dichotomy, with no independent analytic argument.")),
                    Paragraph(Text(
                        "Repository duplicate searches found applications of Mathlib's identity "
                        + "principle and a specialized rational-span level-set theorem, but no "
                        + "existing public declaration of this general complex-analytic zero "
                        + "dichotomy."))),
                DescribeRole.Theorem))));
}
