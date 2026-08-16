using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ResourceOrder;

internal sealed class OneStepHedgingGainDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonzero orthogonal innovation gives the exact one-step squared hedging gain.",
        H("One-Step Hedging Gain"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nonzero-innovation-gives-exact-squared-hedging-gain"),
                DeclarationHandle.Create(
                    "D5/S3/ResourceOrder/OneStepHedgingGain"
                    + ".one_step_hedging_gain"),
                H("A nonzero innovation gives the exact squared hedging gain"),
                StatementSource.FromAuthor(OneStepHedgingGainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let M be contained in Mnext in a finite-dimensional real inner-product "
                        + "space. Assume the directions added to M are exactly the line spanned "
                        + "by a nonzero residual vector.")),
                    Paragraph(Text(
                        "For every target x, the decrease in squared metric distance to the "
                        + "attainable subspace is the squared absolute inner product with the "
                        + "residual, divided by the residual's squared norm.")),
                    Paragraph(Text(
                        "The proof imports the repository's innovation_energy_recurrence. "
                        + "Pinned Mathlib exact-name searches and Loogle each found "
                        + "Submodule.starProjection_singleton and "
                        + "Submodule.starProjection_minimal; Metric.infDist_eq_iInf connects "
                        + "the minimizing projection to distance. Two initial natural-language "
                        + "smart-search queries exited after their declaration-name scan and are "
                        + "not counted as negative search results.")),
                    Paragraph(Text(
                        "This closes qdo-v1 theorem/34.5, atom "
                        + "qdo-residual-97fbc85483c01bc3d120362dee0903ecffe71aeb5b4dc5668678e8fa"
                        + "439f0eb0. "
                        + "The statement covers the displayed one-step gain identity; it does "
                        + "not assert any additional market-completeness conclusion."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula>
        {
            Operatorname,
            Grp(F.Id(name)),
            Open,
        };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula OneStepHedgingGainFormula()
    {
        Formula space = F.Id("V");
        Formula oldSpace = F.Id("M");
        Formula newSpace = F.Id("Mnext");
        Formula target = F.Id("x");
        Formula residual = F.Id("residual");
        Formula inner = Seq(Langle, Sp, target, Comma, Sp, residual, Sp, Rangle);
        Formula absoluteInner = Seq(Lvert, Sp, inner, Sp, Rvert);
        Formula residualNorm = Seq(Vert, Sp, residual, Sp, Vert);

        return Disp(Seq(
            Forall, Sp, space, Colon, Sp,
            Operatorname, Grp(F.Id("FiniteDimensionalRealInnerProductSpace")), Comma, Esc,
            Forall, Sp, oldSpace, Comma, Sp, newSpace, InMacro, Sp,
            Operatorname, Grp(F.Id("Submodule")), Open, space, Close, Comma, Esc,
            Forall, Sp, target, Comma, Sp, residual, InMacro, Sp, space, Comma, Esc,
            oldSpace, Sp, Subseteq, Sp, newSpace, Sp, Land, Sp,
            Call("innovationSubspace", oldSpace, newSpace), Sp, Eq, Sp,
            Call("span", residual), Sp, Land, Sp,
            residual, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
            Call("dist", target, oldSpace), Caret, Grp(D(2)), Sp, Minus, Sp,
            Call("dist", target, newSpace), Caret, Grp(D(2)), Sp, Eq, Sp,
            Frac, Grp(absoluteInner, Caret, Grp(D(2))),
            Grp(residualNorm, Caret, Grp(D(2))), Dot));
    }
}
