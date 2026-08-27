using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.SequentialDecisionRisk;

internal sealed class PredictiveRiskOptimizerHierarchyDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Estimation/SequentialDecisionRisk/PredictiveRiskOptimizerHierarchy."
            + "predictive_risk_optimizer_kernel_hierarchy";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete predictive laws refine expected-risk equivalence, which refines equality of all task optimizer sets.",
        H("Predictive Risk Optimizer Kernel Hierarchy"),
        Blocks(Describe.Lean(
            DescribeId.Create("predictive-risk-optimizer-kernel-hierarchy"),
            DeclarationHandle.Create(Declaration),
            H("Predictive, risk, and optimizer quotient order"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A history carries a complete probability mass function on finite outcomes. "
                        + "The expected-risk profile is the finite sum of that law against every "
                        + "task, action, and loss coordinate.")),
                Paragraph(Text(
                    "The optimizer profile is the complete set of actions attaining the minimum "
                        + "risk for each task. Equality of predictive laws therefore gives equality "
                        + "of risk profiles, and equality of risk profiles gives equality of all "
                        + "optimizer sets.")),
                Paragraph(Text(
                    "The theorem uses equality kernels of these source-semantic profiles, so both "
                        + "inclusions remain falsifiable and no quotient carrier is defined by its "
                        + "target relation."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula TheoremFormula()
    {
        Formula historyType = F.Id("H");
        Formula outcomeType = F.Id("Y");
        Formula taskType = F.Id("L");
        Formula actionType = F.Id("A");
        Formula type = F.Id("Type");
        Formula law = F.Id("Psi");
        Formula loss = F.Id("ell");
        Formula h = F.Id("h");
        Formula hPrime = Seq(F.Id("h"), Apos);
        Formula y = F.Id("y");
        Formula task = F.Id("ell");
        Formula action = F.Id("a");
        Formula alternative = F.Id("b");
        Formula lawType = Call("PMF", outcomeType);
        Formula lossType = Arrow(taskType, Arrow(actionType, Arrow(outcomeType, Seq(Mathbb, Grp(F.Id("R"))))));
        Formula risk = Call("riskProfile", law, loss);
        Formula optimizer = Call("optimizerProfile", law, loss);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, historyType, Comma, Sp, outcomeType, Comma, Sp,
            taskType, Comma, Sp, actionType, Colon, Sp, type, Comma, RowBreak, Grp(),
            Call("Fintype", outcomeType), Comma, Sp,
            law, Colon, Sp, historyType, Sp, To, Sp, lawType, Comma, Sp,
            loss, Colon, Sp, lossType, Comma, RowBreak, Grp(),
            new Formula.Logic(
                Seq(Call("ker", law), Sp, Subseteq, Sp, Call("ker", risk)),
                FormulaLogicOperator.And,
                Seq(Call("ker", risk), Sp, Subseteq, Sp, Call("ker", optimizer))), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
