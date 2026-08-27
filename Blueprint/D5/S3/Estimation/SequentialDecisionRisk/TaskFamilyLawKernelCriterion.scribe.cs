using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.SequentialDecisionRisk;

internal sealed class TaskFamilyLawKernelCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Estimation/SequentialDecisionRisk/TaskFamilyLawKernelCriterion."
            + "task_family_law_kernel_criterion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Separating loss expectations identify predictive laws, while finite event "
            + "indicators identify probability mass functions.",
        H("Task-Family Law Kernel Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("task-family-law-kernel-criterion"),
            DeclarationHandle.Create(Declaration),
            H("Measure-determining tasks recover the predictive kernel"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The risk profile is constructed from the predictive law, the expectation "
                        + "operator, and every loss and action coordinate. If those coordinates "
                        + "determine allowed laws, its equality kernel is exactly the predictive "
                        + "law kernel.")),
                Paragraph(Text(
                    "For a finite outcome carrier, agreement on the expectation of every event "
                        + "indicator includes agreement on singleton events and therefore "
                        + "determines every probability mass."))),
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

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula TheoremFormula()
    {
        Formula historyType = F.Id("H");
        Formula lawType = F.Id("Law");
        Formula outcomeType = F.Id("Y");
        Formula taskType = F.Id("T");
        Formula actionType = F.Id("A");
        Formula finiteOutcomeType = F.Id("Z");
        Formula type = F.Id("Type");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula predictiveLaw = F.Id("Psi");
        Formula expectation = F.Id("E");
        Formula loss = F.Id("ell");
        Formula history = F.Id("h");
        Formula task = F.Id("t");
        Formula action = F.Id("a");
        Formula outcome = F.Id("y");
        Formula firstLaw = F.Id("mu");
        Formula secondLaw = F.Id("nu");
        Formula eventName = F.Id("B");
        Formula finiteOutcome = F.Id("z");

        Formula LossAt(Formula law, Formula taskIndex, Formula actionIndex) =>
            Call("E", law, Lambda(outcome,
                Call("ell", taskIndex, actionIndex, outcome)));

        Formula riskMap = Lambda(history, Lambda(task, Lambda(action,
            LossAt(Apply(predictiveLaw, history), task, action))));

        Formula measureDetermining = Seq(
            Forall, Sp, firstLaw, Comma, Sp, secondLaw, Colon, Sp, lawType, Comma, Sp,
            Open, Forall, Sp, task, Colon, Sp, taskType, Comma, Sp,
            action, Colon, Sp, actionType, Comma, Sp,
            LossAt(firstLaw, task, action), Sp, Eq, Sp,
            LossAt(secondLaw, task, action), Close, Sp, Rightarrow, Sp,
            firstLaw, Sp, Eq, Sp, secondLaw);

        Formula IndicatorExpectation(Formula law, Formula eventFormula) => Seq(
            Sum, Underscore, Grp(finiteOutcome, Colon, Sp, finiteOutcomeType), Sp,
            Call("indicator", eventFormula,
                Lambda(finiteOutcome,
                    Call("toReal", Apply(law, finiteOutcome))),
                finiteOutcome));

        Formula finiteIndicatorSeparation = Seq(
            Forall, Sp, firstLaw, Comma, Sp, secondLaw, Colon, Sp,
            Call("PMF", finiteOutcomeType), Comma, RowBreak, Grp(),
            Open, Forall, Sp, eventName, Colon, Sp,
            Call("Set", finiteOutcomeType), Comma, Sp,
            IndicatorExpectation(firstLaw, eventName), Sp, Eq, Sp,
            IndicatorExpectation(secondLaw, eventName), Close, Sp, Rightarrow, Sp,
            firstLaw, Sp, Eq, Sp, secondLaw);

        Formula conclusion = new Formula.Logic(
            Seq(Call("ker", predictiveLaw), Sp, Eq, Sp, Call("ker", riskMap)),
            FormulaLogicOperator.And,
            finiteIndicatorSeparation);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, historyType, Comma, Sp, lawType, Comma, Sp,
            outcomeType, Comma, Sp, taskType, Comma, Sp, actionType, Comma, Sp,
            finiteOutcomeType, Colon, Sp, type, Comma, RowBreak, Grp(),
            Call("Fintype", finiteOutcomeType), Comma, RowBreak, Grp(),
            predictiveLaw, Colon, Sp, Arrow(historyType, lawType), Comma, RowBreak, Grp(),
            expectation, Colon, Sp,
            Arrow(lawType, Arrow(Grp(Arrow(outcomeType, reals)), reals)),
            Comma, RowBreak, Grp(),
            loss, Colon, Sp,
            Arrow(taskType, Arrow(actionType, Arrow(outcomeType, reals))),
            Comma, RowBreak, Grp(),
            Grp(measureDetermining), Sp, Rightarrow, RowBreak, Grp(),
            conclusion, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
