using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.SequentialDecisionRisk;

internal sealed class FiniteDeficiencyRiskTransferDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Estimation/SequentialDecisionRisk/FiniteDeficiencyRiskTransfer."
            + "deficiency_risk_bound";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One-way finite experiment deficiency bounds the increase in optimal risk for every loss in the unit interval.",
        H("Finite Deficiency Risk Transfer"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-deficiency-risk-transfer"),
            DeclarationHandle.Create(Declaration),
            H("Deficiency controls bounded-loss Bayes risk"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "A target decision is transported through each source-to-target simulator. The "
                    + "frozen statewise total-variation bound is averaged by the prior, after which "
                    + "extended-nonnegative infima optimize the decision and simulator independently."))),
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
        Formula state = F.Id("Theta");
        Formula sourceObservation = F.Id("X");
        Formula targetObservation = F.Id("Y");
        Formula action = F.Id("A");
        Formula prior = F.Id("pi");
        Formula loss = F.Id("ell");
        Formula source = F.Id("E");
        Formula target = F.Id("F");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula stateValue = F.Id("theta");
        Formula actionValue = F.Id("a");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, sourceObservation, Comma, Sp,
            targetObservation, Comma, Sp, action, Colon, Sp, F.Id("Type"), Comma,
            RowBreak, Grp(),
            Call("Fintype", state), Sp, Land, Sp, Call("Nonempty", state), Sp, Land, Sp,
            Call("Fintype", sourceObservation), Sp, Land, Sp,
            Call("Fintype", targetObservation), Sp, Land, Sp, Call("Fintype", action), Comma,
            RowBreak, Grp(),
            prior, Colon, Sp, Arrow(state, real), Comma, Sp,
            loss, Colon, Sp, Arrow(state, Arrow(action, real)), Comma, Sp,
            source, Colon, Sp, Arrow(state, Arrow(sourceObservation, real)), Comma, Sp,
            target, Colon, Sp, Arrow(state, Arrow(targetObservation, real)), Comma,
            RowBreak, Grp(),
            Open, Forall, Sp, stateValue, Comma, Sp, D(0), Sp, Leq, Sp,
            Call("apply", prior, stateValue), Close, Sp, Land, Sp,
            Call("sum", prior), Sp, Eq, Sp, D(1), Sp, Land, Sp,
            Call("IsRowStochastic", source), Sp, Land, Sp,
            Call("IsRowStochastic", target), Comma, RowBreak, Grp(),
            Open, Forall, Sp, stateValue, Comma, Sp, actionValue, Comma, Sp,
            D(0), Sp, Leq, Sp, Call("apply", loss, stateValue, actionValue), Sp,
            Land, Sp, Call("apply", loss, stateValue, actionValue), Sp, Leq, Sp, D(1), Close,
            Sp, Rightarrow, RowBreak, Grp(),
            Call("finiteBayesRisk", prior, loss, source), Sp, Leq, Sp,
            Call("finiteBayesRisk", prior, loss, target), Sp, Plus, Sp,
            Call("finiteDeficiency", target, source), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
