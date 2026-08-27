using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.SequentialDecisionRisk;

internal sealed class DistinctRiskSharedOptimizerDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Estimation/SequentialDecisionRisk/DistinctRiskSharedOptimizer."
            + "distinct_risk_profiles_can_share_optimizer_profile";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct expected-risk profiles can induce the same complete optimizer profile.",
        H("Distinct Risks with a Shared Optimizer"),
        Blocks(Describe.Lean(
            DescribeId.Create("distinct-risk-profiles-shared-optimizer-profile"),
            DeclarationHandle.Create(Declaration),
            H("Different risk values can have the same argmin profile"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A Boolean history is mapped to the matching pure Boolean outcome law. "
                        + "The loss depends on the outcome but not on the action, using the "
                        + "canonical finite-sum riskProfile from the imported hierarchy.")),
                Paragraph(Text(
                    "The two histories therefore have different risk profiles, while every "
                        + "action ties at each history. Their canonical optimizerProfile values "
                        + "are equal, giving the required reverse-inclusion countermodel."))),
            DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula TheoremFormula()
    {
        Formula boolean = F.Id("Bool");
        Formula unit = F.Id("Unit");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula law = F.Id("Psi");
        Formula loss = F.Id("ell");
        Formula lawType = Arrow(boolean, Call("PMF", boolean));
        Formula lossType = Arrow(unit, Arrow(boolean, Arrow(boolean, real)));
        Formula falseRisk = Call("riskProfile", law, loss, F.Id("false"));
        Formula trueRisk = Call("riskProfile", law, loss, F.Id("true"));
        Formula falseOptimizer = Call("optimizerProfile", law, loss, F.Id("false"));
        Formula trueOptimizer = Call("optimizerProfile", law, loss, F.Id("true"));
        Formula conclusion = new Formula.Logic(
            new Formula.Relation(
                falseRisk, FormulaRelationOperator.NotEqual, trueRisk),
            FormulaLogicOperator.And,
            new Formula.Relation(
                falseOptimizer, FormulaRelationOperator.Equal, trueOptimizer));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("Psi", lawType), Bound("ell", lossType)],
            conclusion));
    }
}
