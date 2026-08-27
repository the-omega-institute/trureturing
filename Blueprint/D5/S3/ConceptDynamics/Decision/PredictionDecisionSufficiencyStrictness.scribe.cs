using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Decision;

internal sealed class PredictionDecisionSufficiencyStrictnessDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Decision/PredictionDecisionSufficiencyStrictness."
            + "prediction_sufficiency_implies_decision_sufficiency_strictly";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prediction determines losses and actions, but actions need not determine prediction.",
        H("Prediction and Decision Sufficiency Strictness"),
        Blocks(Describe.Lean(
            DescribeId.Create("prediction-decision-sufficiency-strictness"),
            DeclarationHandle.Create(Declaration),
            H("Prediction sufficiency implies decision sufficiency strictly"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Factoring a predictive PMF through a concept factors both its complete "
                        + "expected-loss profile and the optimizer-set readout through that concept.")),
                Paragraph(Text(
                    "The converse countermodel uses two distinct deterministic predictive laws. "
                        + "Its outcome-dependent loss makes true the unique optimizer in both states, "
                        + "so one constant concept determines the actions but not the predictive law."))),
            DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);

    private static Formula BindMany(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula LetFunction(
        Formula name,
        Formula type,
        Formula.BoundVariable[] variables,
        Formula value) => F.Seq(
            F.Operatorname, F.Grp(F.Id("let")), F.Sp, name, F.Colon, F.Sp, type,
            F.Comma, F.Sp,
            BindMany(variables, Equal(
                Apply(name, [.. variables.Select(variable => F.Id(variable.Name.Value))]),
                value)),
            F.Semi, F.Sp);

    private static Formula OptimizerPredicate(
        Formula expectedLoss,
        Formula state,
        Formula action,
        Formula alternative,
        Formula actionType) =>
        BindMany(
            [Bound("alternative", actionType)],
            LessOrEqual(
                Apply(expectedLoss, state, action),
                Apply(expectedLoss, state, alternative)));

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula real = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        Formula stateType = F.Id("X");
        Formula conceptType = F.Id("C");
        Formula outcomeType = F.Id("Outcome");
        Formula actionType = F.Id("Action");
        Formula state = F.Id("state");
        Formula action = F.Id("action");
        Formula alternative = F.Id("alternative");
        Formula outcome = F.Id("outcome");
        Formula prediction = F.Id("prediction");
        Formula concept = F.Id("concept");
        Formula loss = F.Id("loss");
        Formula expectedLoss = F.Id("expectedLoss");
        Formula optimalActions = F.Id("optimalActions");

        Formula forwardExpectedDefinition = LetFunction(
            expectedLoss,
            Arrow(stateType, Arrow(actionType, real)),
            [Bound("state", stateType), Bound("action", actionType)],
            Call("integral",
                Call("toMeasure", Apply(prediction, state)),
                Apply(loss, action)));
        Formula forwardOptimalDefinition = LetFunction(
            optimalActions,
            Arrow(stateType, Call("Set", actionType)),
            [Bound("state", stateType)],
            F.Seq(
                F.Left, F.OpenBrace, action, F.Colon, F.Sp, actionType, F.Sp,
                F.Mid, F.Sp,
                OptimizerPredicate(expectedLoss, state, action, alternative, actionType),
                F.Right, F.CloseBrace));
        Formula forwardConclusion = Implies(
            Call("Refines", prediction, concept),
            And(
                Call("Refines", expectedLoss, concept),
                Call("Refines", optimalActions, concept)));

        Formula boolean = F.Id("Bool");
        Formula unit = F.Id("Unit");
        Formula predictionExample = F.Id("predictionExample");
        Formula lossExample = F.Id("lossExample");
        Formula expectedLossExample = F.Id("expectedLossExample");
        Formula optimalActionsExample = F.Id("optimalActionsExample");
        Formula conceptExample = F.Id("conceptExample");
        Formula zero = new Formula.Number(0);
        Formula one = new Formula.Number(1);
        Formula two = new Formula.Number(2);

        Formula predictionDefinition = LetFunction(
            predictionExample,
            Arrow(boolean, Call("PMF", boolean)),
            [Bound("state", boolean)],
            Call("pure", state));
        Formula lossDefinition = LetFunction(
            lossExample,
            Arrow(boolean, Arrow(boolean, real)),
            [Bound("action", boolean), Bound("outcome", boolean)],
            Call("if", action, zero, Call("if", outcome, two, one)));
        Formula expectedDefinition = LetFunction(
            expectedLossExample,
            Arrow(boolean, Arrow(boolean, real)),
            [Bound("state", boolean), Bound("action", boolean)],
            Call("integral",
                Call("toMeasure", Apply(predictionExample, state)),
                Apply(lossExample, action)));
        Formula optimalDefinition = LetFunction(
            optimalActionsExample,
            Arrow(boolean, Call("Set", boolean)),
            [Bound("state", boolean)],
            F.Seq(
                F.Left, F.OpenBrace, action, F.Colon, F.Sp, boolean, F.Sp,
                F.Mid, F.Sp,
                OptimizerPredicate(
                    expectedLossExample, state, action, alternative, boolean),
                F.Right, F.CloseBrace));
        Formula conceptDefinition = LetFunction(
            conceptExample,
            Arrow(boolean, unit),
            [Bound("state", boolean)],
            F.Id("unit"));
        Formula countermodel = F.Seq(
            predictionDefinition,
            lossDefinition,
            expectedDefinition,
            optimalDefinition,
            conceptDefinition,
            And(
                Call("Refines", optimalActionsExample, conceptExample),
                F.Seq(F.Neg, F.Sp, Call("Refines", predictionExample, conceptExample))));

        Formula theoremBody = F.Seq(
            forwardExpectedDefinition,
            forwardOptimalDefinition,
            And(forwardConclusion, countermodel));
        Formula boundData = BindMany(
            [
                Bound("prediction", Arrow(stateType, Call("PMF", outcomeType))),
                Bound("concept", Arrow(stateType, conceptType)),
                Bound("loss", Arrow(actionType, Arrow(outcomeType, real))),
            ],
            theoremBody);
        Formula instances = And(
            Call("MeasurableSpace", outcomeType),
            Call("MeasurableSingletonClass", outcomeType));

        return F.Disp(BindMany(
            [
                Bound("X", type),
                Bound("C", type),
                Bound("Outcome", type),
                Bound("Action", type),
            ],
            Implies(instances, boundData)));
    }
}
