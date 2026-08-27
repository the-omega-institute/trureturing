using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Decision;

internal sealed class SamePredictionOppositeOptimaDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Decision/SamePredictionOppositeOptima."
            + "same_prediction_opposite_unique_optima";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One PMF prediction admits opposite unique optima under two loss models.",
        H("Same Prediction, Opposite Optimal Actions"),
        Blocks(Describe.Lean(
            DescribeId.Create("same-prediction-opposite-unique-optima"),
            DeclarationHandle.Create(Declaration),
            H("A predictive law does not determine value"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A single Boolean-state prediction interface is constructed as a PMF on "
                        + "Unit. Two Boolean-action loss models are quantified together with "
                        + "that same interface, and both expected-loss profiles use its PMF "
                        + "through the canonical toMeasure integral.")),
                Paragraph(Text(
                    "The complete optimizer set is the singleton false action under the first "
                        + "loss and the singleton true action under the second loss, for every "
                        + "state. Thus the predictive PMF alone does not determine which action "
                        + "has value.")),
                Paragraph(Text(
                    "The imported decision-family owner supplies the expectation and full "
                        + "optimizer-set shapes. Repository and pinned-Mathlib searches found "
                        + "no theorem packaging this opposite-optimum countermodel."))),
            DescribeRole.Theorem))));

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

    private static Formula TheoremFormula()
    {
        Formula boolean = F.Id("Bool");
        Formula unit = F.Id("Unit");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula prediction = F.Id("K");
        Formula firstLoss = Seq(F.Id("ell"), Underscore, Grp(D(0)));
        Formula secondLoss = Seq(F.Id("ell"), Underscore, Grp(D(1)));
        Formula loss = F.Id("ell");
        Formula expectedLoss = F.Id("Risk");
        Formula optimal = F.Id("Opt");
        Formula state = F.Id("x");
        Formula action = F.Id("a");
        Formula alternative = F.Id("b");
        Formula predictionType = Arrow(boolean, Call("PMF", unit));
        Formula lossType = Seq(
            boolean, Sp, To, Sp, Open, unit, Sp, To, Sp, real, Close);
        Formula expectedType = Seq(
            Open, boolean, Sp, To, Sp, Open, unit, Sp, To, Sp, real, Close,
            Close, Sp, To, Sp, boolean, Sp, To, Sp, boolean, Sp, To, Sp, real);
        Formula optimalType = Seq(
            Open, boolean, Sp, To, Sp, Open, unit, Sp, To, Sp, real, Close,
            Close, Sp, To, Sp, boolean, Sp, To, Sp, Call("Set", boolean));
        Formula riskAt(Formula model, Formula chosen) =>
            Apply(expectedLoss, model, state, chosen);
        Formula optimizerPredicate = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("b"),
            boolean,
            LessOrEqual(riskAt(loss, action), riskAt(loss, alternative)));
        Formula expectedDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            expectedLoss, Colon, Sp, expectedType, Comma, Sp,
            Forall, Sp, loss, Colon, Sp, lossType, Comma, Sp,
            state, Colon, Sp, boolean, Comma, Sp,
            action, Colon, Sp, boolean, Comma, Sp,
            riskAt(loss, action), Sp, Colon, Eq, Sp,
            Call("integral", Call("toMeasure", Apply(prediction, state)),
                Apply(loss, action)), Semi, Sp);
        Formula optimizerDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            optimal, Colon, Sp, optimalType, Comma, Sp,
            Forall, Sp, loss, Colon, Sp, lossType, Comma, Sp,
            state, Colon, Sp, boolean, Comma, Sp,
            Apply(optimal, loss, state), Sp, Colon, Eq, Sp,
            Left, OpenBrace, action, Colon, Sp, boolean, Sp, Mid, Sp,
            optimizerPredicate, Right, CloseBrace, Semi, Sp);
        Formula firstOptimum = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("x"),
            boolean,
            Equal(Apply(optimal, firstLoss, state),
                new Formula.SetLiteral([F.Id("false")])));
        Formula secondOptimum = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("x"),
            boolean,
            Equal(Apply(optimal, secondLoss, state),
                new Formula.SetLiteral([F.Id("true")])));

        return Disp(Seq(
            Exists, Sp, prediction, Colon, Sp, predictionType, Comma, Sp,
            firstLoss, Comma, Sp, secondLoss, Colon, Sp, lossType, Comma, RowBreak, Grp(),
            expectedDefinition, RowBreak, Grp(),
            optimizerDefinition, RowBreak, Grp(),
            Open, firstOptimum, Close, Sp, Land, Sp,
            Open, secondOptimum, Close, Dot));
    }
}
