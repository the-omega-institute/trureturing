using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Decision;

internal sealed class ArbitraryPredictionOppositeOptimaDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Decision/ArbitraryPredictionOppositeOptima."
            + "arbitrary_prediction_opposite_unique_optima";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every PMF prediction admits opposite unique optima under two constant loss models.",
        H("Arbitrary Prediction, Opposite Optimal Actions"),
        Blocks(Describe.Lean(
            DescribeId.Create("arbitrary-prediction-opposite-unique-optima"),
            DeclarationHandle.Create(Declaration),
            H("Any fixed predictive law is compatible with opposite unique optima"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The same arbitrary PMF-valued prediction is used for both losses. "
                        + "The false action has constant losses zero and one respectively, "
                        + "while the true action has constant losses one and zero.")),
                Paragraph(Text(
                    "Expected loss is constructed by integrating each action loss against "
                        + "the supplied predictive PMF. The displayed optimal-action sets are "
                        + "the full pointwise argmin sets, not separately chosen selectors."))),
            DescribeRole.Theorem))));

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
        Formula stateType = F.Id("X");
        Formula outcomeType = F.Id("Y");
        Formula boolean = F.Id("Bool");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula prediction = F.Id("K");
        Formula lossFalse = F.Id("ellL");
        Formula lossTrue = F.Id("ellR");
        Formula loss = F.Id("ell");
        Formula expectedLoss = F.Id("Risk");
        Formula optimal = F.Id("Opt");
        Formula state = F.Id("x");
        Formula action = F.Id("a");
        Formula alternative = F.Id("b");
        Formula outcome = F.Id("y");
        Formula lossType = Seq(
            boolean, Sp, To, Sp, outcomeType, Sp, To, Sp, real);
        Formula expectedType = Seq(
            Open, lossType, Close, Sp, To, Sp, stateType, Sp, To, Sp,
            boolean, Sp, To, Sp, real);
        Formula optimalType = Seq(
            Open, lossType, Close, Sp, To, Sp, stateType, Sp, To, Sp,
            Call("Set", boolean));
        Formula riskAt(Formula model, Formula chosen) =>
            Apply(expectedLoss, model, state, chosen);
        Formula optimizerPredicate = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("b"),
            boolean,
            LessOrEqual(riskAt(loss, action), riskAt(loss, alternative)));
        Formula lossFalseDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            lossFalse, Colon, Sp, lossType, Comma, Sp,
            Forall, Sp, action, Colon, Sp, boolean, Comma, Sp,
            outcome, Colon, Sp, outcomeType, Comma, Sp,
            Apply(lossFalse, action, outcome), Sp, Colon, Eq, Sp,
            Call("if", action, D(1), D(0)), Semi, Sp);
        Formula lossTrueDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            lossTrue, Colon, Sp, lossType, Comma, Sp,
            Forall, Sp, action, Colon, Sp, boolean, Comma, Sp,
            outcome, Colon, Sp, outcomeType, Comma, Sp,
            Apply(lossTrue, action, outcome), Sp, Colon, Eq, Sp,
            Call("if", action, D(0), D(1)), Semi, Sp);
        Formula expectedDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            expectedLoss, Colon, Sp, expectedType, Comma, Sp,
            Forall, Sp, loss, Colon, Sp, lossType, Comma, Sp,
            state, Colon, Sp, stateType, Comma, Sp,
            action, Colon, Sp, boolean, Comma, Sp,
            riskAt(loss, action), Sp, Colon, Eq, Sp,
            Call("integral", Call("toMeasure", Apply(prediction, state)),
                Apply(loss, action)), Semi, Sp);
        Formula optimizerDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            optimal, Colon, Sp, optimalType, Comma, Sp,
            Forall, Sp, loss, Colon, Sp, lossType, Comma, Sp,
            state, Colon, Sp, stateType, Comma, Sp,
            Apply(optimal, loss, state), Sp, Colon, Eq, Sp,
            Left, OpenBrace, action, Colon, Sp, boolean, Sp, Mid, Sp,
            optimizerPredicate, Right, CloseBrace, Semi, Sp);
        Formula firstOptimum = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("x"),
            stateType,
            Equal(Apply(optimal, lossFalse, state),
                new Formula.SetLiteral([F.Id("false")])));
        Formula secondOptimum = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("x"),
            stateType,
            Equal(Apply(optimal, lossTrue, state),
                new Formula.SetLiteral([F.Id("true")])));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, stateType, Comma, Sp, outcomeType,
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            Call("MeasurableSpace", outcomeType), Sp, Land, Sp,
            Call("MeasurableSingletonClass", outcomeType), Comma, RowBreak, Grp(),
            prediction, Colon, Sp, stateType, Sp, To, Sp,
            Call("PMF", outcomeType), Comma, RowBreak, Grp(),
            lossFalseDefinition, RowBreak, Grp(),
            lossTrueDefinition, RowBreak, Grp(),
            expectedDefinition, RowBreak, Grp(),
            optimizerDefinition, RowBreak, Grp(),
            Open, firstOptimum, Close, Sp, Land, Sp,
            Open, secondOptimum, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
