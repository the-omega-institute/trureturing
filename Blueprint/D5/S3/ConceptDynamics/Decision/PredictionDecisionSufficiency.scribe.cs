using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Decision;

internal sealed class PredictionDecisionSufficiencyDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Decision/PredictionDecisionSufficiency."
            + "prediction_sufficiency_implies_decision_sufficiency";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A sufficient predictive readout determines expected losses and optimal actions.",
        H("Prediction Sufficiency Implies Decision Sufficiency"),
        Blocks(Describe.Lean(
            DescribeId.Create("prediction-sufficiency-implies-decision-sufficiency"),
            DeclarationHandle.Create(Declaration),
            H("Prediction sufficiency implies decision sufficiency"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The outcome carrier has discrete measurable points, and every displayed "
                        + "action loss is integrable under every predicted law.")),
                Paragraph(Text(
                    "Expected loss is the integral of the supplied loss against the same PMF "
                        + "readout appearing in the refinement premise. The optimal-action "
                        + "readout is the full argmin set of that expected-loss profile.")),
                Paragraph(Text(
                    "Composing both constructions with the prediction factor map proves the "
                        + "two refinement clauses simultaneously."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

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

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula conceptCarrier = F.Id("C");
        Formula outcomeType = F.Id("Y");
        Formula actionType = F.Id("A");
        Formula prediction = F.Id("K");
        Formula concept = F.Id("CReadout");
        Formula loss = Ell;
        Formula x = F.Id("x");
        Formula action = F.Id("a");
        Formula outcome = F.Id("y");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula expectedLoss = Call("expectedLoss", prediction, loss);
        Formula optimalActions = Call("optimalActions", prediction, loss);
        Formula expectedAt(Formula chosen) =>
            Apply(expectedLoss, x, chosen);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, conceptCarrier, Comma, Sp,
            outcomeType, Comma, Sp, actionType,
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            prediction, Colon, Sp, state, Sp, To, Sp,
            Call("PMF", outcomeType), Comma, Sp,
            concept, Colon, Sp, state, Sp, To, Sp, conceptCarrier,
            Comma, RowBreak, Grp(),
            loss, Colon, Sp, actionType, Sp, To, Sp, outcomeType, Sp, To, Sp, real,
            Comma, RowBreak, Grp(),
            Call("MeasurableSpace", outcomeType), Sp, Land, Sp,
            Call("MeasurableSingletonClass", outcomeType), Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, x, Colon, Sp, state, Comma, Sp,
            action, Colon, Sp, actionType, Comma, Sp,
            Call("Integrable", Apply(loss, action),
                Call("toMeasure", Apply(prediction, x))), Close,
            Comma, RowBreak, Grp(),
            Forall, Sp, x, Colon, Sp, state, Comma, Sp,
            action, Colon, Sp, actionType, Comma, Sp,
            expectedAt(action), Sp, Colon, Eq, Sp,
            Int, Underscore, Grp(outcomeType), Sp,
            Apply(loss, action, outcome), Thin, F.Id("d"), Apply(prediction, x),
            Comma, RowBreak, Grp(),
            Forall, Sp, x, Colon, Sp, state, Comma, Sp,
            Apply(optimalActions, x), Sp, Colon, Eq, Sp,
            Operatorname, Grp(F.Id("argmin")), Underscore,
            Grp(action, InMacro, Sp, actionType), Sp, expectedAt(action),
            Comma, RowBreak, Grp(),
            Call("Refines", prediction, concept), Sp, Rightarrow, RowBreak, Grp(),
            Call("Refines", expectedLoss, concept), Sp, Land, Sp,
            Call("Refines", optimalActions, concept), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
