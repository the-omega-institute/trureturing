using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Uncertainty;

internal sealed class FourWayIndependenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite source models realize every truth profile of four uncertainty kinds.",
        H("Four-Way Uncertainty Independence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("four-uncertainties-have-all-truth-profiles"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Uncertainty/FourWayIndependence."
                        + "four_uncertainties_have_all_truth_profiles"),
                H("All four-way uncertainty truth profiles are realizable"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The profile p assigns independent truth values to epistemic, "
                            + "aleatoric, model, and normative uncertainty.")),
                    Paragraph(Text(
                        "Evidence switches between identity and a constant readout. Future "
                            + "support switches between a singleton and both Boolean outcomes. "
                            + "Prediction switches between a constant and the model bit, while "
                            + "preference switches between no rankings and two opposed rankings.")),
                    Paragraph(Text(
                        "Each uncertainty predicate is defined from its source primitive: "
                            + "evidence noninjectivity, two distinct supported futures, compatible "
                            + "models with distinct predictions, and distinct doctrines with "
                            + "opposite rankings of distinct actions.")),
                    Paragraph(Text(
                        "The four public equivalences hold for every p. Thus all sixteen truth "
                            + "profiles occur, including a model with any chosen uncertainty true "
                            + "and any other chosen uncertainty false, so no general implication "
                            + "exists between distinct kinds."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Assign(Formula left, Formula right) =>
        Seq(left, Sp, Colon, Eq, Sp, right);

    private static Formula Declare(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TheoremFormula()
    {
        Formula profile = F.Id("p");
        Formula boolean = F.Id("Bool");
        Formula unit = F.Id("Unit");
        Formula proposition = F.Id("Prop");
        Formula trueValue = F.Id("true");
        Formula falseValue = F.Id("false");
        Formula evidence = F.Id("C");
        Formula support = F.Id("Supp");
        Formula compatible = F.Id("Compat");
        Formula prediction = F.Id("Pred");
        Formula preference = F.Id("Pref");
        Formula epistemic = F.Id("Epistemic");
        Formula aleatoric = F.Id("Aleatoric");
        Formula modelUncertainty = F.Id("ModelUncertainty");
        Formula normative = F.Id("Normative");
        Formula state = F.Id("x");
        Formula action = F.Id("u");
        Formula outcome = F.Id("y");
        Formula otherOutcome = F.Id("z");
        Formula firstModel = F.Id("m");
        Formula secondModel = F.Id("n");
        Formula target = F.Id("t");
        Formula leftDoctrine = F.Id("i");
        Formula rightDoctrine = F.Id("j");
        Formula firstAction = F.Id("a");
        Formula secondAction = F.Id("b");
        Formula profileBit(byte index) => Apply(profile, D(index));
        Formula enabled(byte index) =>
            Seq(profileBit(index), Sp, Eq, Sp, trueValue);
        Formula evidenceType = Arrow(boolean, boolean);
        Formula supportType = Arrow(boolean, Arrow(unit, Arrow(boolean, proposition)));
        Formula compatibleType = Arrow(boolean, proposition);
        Formula predictionType = Arrow(boolean, Arrow(unit, boolean));
        Formula preferenceType = Arrow(boolean, Arrow(boolean, Arrow(boolean, proposition)));
        Formula evidenceBody = Call("if", enabled(0), falseValue, state);
        Formula supportBody = Seq(
            enabled(1), Sp, Lor, Sp, outcome, Sp, Eq, Sp, falseValue);
        Formula predictionBody = Call("if", enabled(2), firstModel, falseValue);
        Formula opposedPreference = Seq(
            enabled(3), Sp, Land, Sp, Open,
            Open, leftDoctrine, Sp, Eq, Sp, falseValue, Sp, Land, Sp,
            firstAction, Sp, Eq, Sp, trueValue, Sp, Land, Sp,
            secondAction, Sp, Eq, Sp, falseValue, Close,
            Sp, Lor, Sp,
            Open, leftDoctrine, Sp, Eq, Sp, trueValue, Sp, Land, Sp,
            firstAction, Sp, Eq, Sp, falseValue, Sp, Land, Sp,
            secondAction, Sp, Eq, Sp, trueValue, Close,
            Close);
        Formula epistemicBody = Seq(Neg, Sp, Call("Injective", evidence));
        Formula aleatoricBody = Seq(
            Exists, Sp, state, Colon, Sp, boolean, Comma, Sp,
            action, Colon, Sp, unit, Comma, Sp,
            outcome, Comma, Sp, otherOutcome, Colon, Sp, boolean, Comma, Sp,
            outcome, Sp, Neq, Sp, otherOutcome, Sp, Land, Sp,
            Apply(support, state, action, outcome), Sp, Land, Sp,
            Apply(support, state, action, otherOutcome));
        Formula modelBody = Seq(
            Exists, Sp, firstModel, Comma, Sp, secondModel, Colon, Sp, boolean, Comma, Sp,
            target, Colon, Sp, unit, Comma, Sp,
            firstModel, Sp, Neq, Sp, secondModel, Sp, Land, Sp,
            Apply(compatible, firstModel), Sp, Land, Sp,
            Apply(compatible, secondModel), Sp, Land, Sp,
            Apply(prediction, firstModel, target), Sp, Neq, Sp,
            Apply(prediction, secondModel, target));
        Formula normativeBody = Seq(
            Exists, Sp, leftDoctrine, Comma, Sp, rightDoctrine, Comma, Sp,
            firstAction, Comma, Sp, secondAction, Colon, Sp, boolean, Comma, Sp,
            leftDoctrine, Sp, Neq, Sp, rightDoctrine, Sp, Land, Sp,
            firstAction, Sp, Neq, Sp, secondAction, Sp, Land, Sp,
            Apply(preference, leftDoctrine, firstAction, secondAction), Sp, Land, Sp,
            Apply(preference, rightDoctrine, secondAction, firstAction));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Declare(profile, Arrow(Call("Fin", D(4)), boolean)), Comma,
            RowBreak, Grp(),
            Declare(evidence, evidenceType), Comma, Sp,
            Assign(Apply(evidence, state), evidenceBody), Comma,
            RowBreak, Grp(),
            Declare(support, supportType), Comma, Sp,
            Assign(Apply(support, state, action, outcome), supportBody), Comma,
            RowBreak, Grp(),
            Declare(compatible, compatibleType), Comma, Sp,
            Assign(Apply(compatible, firstModel), F.Id("True")), Comma, Sp,
            Declare(prediction, predictionType), Comma,
            RowBreak, Grp(),
            Assign(Apply(prediction, firstModel, target), predictionBody), Comma, Sp,
            Declare(preference, preferenceType), Comma,
            RowBreak, Grp(),
            Assign(Apply(preference, leftDoctrine, firstAction, secondAction), opposedPreference),
            Comma, RowBreak, Grp(),
            Assign(epistemic, epistemicBody), Comma, Sp,
            Assign(aleatoric, aleatoricBody), Comma,
            RowBreak, Grp(),
            Assign(modelUncertainty, modelBody), Comma,
            RowBreak, Grp(),
            Assign(normative, normativeBody), Comma,
            RowBreak, Grp(),
            Open, epistemic, Sp, Iff, Sp, enabled(0), Close, Sp, Land,
            RowBreak, Grp(),
            Open, aleatoric, Sp, Iff, Sp, enabled(1), Close, Sp, Land,
            RowBreak, Grp(),
            Open, modelUncertainty, Sp, Iff, Sp, enabled(2), Close, Sp, Land,
            RowBreak, Grp(),
            Open, normative, Sp, Iff, Sp, enabled(3), Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
