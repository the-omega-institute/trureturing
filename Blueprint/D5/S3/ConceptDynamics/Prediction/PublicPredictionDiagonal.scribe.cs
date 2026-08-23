using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Prediction;

internal sealed class PublicPredictionDiagonalDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Prediction/PublicPredictionDiagonal.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed-point-free public reactions defeat universal prediction, while a fixed point "
            + "supports a correct constant predictor.",
        H("Public Prediction Diagonal"),
        Blocks(
            Describe.Lean(
                DescribeId.Create(
                    "fixed-point-free-public-reactions-defeat-universal-prediction"),
                DeclarationHandle.Create(DeclarationPrefix + "no_correct_public_predictor"),
                H("Fixed-point-free public reactions defeat universal prediction"),
                StatementSource.FromAuthor(NoCorrectPublicPredictorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The actual action is obtained by feeding the public prediction into "
                            + "the subject's response. If a predictor were correct at every "
                            + "state, then at any state its predicted action would equal the "
                            + "response to that same action.")),
                    Paragraph(Text(
                        "A nonempty state space supplies such a state. The resulting action is "
                            + "a fixed point of the response, contradicting the assumption that "
                            + "the response has no fixed points. Hence no public predictor is "
                            + "universally correct."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("boolean-negation-defeats-every-public-predictor"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "bool_not_no_correct_public_predictor"),
                H("Boolean negation defeats every public predictor"),
                StatementSource.FromAuthor(BooleanNegationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On the one-state space, every public predictor announces one Boolean "
                        + "value. The response is its negation, which is always the opposite "
                        + "value and has no fixed point. Thus every predictor is wrong about "
                        + "the action produced after its announcement is read."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create(
                    "a-fixed-point-yields-a-correct-constant-public-predictor"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "exists_correct_public_predictor_of_fixed_point"),
                H("A fixed point yields a correct constant public predictor"),
                StatementSource.FromAuthor(FixedPointConverseFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If the response fixes an action, the predictor that announces that action "
                        + "at every state is universally correct. Reading the announcement and "
                        + "responding leaves the fixed action unchanged, showing that the "
                        + "fixed-point-free hypothesis in the obstruction is essential."))),
                DescribeRole.Lemma))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula Actual(
        Formula predictor, Formula response, Formula state) =>
        Call("actual", predictor, response, state);

    private static Formula NoCorrectPublicPredictorFormula()
    {
        Formula stateType = F.Id("State");
        Formula actionType = F.Id("Action");
        Formula predictor = F.Id("predict");
        Formula response = F.Id("react");
        Formula action = F.Id("action");
        Formula state = F.Id("state");

        Formula fixedPointFree = Seq(
            Forall, Sp, Typed(action, actionType), Comma, Sp,
            Apply(response, action), Sp, Neq, Sp, action);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(stateType, Comma, Sp, actionType), TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(predictor, Arrow(stateType, actionType)), Comma, Sp,
            Typed(response, Arrow(actionType, actionType)), Comma, RowBreak, Grp(),
            Open, fixedPointFree, Close, Sp, Land, Sp,
            Call("Nonempty", stateType), Sp, Rightarrow, Sp, RowBreak, Grp(),
            Neg, Sp, Forall, Sp, Typed(state, stateType), Comma, Sp,
            Apply(predictor, state), Sp, Eq, Sp,
            Actual(predictor, response, state), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula BooleanNegationFormula()
    {
        Formula unitType = F.Id("Unit");
        Formula boolType = F.Id("Bool");
        Formula predictor = F.Id("predict");
        Formula state = F.Id("state");
        Formula booleanNegation = Seq(boolType, Dot, F.Id("not"));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(predictor, Arrow(unitType, boolType)), Comma,
            RowBreak, Grp(),
            Neg, Sp, Forall, Sp, Typed(state, unitType), Comma, Sp,
            Apply(predictor, state), Sp, Eq, Sp,
            Actual(predictor, booleanNegation, state), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula FixedPointConverseFormula()
    {
        Formula stateType = F.Id("State");
        Formula actionType = F.Id("Action");
        Formula response = F.Id("react");
        Formula action = F.Id("action");
        Formula predictor = F.Id("predict");
        Formula state = F.Id("state");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(stateType, Comma, Sp, actionType), TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(response, Arrow(actionType, actionType)), Comma, Sp,
            Typed(action, actionType), Comma, RowBreak, Grp(),
            Apply(response, action), Sp, Eq, Sp, action, Sp, Rightarrow, Sp,
            RowBreak, Grp(),
            Exists, Sp, Typed(predictor, Arrow(stateType, actionType)), Comma,
            RowBreak, Grp(),
            Forall, Sp, Typed(state, stateType), Comma, Sp,
            Apply(predictor, state), Sp, Eq, Sp,
            Actual(predictor, response, state), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
