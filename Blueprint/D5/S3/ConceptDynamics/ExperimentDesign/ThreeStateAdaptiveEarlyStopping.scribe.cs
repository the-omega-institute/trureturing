using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ExperimentDesign;

internal sealed class ThreeStateAdaptiveEarlyStoppingDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/ExperimentDesign/ThreeStateAdaptiveEarlyStopping."
            + "three_state_adaptive_early_stopping_strict_advantage";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A three-state early-stopping tree preserves exact identification and lowers "
            + "expected experiment cost.",
        H("Three-State Adaptive Early Stopping"),
        Blocks(Describe.Lean(
            DescribeId.Create("three-state-adaptive-early-stopping-strict-advantage"),
            DeclarationHandle.Create(Declaration),
            H("Adaptive early stopping has a strict expected-cost advantage"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The state encoding is a three-point option type. The distinguished "
                        + "none state has mass one minus twice epsilon, and each remaining "
                        + "state has mass epsilon.")),
                Paragraph(Text(
                    "The fixed transcript always reads both deterministic experiments. "
                        + "The adaptive transcript stops after the first answer exactly on "
                        + "the distinguished state.")),
                Paragraph(Text(
                    "Injectivity states zero-error identification. The length clauses give "
                        + "worst-case cost two, static mean two, and adaptive mean one plus "
                        + "twice epsilon."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula epsilon = F.Id("epsilon");
        Formula stateType = F.Id("X");
        Formula state = F.Id("x");
        Formula prior = F.Id("pi");
        Formula first = F.Id("A");
        Formula second = F.Id("B");
        Formula fixedTranscript = F.Id("S");
        Formula adaptiveTranscript = F.Id("T");
        Formula none = F.Id("none");
        Formula falseState = Call("some", F.Id("false"));
        Formula trueState = Call("some", F.Id("true"));

        Formula priorValid = new Formula.Logic(
            new Formula.Bind(
                FormulaQuantifier.ForAll,
                FormulaIdentifier.Create("x"),
                stateType,
                Seq(D(0), Sp, Leq, Sp, Call(prior, state))),
            FormulaLogicOperator.And,
            Equal(SumOver(state, stateType, Call(prior, state)), D(1)));

        Formula staticExact = Call("Injective", fixedTranscript);
        Formula adaptiveExact = Call("Injective", adaptiveTranscript);
        Formula worstCase = new Formula.Logic(
            new Formula.Bind(
                FormulaQuantifier.ForAll,
                FormulaIdentifier.Create("x"),
                stateType,
                Seq(Length(Call(adaptiveTranscript, state)), Sp, Leq, Sp, D(2))),
            FormulaLogicOperator.And,
            new Formula.Bind(
                FormulaQuantifier.Exists,
                FormulaIdentifier.Create("x"),
                stateType,
                Equal(Length(Call(adaptiveTranscript, state)), D(2))));

        Formula staticMean = ExpectedLength(prior, fixedTranscript, state, stateType);
        Formula adaptiveMean = ExpectedLength(prior, adaptiveTranscript, state, stateType);
        Formula conclusions = And(
            priorValid,
            staticExact,
            adaptiveExact,
            worstCase,
            Equal(staticMean, D(2)),
            Equal(adaptiveMean, Seq(D(1), Sp, Plus, Sp, D(2), epsilon)),
            Seq(adaptiveMean, Sp, Lt, Sp, staticMean));

        Formula hypotheses = And(
            Seq(D(0), Sp, Lt, Sp, epsilon),
            Seq(epsilon, Sp, Lt, Sp, Frac, Grp(D(1)), Grp(D(2))));

        Formula body = Seq(
            Begin, Grp(F.Id("gathered")),
            Operatorname, Grp(F.Id("let")), Sp,
            stateType, Sp, Colon, Eq, Sp, Call("Option", F.Id("Bool")), Comma,
            RowBreak, Grp(),
            Call(prior, none), Sp, Eq, Sp,
            D(1), Sp, Minus, Sp, D(2), epsilon, Comma, Sp,
            Call(prior, falseState), Sp, Eq, Sp,
            Call(prior, trueState), Sp, Eq, Sp, epsilon, Comma,
            RowBreak, Grp(),
            Call(first, none), Sp, Eq, Sp, F.Id("true"), Comma, Sp,
            Call(first, falseState), Sp, Eq, Sp,
            Call(first, trueState), Sp, Eq, Sp, F.Id("false"), Comma,
            RowBreak, Grp(),
            Call(second, trueState), Sp, Eq, Sp, F.Id("true"), Comma, Sp,
            Call(second, none), Sp, Eq, Sp,
            Call(second, falseState), Sp, Eq, Sp, F.Id("false"), Comma,
            RowBreak, Grp(),
            Call(fixedTranscript, state), Sp, Colon, Eq, Sp,
            OpenBracket, Call(first, state), Comma, Sp, Call(second, state), CloseBracket,
            Comma, RowBreak, Grp(),
            Call(adaptiveTranscript, state), Sp, Colon, Eq, Sp,
            Call("ite", Call(first, state),
                Seq(OpenBracket, F.Id("true"), CloseBracket),
                Seq(OpenBracket, F.Id("false"), Comma, Sp,
                    Call(second, state), CloseBracket)), Comma,
            RowBreak, Grp(),
            conclusions, Dot,
            End, Grp(F.Id("gathered")));

        return Disp(new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("epsilon"),
            F.Id("Real"),
            new Formula.Logic(hypotheses, FormulaLogicOperator.Implies, body)));
    }

    private static Formula ExpectedLength(
        Formula prior, Formula transcript, Formula state, Formula stateType) =>
        SumOver(
            state,
            stateType,
            Seq(Call(prior, state), Sp, Cdot, Sp,
                Length(Call(transcript, state))));

    private static Formula SumOver(
        Formula variable, Formula carrier, Formula summand) =>
        Seq(Sum, Underscore, Grp(variable, Sp, InMacro, Sp, carrier), Sp, summand);

    private static Formula Length(Formula value) =>
        Call("length", value);

    private static Formula And(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (int index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(clauses[index], FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Call(Formula name, params Formula[] arguments) =>
        new Formula.Apply(name, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        Call(F.Id(name), arguments);
}
