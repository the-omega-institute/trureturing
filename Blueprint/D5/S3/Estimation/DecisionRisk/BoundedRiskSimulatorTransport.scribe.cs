using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DecisionRisk;

internal sealed class BoundedRiskSimulatorTransportDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Estimation/DecisionRisk/BoundedRiskSimulatorTransport."
            + "bounded_loss_risk_stability_of_simulator";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform simulation error bounds the statewise risk increase of every bounded-loss rule.",
        H("Bounded-Risk Simulator Transport"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bounded-risk-simulator-transport"),
                DeclarationHandle.Create(Declaration),
                H("A total-variation simulator transports every bounded-loss decision rule"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The state, observation, simulated-observation, and action carriers are "
                            + "finite, with a nonempty state carrier. K and L are experiments, M "
                            + "is the simulator, and d is an arbitrary randomized decision rule "
                            + "based on L; all four are row-stochastic.")),
                    Paragraph(Text(
                        "The transported rule is the canonical composition: after observing K, "
                            + "apply M and then d. Its row-stochasticity is part of the public "
                            + "conclusion, so the transported object is exposed rather than hidden "
                            + "behind an existence claim.")),
                    Paragraph(Text(
                        "For every loss taking values between zero and one, the finite supremum "
                            + "of the rowwise total-variation simulation error bounds the increase "
                            + "of expected loss separately at every state."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("row-stochastic-channel-composition"),
                DeclarationHandle.Create("D5/S3/Estimation/DecisionRisk/BoundedRiskSimulatorTransport.row_stochastic_channel_comp"),
                H("Composition preserves stochastic rows"),
                StatementSource.FromAuthor(CompositionFormula(true)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary input types and finite intermediate and output types, composing two nonnegative unit-row matrices gives another nonnegative unit-row matrix. The inner row sum reduces the composite row sum to the first matrix's row sum."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("channel-output-associativity"),
                DeclarationHandle.Create("D5/S3/Estimation/DecisionRisk/BoundedRiskSimulatorTransport.channel_output_comp"),
                H("Finite channel output is associative"),
                StatementSource.FromAuthor(CompositionFormula(false)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For finite input and intermediate types and an arbitrary output type, applying a composite real matrix to a real mass agrees with two successive channel outputs. This is a finite distributive identity and requires no positivity or normalization."))),
                DescribeRole.Lemma))));

    private static Formula CompositionFormula(bool stochastic)
    {
        Formula first = F.Id("K"), second = F.Id("D"), mass = F.Id("p");
        Formula i = F.Id("i"), o = F.Id("o");
        Formula composite = Seq(Open, i, Comma, Sp, o, Sp, Mapsto, Sp,
            Apply(Call("channelOutput", second, Apply(first, i)), o), Close);
        Formula body = stochastic
            ? Seq(Call("IsRowStochastic", first), Sp, Land, Sp,
                Call("IsRowStochastic", second), Sp, Rightarrow, Sp,
                Call("IsRowStochastic", composite))
            : Seq(Call("channelOutput", composite, mass), Sp, Eq, Sp,
                Call("channelOutput", second, Call("channelOutput", first, mass)));
        return Disp(Seq(Forall, Sp, first, Comma, Sp, second, Comma, Sp,
            stochastic ? Grp() : Seq(mass, Comma, Sp), body));
    }

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

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("X");
        Formula observationType = F.Id("O");
        Formula simulatedType = F.Id("R");
        Formula actionType = F.Id("A");
        Formula state = F.Id("x");
        Formula observation = F.Id("o");
        Formula simulated = F.Id("r");
        Formula action = F.Id("a");
        Formula experiment = F.Id("K");
        Formula simulatedExperiment = F.Id("L");
        Formula simulator = F.Id("M");
        Formula decision = F.Id("d");
        Formula loss = F.Id("ell");
        Formula epsilon = F.Id("epsilon");
        Formula transported = F.Id("dK");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula Row(Formula kernel, Formula source) => Apply(kernel, source);
        Formula Output(Formula kernel, Formula mass, Formula output) =>
            Apply(Call("channelOutput", kernel, mass), output);
        Formula transportedDefinition = Seq(
            Apply(Apply(transported, observation), action), Sp, Colon, Eq, Sp,
            Output(decision, Row(simulator, observation), action));
        Formula boundedLoss = Seq(
            Forall, Sp, state, Colon, Sp, stateType, Comma, Sp,
            action, Colon, Sp, actionType, Comma, Sp,
            D(0), Sp, Leq, Sp, Apply(loss, state, action), Sp, Land, Sp,
            Apply(loss, state, action), Sp, Leq, Sp, D(1));
        Formula simulatedRow =
            Call("channelOutput", simulator, Row(experiment, state));
        Formula uniformError = Seq(
            Call("sup", state,
                Call("TV", Row(simulatedExperiment, state), simulatedRow)),
            Sp, Leq, Sp, epsilon);
        Formula Risk(Formula rule, Formula sourceLaw) =>
            Call("sum", action,
                Seq(Output(rule, sourceLaw, action), Sp, Cdot, Sp,
                    Apply(loss, state, action)));
        Formula transportedRisk = Risk(transported, Row(experiment, state));
        Formula originalRisk = Risk(decision, Row(simulatedExperiment, state));
        Formula hypotheses = Seq(
            Call("IsRowStochastic", experiment), Sp, Land, Sp,
            Call("IsRowStochastic", simulatedExperiment), Sp, Land, Sp,
            Call("IsRowStochastic", simulator), Sp, Land, Sp,
            Call("IsRowStochastic", decision), Sp, Land, RowBreak, Grp(),
            Open, boundedLoss, Close, Sp, Land, Sp, uniformError);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, stateType, Comma, Sp, observationType, Comma, Sp,
            simulatedType, Comma, Sp, actionType, Comma, RowBreak, Grp(),
            Call("Fintype", stateType), Comma, Sp,
            Call("Nonempty", stateType), Comma, Sp,
            Call("Fintype", observationType), Comma, RowBreak, Grp(),
            Call("Fintype", simulatedType), Comma, Sp,
            Call("Fintype", actionType), Comma, RowBreak, Grp(),
            experiment, Colon, Sp, stateType, Sp, To, Sp,
            observationType, Sp, To, Sp, real, Comma, Sp,
            simulatedExperiment, Colon, Sp, stateType, Sp, To, Sp,
            simulatedType, Sp, To, Sp, real, Comma, RowBreak, Grp(),
            simulator, Colon, Sp, observationType, Sp, To, Sp,
            simulatedType, Sp, To, Sp, real, Comma, Sp,
            decision, Colon, Sp, simulatedType, Sp, To, Sp,
            actionType, Sp, To, Sp, real, Comma, RowBreak, Grp(),
            loss, Colon, Sp, stateType, Sp, To, Sp,
            actionType, Sp, To, Sp, real, Comma, Sp,
            epsilon, Colon, Sp, real, Comma, RowBreak, Grp(),
            Open, hypotheses, Close, Sp, Rightarrow, RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Open,
            transportedDefinition, Close, SemiSpace, RowBreak, Grp(),
            Call("IsRowStochastic", transported), Sp, Land, RowBreak, Grp(),
            Forall, Sp, state, Colon, Sp, stateType, Comma, Sp,
            transportedRisk, Sp, Leq, Sp,
            originalRisk, Sp, Plus, Sp, epsilon, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
