using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Forgetting;

internal sealed class DeterministicOutputEntropyRateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite deterministic output process has no conditional entropy injection and zero normalized output-entropy rate.",
        H("Deterministic Output Entropy Rate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-deterministic-output-entropy-has-a-fixed-budget"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Forgetting/DeterministicOutputEntropyRate."
                        + "deterministic_output_entropy_budget_and_rate"),
                H("Deterministic output blocks have a fixed entropy budget and zero rate"),
                StatementSource.FromAuthor(EntropyBudgetFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a normalized nonnegative mass on a finite state carrier choose the "
                            + "initial state of a deterministic update and readout. The block "
                            + "outputBlock contains the readouts at every time from zero through "
                            + "the chosen horizon and is constructed directly by function "
                            + "iteration.")),
                    Paragraph(Text(
                        "For every horizon, the graph law of the initial state and its output "
                            + "block has zero conditional entropy. Deterministic pushforward cannot "
                            + "increase Shannon entropy, and the initial entropy is bounded by the "
                            + "logarithm of the state-cardinality. The bounded numerator divided by "
                            + "the growing block length therefore tends to zero.")),
                    Paragraph(Text(
                        "A second normalized law may jointly sample a finite configuration and "
                            + "initial state. The configured block keeps that sampled configuration "
                            + "fixed at every time. Its graph conditional entropy is zero and its "
                            + "output entropy is bounded by the joint configuration-state entropy. "
                            + "All entropy values and logarithms use the repository's canonical "
                            + "natural-logarithm convention."))),
                DescribeRole.Theorem))));

    private static Formula Typed(Formula name, Formula type) => Seq(name, Colon, Sp, type);

    private static Formula At(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Law(Formula mass, Formula variable) => Seq(
        Open, Forall, Sp, variable, Comma, Sp, D(0), Sp, Leq, Sp, At(mass, variable), Close,
        Sp, Land, Sp, Sum, Underscore, Grp(variable), At(mass, variable), Sp, Eq, Sp, D(1));

    private static Formula Block(
        Formula update, Formula readout, Formula horizon, Formula initial) =>
        Call("outputBlock", update, readout, horizon, initial);

    private static Formula ConfiguredBlock(
        Formula update, Formula readout, Formula horizon, Formula initial) =>
        Call("configuredOutputBlock", update, readout, horizon, initial);

    private static Formula Pushforward(Formula map, Formula mass) =>
        Call("pushforward", map, mass);

    private static Formula Entropy(Formula mass) => Call("shannonEntropy", mass);

    private static Formula ConditionalEntropy(Formula mass) =>
        Call("conditionalEntropy", mass);

    private static Formula EntropyBudgetFormula()
    {
        Formula stateType = F.Id("Y");
        Formula outputType = F.Id("O");
        Formula configurationType = F.Id("Theta");
        Formula update = F.Id("F");
        Formula readout = F.Id("q");
        Formula initialMass = F.Id("p");
        Formula configuredUpdate = F.Id("G");
        Formula configuredReadout = F.Id("r");
        Formula configuredMass = F.Id("w");
        Formula state = F.Id("y");
        Formula configuredState = F.Id("z");
        Formula horizon = F.Id("T");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula stateOutput = Block(update, readout, horizon, state);
        Formula outputMap = Seq(state, Mapsto, Sp, stateOutput);
        Formula graphMap = Seq(state, Mapsto, Sp, Open,
            state, Comma, Sp, stateOutput, Close);
        Formula configuredOutput = ConfiguredBlock(
            configuredUpdate, configuredReadout, horizon, configuredState);
        Formula configuredOutputMap = Seq(configuredState, Mapsto, Sp, configuredOutput);
        Formula configuredGraphMap = Seq(configuredState, Mapsto, Sp, Open,
            configuredState, Comma, Sp, configuredOutput, Close);
        Formula outputLaw = Pushforward(outputMap, initialMass);
        Formula configuredOutputLaw = Pushforward(configuredOutputMap, configuredMass);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(stateType, type), Comma, Sp,
            Typed(outputType, type), Comma, Sp,
            Typed(configurationType, type), Comma, RowBreak, Grp(),
            OpenBracket, Call("Fintype", stateType), CloseBracket, Comma, Sp,
            OpenBracket, Call("Fintype", outputType), CloseBracket, Comma, Sp,
            OpenBracket, Call("Fintype", configurationType), CloseBracket, Comma, RowBreak, Grp(),
            Typed(update, new Formula.TypeArrow(stateType, stateType)), Comma, Sp,
            Typed(readout, new Formula.TypeArrow(stateType, outputType)), Comma, Sp,
            Typed(initialMass, new Formula.TypeArrow(stateType, real)), Comma, RowBreak, Grp(),
            Typed(configuredUpdate, new Formula.TypeArrow(configurationType,
                new Formula.TypeArrow(stateType, stateType))), Comma, Sp,
            Typed(configuredReadout, new Formula.TypeArrow(configurationType,
                new Formula.TypeArrow(stateType, outputType))), Comma, RowBreak, Grp(),
            Typed(configuredMass, new Formula.TypeArrow(
                Seq(configurationType, Times, Sp, stateType), real)), Comma, RowBreak, Grp(),
            Open, Law(initialMass, state), Close, Sp, Land, Sp,
            Open, Law(configuredMass, configuredState), Close, Sp, Rightarrow, RowBreak, Grp(),
            Open,
                Forall, Sp, horizon, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                ConditionalEntropy(Pushforward(graphMap, initialMass)), Sp, Eq, Sp, D(0),
            Close, Sp, Land, RowBreak, Grp(),
            Open,
                Forall, Sp, horizon, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                Entropy(outputLaw), Sp, Leq, Sp, Entropy(initialMass), Sp, Leq, Sp,
                Log, Open, Lvert, Sp, stateType, Sp, Rvert, Close,
            Close, Sp, Land, RowBreak, Grp(),
            Lim, Underscore, Grp(horizon, Sp, To, Sp, Infty), Sp,
                Frac, Grp(Entropy(outputLaw)), Grp(horizon, Plus, D(1)),
                Sp, Eq, Sp, D(0), Sp, Land, RowBreak, Grp(),
            Open,
                Forall, Sp, horizon, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                ConditionalEntropy(Pushforward(configuredGraphMap, configuredMass)),
                    Sp, Eq, Sp, D(0),
            Close, Sp, Land, RowBreak, Grp(),
            Open,
                Forall, Sp, horizon, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                Entropy(configuredOutputLaw), Sp, Leq, Sp, Entropy(configuredMass),
            Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
