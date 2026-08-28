using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Budget;

internal sealed class AdaptiveEarlyStoppingLimitsDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Budget/AdaptiveEarlyStoppingLimits.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adaptive early stopping lowers a concrete expected count while preserving the "
            + "adaptive worst-case information bound and the fixed answer alphabet.",
        H("Adaptive Early Stopping Limits"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("adaptive-worst-case-depth-information-lower-bound"),
                DeclarationHandle.Create(
                    Prefix + "adaptive_worst_case_depth_information_lower_bound"),
                H("Early stopping retains the adaptive worst-case lower bound"),
                StatementSource.FromAuthor(WorstCaseFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The imported adaptive protocol already permits a leaf under any remaining "
                        + "budget. Its logarithmic lower bound therefore applies directly for "
                        + "positive branching, while the totalized base-zero logarithm is zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("adaptive-worst-case-depth-lower-bound-is-tight"),
                DeclarationHandle.Create(
                    Prefix + "adaptive_worst_case_depth_lower_bound_is_tight"),
                H("Full transcript spaces attain the worst-case lower bound"),
                StatementSource.FromAuthor(TightFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For more than one possible answer, coordinate questions identify all "
                        + "B-valued transcripts of length h. The imported cardinality equality "
                        + "and the lower bound force the least adaptive depth to equal h."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "branching-gt-one-is-necessary-for-positive-depth-tightness"),
                DeclarationHandle.Create(
                    Prefix
                        + "branching_gt_one_is_necessary_for_positive_depth_tightness"),
                H("Nonunary branching is necessary for positive-depth tightness"),
                StatementSource.FromAuthor(TightnessNecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At B=1 and nominal depth one, the transcript state space is a singleton. "
                        + "A root leaf identifies it at depth zero, so equality with depth one "
                        + "is false."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("single-experiment-output-count-le"),
                DeclarationHandle.Create(Prefix + "single_experiment_output_count_le"),
                H("One experiment has at most B attained answers"),
                StatementSource.FromAuthor(OutputBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every adaptive query returns a value in Fin B by definition. The attained "
                        + "image is a subset of that fixed alphabet, so its cardinality is at "
                        + "most B independently of how later questions are selected."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("identity-experiment-attains-output-bound"),
                DeclarationHandle.Create(
                    Prefix + "identity_experiment_attains_output_bound"),
                H("The single-experiment output bound is attained"),
                StatementSource.FromAuthor(OutputTightFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The identity experiment on Fin B realizes every output. This also covers "
                        + "B=0, where both the state space and attained output set are empty."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("single-experiment-degenerate-audit"),
                DeclarationHandle.Create(Prefix + "single_experiment_degenerate_audit"),
                H("Empty and unary experiments have the expected output counts"),
                StatementSource.FromAuthor(OutputDegenerateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An experiment on Empty with an empty alphabet attains no answer. A constant "
                        + "unary experiment on Unit attains exactly its sole answer."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("protocol-degenerate-audit"),
                DeclarationHandle.Create(Prefix + "protocol_degenerate_audit"),
                H("Zero depth and constant-readout boundaries are explicit"),
                StatementSource.FromAuthor(ProtocolDegenerateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Imported named audits identify Empty and Unit at depth zero and rule out "
                        + "identifying Bool with a constant binary readout. Unary clog is zero."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("all-experiments-required-has-no-average-saving"),
                DeclarationHandle.Create(
                    Prefix + "all_experiments_required_has_no_average_saving"),
                H("Doing every experiment removes the average saving"),
                StatementSource.FromAuthor(NoSavingFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The imported three-model example has a point mass on a branch that cannot "
                        + "stop after the first question. Its adaptive count is exactly two, "
                        + "matching the static count."))),
                DescribeRole.Lemma))));

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

    private static Formula Card(Formula value) =>
        Call("card", value);

    private static Formula Outputs(Formula question) =>
        Call("singleExperimentOutputs", question);

    private static Formula AdaptiveDepth(Formula readout, Formula identifiable) =>
        Call("adaptiveIdentificationDepth", readout, identifiable);

    private static Formula TranscriptSpace(Formula branching, Formula depth) =>
        Call("TranscriptSpace", branching, depth);

    private static Formula WorstCaseFormula()
    {
        Formula question = F.Id("Question");
        Formula state = F.Id("X");
        Formula readout = F.Id("q");
        Formula branching = F.Id("B");
        Formula identifiable = F.Id("identifiable");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula readoutType = new Formula.TypeArrow(question,
            new Formula.TypeArrow(state, Call("Fin", branching)));
        Formula identifiableType = Seq(
            Exists, Sp, F.Id("depth"), Colon, Sp, naturals, Comma, Sp,
            Call("ExactAtDepth", readout, F.Id("depth")));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, question, Comma, Sp, state, Colon, Sp, type, Comma, Sp,
                OpenBracket, Call("Fintype", state), CloseBracket, Comma),
            Seq(Grp(), Forall, Sp, branching, Colon, Sp, naturals, Comma),
            Seq(Grp(), Forall, Sp, readout, Colon, Sp, readoutType, Comma),
            Seq(Grp(), Forall, Sp, identifiable, Colon, Sp, identifiableType, Comma),
            Seq(Grp(), Call("clog", branching, Card(state)), Sp, Leq, Sp,
                AdaptiveDepth(readout, identifiable), Dot),
        ]));
    }

    private static Formula TightFormula()
    {
        Formula branching = F.Id("B");
        Formula depth = F.Id("h");
        Formula state = TranscriptSpace(branching, depth);
        Formula readout = Call("coordinateReadout", branching, depth);
        return Disp(Seq(
            D(1), Sp, Lt, Sp, branching, Sp, Implies, Sp,
            AdaptiveDepth(state, readout), Sp, Eq, Sp, depth, Dot));
    }

    private static Formula TightnessNecessityFormula()
    {
        Formula state = TranscriptSpace(D(1), D(1));
        Formula readout = Call("coordinateReadout", D(1), D(1));
        Formula adaptiveDepth = AdaptiveDepth(state, readout);
        return Disp(Seq(
            adaptiveDepth, Sp, Eq, Sp, D(0), Sp, Land, Sp,
            adaptiveDepth, Sp, Neq, Sp, D(1), Dot));
    }

    private static Formula OutputBoundFormula()
    {
        return Disp(Seq(
            Card(Outputs(F.Id("q"))), Sp, Leq, Sp, F.Id("B"), Dot));
    }

    private static Formula OutputTightFormula()
    {
        Formula branching = F.Id("B");
        Formula identity = Call("identityOn", Call("Fin", branching));
        return Disp(Seq(
            Card(Outputs(identity)), Sp, Eq, Sp, branching, Dot));
    }

    private static Formula OutputDegenerateFormula()
    {
        return Disp(Seq(
            Card(Outputs(F.Id("emptyToFinZero"))), Sp, Eq, Sp, D(0), Sp, Land, Sp,
            Card(Outputs(F.Id("unitToFinOne"))), Sp, Eq, Sp, D(1), Dot));
    }

    private static Formula ProtocolDegenerateFormula()
    {
        Formula depth = F.Id("h");
        return Disp(Seq(
            Call("ExactAtDepth", F.Id("qEmpty"), D(0)), Sp, Land, Sp,
            Call("ExactAtDepth", F.Id("qUnit"), D(0)), Sp, Land, Sp,
            Call("clog", D(1), D(1)), Sp, Eq, Sp, D(0), Sp, Land, Sp,
            Forall, Sp, depth, Comma, Sp, Neg,
            Call("ExactAtDepth", Call("constantZero", D(2)), depth), Dot));
    }

    private static Formula NoSavingFormula()
    {
        Formula prior = Call("pure", F.Id("M0"));
        return Disp(Seq(
            Call("expectedExperimentCount", prior), Sp, Eq, Sp, D(2), Dot));
    }
}
