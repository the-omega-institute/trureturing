using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.ExperimentCost;

internal sealed class OutputStateRandomnessSeparationDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Boolean kernels separate randomness in state, interface, and prior.",
        H("Output and State Randomness Separation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("dirac-law-is-degenerate"),
                Handle("dirac_law_is_degenerate"),
                H("Every Dirac law is degenerate"),
                StatementSource.FromAuthor(DiracDegenerateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A point mass has singleton support, so it cannot support two distinct "
                        + "values. This fact audits both fixed priors and deterministic rows."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fixed-state-random-output"),
                Handle("fixed_state_random_output"),
                H("A fixed state can have random output"),
                StatementSource.FromAuthor(FixedStateRandomOutputFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The state law is the point mass at false, while every row of the "
                        + "interface kernel is the fair Boolean law. The induced output "
                        + "therefore remains nondegenerate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("random-state-deterministic-output"),
                Handle("random_state_deterministic_output"),
                H("A random state can have deterministic output"),
                StatementSource.FromAuthor(RandomStateDeterministicOutputFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A fair Boolean state law is sent by a constant Dirac kernel to false. "
                        + "Thus the state law is nondegenerate while the output law is a point "
                        + "mass."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("output-state-randomness-nonimplication"),
                Handle("output_state_randomness_nonimplication"),
                H("Output and state randomness imply neither direction"),
                StatementSource.FromAuthor(OutputStateNonimplicationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The preceding two Boolean witnesses refute both universal implications: "
                        + "random output need not come from a random state law, and a random "
                        + "state law need not survive in the output."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("single-source-models-isolate-uncertainties"),
                Handle("single_source_models_isolate_uncertainties"),
                H("Three models isolate the three uncertainty sources"),
                StatementSource.FromAuthor(SingleSourceModelsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "One model has only a random state transition, one has only measurement "
                        + "noise, and one has only a nondegenerate initial prior. All other "
                        + "rows in each model are explicit Dirac laws."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("single-source-models-observationally-equal"),
                Handle("single_source_models_observationally_equal"),
                H("The three isolated sources have one observable law"),
                StatementSource.FromAuthor(ObservationalEqualityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each single-source model induces the fair Boolean observation law. The "
                        + "same observable distribution therefore admits three distinct "
                        + "source placements in this finite construction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("uncertainty-sources-pairwise-do-not-imply"),
                Handle("uncertainty_sources_pairwise_do_not_imply"),
                H("The three uncertainty sources are pairwise nonimplicative"),
                StatementSource.FromAuthor(PairwiseNonimplicationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The three single-source witnesses refute all six directed implications "
                        + "between state-transition uncertainty, measurement noise, and prior "
                        + "uncertainty."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("empty-type-has-no-probability-law"),
                Handle("empty_type_has_no_probability_law"),
                H("The empty carrier has no probability law"),
                StatementSource.FromAuthor(EmptyLawFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A PMF on Empty would have total mass both zero and one. Hence an empty "
                        + "state carrier cannot supply the prior required by these models."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("singleton-state-can-still-have-random-output"),
                Handle("singleton_state_can_still_have_random_output"),
                H("A singleton state is fixed but its output can be random"),
                StatementSource.FromAuthor(SingletonStateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every PMF on PUnit is degenerate because no two states differ, yet a "
                        + "kernel row on that sole state can be the fair Boolean law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("deterministic-kernel-cannot-witness-random-output"),
                Handle("deterministic_kernel_cannot_witness_random_output"),
                H("A deterministic kernel row cannot be random"),
                StatementSource.FromAuthor(DeterministicKernelFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Evaluating a deterministic kernel at any fixed state gives a Dirac law. "
                        + "Consequently the fixed-state random-output witness requires a "
                        + "genuinely stochastic interface row."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-uncertainty-observation-is-deterministic"),
                Handle("zero_uncertainty_observation_is_deterministic"),
                H("Zero uncertainty gives a deterministic observation"),
                StatementSource.FromAuthor(ZeroUncertaintyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "With a Dirac prior and Dirac state and measurement kernels, binding the "
                        + "three stages yields the point mass at the composed deterministic "
                        + "output."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fpod-principle-202-1"),
                Handle("fpod_principle_202_1"),
                H("FPOD principle 202.1"),
                StatementSource.FromAuthor(FpodFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The bidirectional output-state separation, all six source "
                        + "nonimplications, the exact one-source audits, and their common "
                        + "observable law hold together in the explicit Boolean models."))),
                DescribeRole.Theorem))));

    private static DeclarationHandle Handle(string name) => DeclarationHandle.Create(
        "D5/S3/Estimation/ExperimentCost/OutputStateRandomnessSeparation." + name);

    private static Formula DiracDegenerateFormula()
    {
        Formula carrier = F.Id("A");
        Formula value = F.Id("a");
        return Disp(Seq(
            Forall, Sp, carrier, Comma, Sp, value, Colon, Sp, carrier, Comma, Sp,
            Neg, Nondegenerate(Pure(value)), Dot));
    }

    private static Formula FixedStateRandomOutputFormula() =>
        Disp(Seq(FixedStateRandomOutputBody(), Dot));

    private static Formula FixedStateRandomOutputBody()
    {
        Formula state = F.Id("x");
        Formula stateLaw = Mu;
        Formula kernel = F.Id("K");
        Formula boolean = F.Id("Bool");
        return Seq(
            Exists, Sp, state, Colon, Sp, boolean, Comma, Sp,
            stateLaw, Colon, Sp, Pmf(boolean), Comma, Sp,
            kernel, Colon, Sp, Kernel(boolean, boolean), Comma, RowBreak, Grp(),
            stateLaw, Sp, Eq, Sp, Pure(state), Sp, Land, Sp,
            Nondegenerate(Apply(kernel, state)), Sp, Land, Sp,
            Nondegenerate(OutputLaw(stateLaw, kernel)));
    }

    private static Formula RandomStateDeterministicOutputFormula() =>
        Disp(Seq(RandomStateDeterministicOutputBody(), Dot));

    private static Formula RandomStateDeterministicOutputBody()
    {
        Formula stateLaw = Mu;
        Formula kernel = F.Id("K");
        Formula output = F.Id("y");
        Formula state = F.Id("x");
        Formula boolean = F.Id("Bool");
        return Seq(
            Exists, Sp, stateLaw, Colon, Sp, Pmf(boolean), Comma, Sp,
            kernel, Colon, Sp, Kernel(boolean, boolean), Comma, Sp,
            output, Colon, Sp, boolean, Comma, RowBreak, Grp(),
            Nondegenerate(stateLaw), Sp, Land, Sp,
            Grp(Forall, Sp, state, Comma, Sp,
                Apply(kernel, state), Sp, Eq, Sp, Pure(output)), Sp, Land, Sp,
            OutputLaw(stateLaw, kernel), Sp, Eq, Sp, Pure(output));
    }

    private static Formula OutputStateNonimplicationFormula() =>
        Disp(Seq(OutputStateNonimplicationBody(), Dot));

    private static Formula OutputStateNonimplicationBody()
    {
        Formula stateLaw = Mu;
        Formula kernel = F.Id("K");
        Formula boolean = F.Id("Bool");
        Formula binders = Seq(
            Forall, Sp, stateLaw, Colon, Sp, Pmf(boolean), Comma, Sp,
            kernel, Colon, Sp, Kernel(boolean, boolean), Comma, Sp);
        return Seq(
            Neg, Grp(binders,
                Nondegenerate(OutputLaw(stateLaw, kernel)), Sp, Rightarrow, Sp,
                Nondegenerate(stateLaw)), Sp, Land, RowBreak, Grp(),
            Neg, Grp(binders,
                Nondegenerate(stateLaw), Sp, Rightarrow, Sp,
                Nondegenerate(OutputLaw(stateLaw, kernel))));
    }

    private static Formula SingleSourceModelsFormula() =>
        Disp(Seq(SingleSourceModelsBody(), Dot));

    private static Formula SingleSourceModelsBody()
    {
        Formula stateModel = new Formula.Subscript(F.Id("M"), F.Id("state"));
        Formula measurementModel =
            new Formula.Subscript(F.Id("M"), F.Id("measurement"));
        Formula priorModel = new Formula.Subscript(F.Id("M"), F.Id("prior"));
        return Seq(
            Grp(StateRandom(stateModel), Sp, Land, Sp,
                Neg, MeasurementRandom(stateModel), Sp, Land, Sp,
                Neg, PriorRandom(stateModel)), Sp, Land, RowBreak, Grp(),
            Grp(Neg, StateRandom(measurementModel), Sp, Land, Sp,
                MeasurementRandom(measurementModel), Sp, Land, Sp,
                Neg, PriorRandom(measurementModel)), Sp, Land, RowBreak, Grp(),
            Grp(Neg, StateRandom(priorModel), Sp, Land, Sp,
                Neg, MeasurementRandom(priorModel), Sp, Land, Sp,
                PriorRandom(priorModel)));
    }

    private static Formula ObservationalEqualityFormula() =>
        Disp(Seq(ObservationalEqualityBody(), Dot));

    private static Formula ObservationalEqualityBody()
    {
        Formula stateModel = new Formula.Subscript(F.Id("M"), F.Id("state"));
        Formula measurementModel =
            new Formula.Subscript(F.Id("M"), F.Id("measurement"));
        Formula priorModel = new Formula.Subscript(F.Id("M"), F.Id("prior"));
        Formula fair = Call("uniform", F.Id("Bool"));
        return Seq(
            Observable(stateModel), Sp, Eq, Sp, fair, Sp, Land, RowBreak, Grp(),
            Observable(measurementModel), Sp, Eq, Sp, fair, Sp, Land, RowBreak, Grp(),
            Observable(priorModel), Sp, Eq, Sp, fair);
    }

    private static Formula PairwiseNonimplicationFormula() =>
        Disp(Seq(PairwiseNonimplicationBody(), Dot));

    private static Formula PairwiseNonimplicationBody()
    {
        Formula state = F.Id("StateUncertainty");
        Formula measurement = F.Id("MeasurementNoise");
        Formula prior = F.Id("PriorUncertainty");
        return Seq(
            DoesNotImply(state, measurement), Sp, Land, Sp,
            DoesNotImply(measurement, state), Sp, Land, RowBreak, Grp(),
            DoesNotImply(state, prior), Sp, Land, Sp,
            DoesNotImply(prior, state), Sp, Land, RowBreak, Grp(),
            DoesNotImply(measurement, prior), Sp, Land, Sp,
            DoesNotImply(prior, measurement));
    }

    private static Formula EmptyLawFormula() =>
        Disp(Seq(Neg, Call("Nonempty", Pmf(F.Id("Empty"))), Dot));

    private static Formula SingletonStateFormula()
    {
        Formula stateLaw = Mu;
        Formula kernel = F.Id("K");
        Formula unit = F.Id("unit");
        Formula punit = F.Id("PUnit");
        Formula boolean = F.Id("Bool");
        return Disp(Seq(
            Grp(Forall, Sp, stateLaw, Colon, Sp, Pmf(punit), Comma, Sp,
                Neg, Nondegenerate(stateLaw)), Sp, Land, RowBreak, Grp(),
            Exists, Sp, kernel, Colon, Sp, Kernel(punit, boolean), Comma, Sp,
            Nondegenerate(Apply(kernel, unit)), Dot));
    }

    private static Formula DeterministicKernelFormula()
    {
        Formula source = F.Id("X");
        Formula target = F.Id("Y");
        Formula state = F.Id("x");
        Formula readout = F.Id("f");
        return Disp(Seq(
            Forall, Sp, source, Comma, Sp, target, Comma, Sp,
            state, Colon, Sp, source, Comma, Sp,
            readout, Colon, Sp, source, Sp, To, Sp, target, Comma, RowBreak, Grp(),
            Neg, Nondegenerate(Pure(Apply(readout, state))), Dot));
    }

    private static Formula ZeroUncertaintyFormula()
    {
        Formula initial = F.Id("i");
        Formula transition = F.Id("f");
        Formula measurement = F.Id("g");
        Formula boolean = F.Id("Bool");
        Formula function = Seq(boolean, Sp, To, Sp, boolean);
        Formula model = Call("deterministicModel", initial, transition, measurement);
        return Disp(Seq(
            Forall, Sp, initial, Colon, Sp, boolean, Comma, Sp,
            transition, Colon, Sp, function, Comma, Sp,
            measurement, Colon, Sp, function, Comma, RowBreak, Grp(),
            Observable(model), Sp, Eq, Sp,
            Pure(Apply(measurement, Apply(transition, initial))), Dot));
    }

    private static Formula FpodFormula() => Disp(Seq(
        OutputStateNonimplicationBody(), Sp, Land, RowBreak, Grp(),
        SingleSourceModelsBody(), Sp, Land, RowBreak, Grp(),
        PairwiseNonimplicationBody(), Sp, Land, RowBreak, Grp(),
        ObservationalEqualityBody(), Dot));

    private static Formula DoesNotImply(Formula source, Formula target)
    {
        Formula model = F.Id("M");
        return Seq(
            Neg, Grp(Forall, Sp, model, Comma, Sp,
                Apply(source, model), Sp, Rightarrow, Sp, Apply(target, model)));
    }

    private static Formula Pmf(Formula carrier) => Call("PMF", carrier);

    private static Formula Kernel(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, Pmf(target));

    private static Formula Pure(Formula value) => Call("pure", value);

    private static Formula Nondegenerate(Formula law) =>
        Call("NondegenerateLaw", law);

    private static Formula OutputLaw(Formula stateLaw, Formula kernel) =>
        Call("inducedOutputLaw", stateLaw, kernel);

    private static Formula StateRandom(Formula model) =>
        Call("StateUncertainty", model);

    private static Formula MeasurementRandom(Formula model) =>
        Call("MeasurementNoise", model);

    private static Formula PriorRandom(Formula model) =>
        Call("PriorUncertainty", model);

    private static Formula Observable(Formula model) =>
        Call("observableLaw", model);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);
}
