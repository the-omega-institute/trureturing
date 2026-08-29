using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.ExperimentCost;

internal sealed class StaticAdaptiveSubmodularitySeparationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Estimation/ExperimentCost/StaticAdaptiveSubmodularitySeparation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rare posterior branch separates expected from pathwise diminishing returns.",
        H("Static and Adaptive Submodularity Separation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("adaptive-implies-static"),
                Handle("adaptive_submodular_implies_static_submodular"),
                H("Adaptive submodularity implies static submodularity"),
                StatementSource.FromAuthor(AdaptiveImpliesStaticFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A positive-mass pathwise bound can be multiplied by its mass and summed. "
                        + "Zero-mass outputs contribute zero, and normalization gives the "
                        + "static expected bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rare-prior-and-gate-normalized"),
                Handle("rare_prior_and_gate_are_normalized"),
                H("The prior and gate law are normalized"),
                StatementSource.FromAuthor(NormalizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The common state has mass 9/10 and the two rare states each have mass "
                        + "1/20. The gate's rare output therefore has total mass 1/10."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rare-output-activates-specialist"),
                Handle("rare_output_posterior_activates_specialist"),
                H("A rare output activates the specialist"),
                StatementSource.FromAuthor(PosteriorActivationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Conditioning on the rare gate output removes the common state. The two "
                        + "remaining states become equiprobable, so specialist value rises "
                        + "from 1/20 to 1/2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rare-branch-static-submodular"),
                Handle("rare_branch_static_submodular"),
                H("The rare-branch instance is statically submodular"),
                StatementSource.FromAuthor(StaticWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The specialist has gain zero on the common output and gain 1/2 on the "
                        + "rare output. Its expected posterior gain is exactly 1/20, equal to "
                        + "its prior gain."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rare-branch-not-adaptive-submodular"),
                Handle("rare_branch_not_adaptive_submodular"),
                H("The rare-branch instance is not adaptively submodular"),
                StatementSource.FromAuthor(NotAdaptiveFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The rare output has positive probability, yet its realized specialist "
                        + "gain 1/2 exceeds the prior gain 1/20. This violates the pathwise "
                        + "bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fpod-principle-246-1"),
                Handle("fpod_principle_246_1"),
                H("FPOD principle 246.1"),
                StatementSource.FromAuthor(FpodFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The same finite instance satisfies expected diminishing returns and "
                        + "fails pathwise diminishing returns. Static submodularity therefore "
                        + "does not imply adaptive submodularity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("empty-experiment-family-satisfies-both"),
                Handle("empty_experiment_family_satisfies_both"),
                H("An empty experiment family satisfies both properties"),
                StatementSource.FromAuthor(EmptyFamilyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "With no next experiment, both marginal-return conditions are vacuous. "
                        + "Only normalization of the gate-output law remains."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("singleton-experiment-family-satisfies-both"),
                Handle("singleton_experiment_family_satisfies_both"),
                H("An unavailable singleton family satisfies both properties"),
                StatementSource.FromAuthor(SingletonFamilyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A singleton experiment family whose sole member is unavailable has no "
                        + "next-step obligation, so both conditions again hold vacuously."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("constant-gain-satisfies-both"),
                Handle("constant_gain_satisfies_both"),
                H("Constant zero gain satisfies both properties"),
                StatementSource.FromAuthor(ConstantGainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When every prior and posterior marginal gain is zero, all expected and "
                        + "pathwise comparisons reduce to equality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("posterior-not-updating-satisfies-both"),
                Handle("posterior_not_updating_satisfies_both"),
                H("Posterior-independent gain satisfies both properties"),
                StatementSource.FromAuthor(NoUpdateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If every posterior marginal equals its prior marginal, conditioning "
                        + "cannot create a pathwise increase and both notions reduce to "
                        + "equality."))),
                DescribeRole.Theorem))));

    private static DeclarationHandle Handle(string name) =>
        DeclarationHandle.Create(Prefix + name);

    private static Formula Static(
        Formula mass,
        Formula available,
        Formula priorGain,
        Formula pathGain) =>
        Call("StaticSubmodular", mass, available, priorGain, pathGain);

    private static Formula Adaptive(
        Formula mass,
        Formula available,
        Formula priorGain,
        Formula pathGain) =>
        Call("AdaptiveSubmodular", mass, available, priorGain, pathGain);

    private static Formula WitnessStatic() =>
        Static(
            F.Id("rareGateOutcomeMass"),
            F.Id("availableAfterGate"),
            F.Id("rarePriorMarginalGain"),
            F.Id("rarePathMarginalGain"));

    private static Formula WitnessAdaptive() =>
        Adaptive(
            F.Id("rareGateOutcomeMass"),
            F.Id("availableAfterGate"),
            F.Id("rarePriorMarginalGain"),
            F.Id("rarePathMarginalGain"));

    private static Formula AdaptiveImpliesStaticFormula()
    {
        Formula mass = F.Id("mu");
        Formula available = F.Id("A");
        Formula priorGain = F.Id("gPrior");
        Formula pathGain = F.Id("gPath");
        return Disp(Seq(
            Forall, Sp, mass, Comma, Sp, available, Comma, Sp,
            priorGain, Comma, Sp, pathGain, Comma, RowBreak, Grp(),
            Adaptive(mass, available, priorGain, pathGain),
            Sp, Rightarrow, Sp,
            Static(mass, available, priorGain, pathGain), Dot));
    }

    private static Formula NormalizationFormula() =>
        Disp(Seq(
            Call("ProbabilityMass", F.Id("rarePriorMass")), Sp, Land, RowBreak, Grp(),
            Call("ProbabilityMass", F.Id("rareGateOutcomeMass")), Sp, Land, RowBreak, Grp(),
            Call("rareGateOutcomeMass", F.Id("false")), Sp, Eq, Sp,
            Frac, Grp(D(1)), Grp(D(1, 0)), Dot));

    private static Formula PosteriorActivationFormula() =>
        Disp(Seq(
            Call("posteriorAfterReadout", F.Id("gateExperiment"), F.Id("false"),
                F.Id("none")),
            Sp, Eq, Sp, D(0), Sp, Land, RowBreak, Grp(),
            Call("posteriorAfterReadout", F.Id("gateExperiment"), F.Id("false"),
                Call("some", F.Id("false"))),
            Sp, Eq, Sp, Frac, Grp(D(1)), Grp(D(2)), Sp, Land, RowBreak, Grp(),
            Call("posteriorAfterReadout", F.Id("gateExperiment"), F.Id("false"),
                Call("some", F.Id("true"))),
            Sp, Eq, Sp, Frac, Grp(D(1)), Grp(D(2)), Sp, Land, RowBreak, Grp(),
            Call("rarePriorMarginalGain", F.Id("specialistExperiment")),
            Sp, Eq, Sp, Frac, Grp(D(1)), Grp(D(2, 0)), Sp, Land, RowBreak, Grp(),
            Call("rarePathMarginalGain", F.Id("false"),
                F.Id("specialistExperiment")),
            Sp, Eq, Sp, Frac, Grp(D(1)), Grp(D(2)), Dot));

    private static Formula StaticWitnessFormula() =>
        Disp(Seq(WitnessStatic(), Dot));

    private static Formula NotAdaptiveFormula() =>
        Disp(Seq(Neg, WitnessAdaptive(), Dot));

    private static Formula FpodFormula() =>
        Disp(Seq(Neg, Grp(
            WitnessStatic(), Sp, Rightarrow, Sp, WitnessAdaptive()), Dot));

    private static Formula EmptyFamilyFormula()
    {
        Formula mass = F.Id("rareGateOutcomeMass");
        Formula unavailable = Call("unavailable", F.Id("Empty"));
        Formula priorGain = F.Id("emptyPriorGain");
        Formula pathGain = F.Id("emptyPathGain");
        return Disp(Seq(
            Static(mass, unavailable, priorGain, pathGain), Sp, Land, RowBreak, Grp(),
            Adaptive(mass, unavailable, priorGain, pathGain), Dot));
    }

    private static Formula SingletonFamilyFormula()
    {
        Formula mass = F.Id("rareGateOutcomeMass");
        Formula unavailable = Call("unavailable", F.Id("Unit"));
        Formula zeroGain = F.Id("zeroGain");
        return Disp(Seq(
            Static(mass, unavailable, zeroGain, zeroGain), Sp, Land, RowBreak, Grp(),
            Adaptive(mass, unavailable, zeroGain, zeroGain), Dot));
    }

    private static Formula ConstantGainFormula()
    {
        Formula mass = F.Id("rareGateOutcomeMass");
        Formula all = F.Id("allExperiments");
        Formula zeroGain = F.Id("zeroGain");
        return Disp(Seq(
            Static(mass, all, zeroGain, zeroGain), Sp, Land, RowBreak, Grp(),
            Adaptive(mass, all, zeroGain, zeroGain), Dot));
    }

    private static Formula NoUpdateFormula()
    {
        Formula mass = F.Id("rareGateOutcomeMass");
        Formula available = F.Id("availableAfterGate");
        Formula gain = F.Id("rarePriorMarginalGain");
        Formula unchanged = Call("posteriorIndependent", gain);
        return Disp(Seq(
            Static(mass, available, gain, unchanged), Sp, Land, RowBreak, Grp(),
            Adaptive(mass, available, gain, unchanged), Dot));
    }
}
