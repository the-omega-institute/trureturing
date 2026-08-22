using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Experiments;

internal sealed class ExperimentRefinementGainMonotoneDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Experiments/ExperimentRefinementGainMonotone.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Refining an experiment only enlarges its set of repaired target defects.",
        H("Experiment Refinement Gain Monotonicity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("target-defects-are-antitone-under-refinement"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "targetDefects_antitone_of_refines"),
                H("Target defects are antitone under refinement"),
                StatementSource.FromAuthor(TargetDefectsAntitoneFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If a finer readout gives the same value on two states, then the coarser "
                        + "readout does as well because it factors through the finer one. The "
                        + "states' distinct target values are unchanged, so every defect of "
                        + "the finer readout was already a defect of the coarser readout."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("joining-a-fixed-concept-preserves-experiment-refinement"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "conceptJoin_refines_of_right_refines"),
                H("A fixed concept preserves refinement on the experiment coordinate"),
                StatementSource.FromAuthor(ConceptJoinRefinementFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When one experiment readout factors through another, adjoining the same "
                        + "concept readout to both preserves that factorization. The induced "
                        + "factor map leaves the concept coordinate fixed and applies the "
                        + "experiment factor map to the second coordinate."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("experiment-refinement-gain-is-monotone"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "experiment_refinement_gain_monotone"),
                H("Experiment refinement can only enlarge gain"),
                StatementSource.FromAuthor(GainMonotonicityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Gain consists of target defects of the fixed concept that disappear "
                            + "after the experiment is joined to it. Refining the experiment "
                            + "shrinks the joined readout's remaining target-defect set.")),
                    Paragraph(Text(
                        "Subtracting that smaller remaining-defect set from the same base set "
                            + "can only add repaired pairs. Thus every defect repaired by the "
                            + "coarser experiment is also repaired by the finer experiment."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a-refined-experiment-does-not-reintroduce-a-defect"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "refined_experiment_does_not_reintroduce_defect"),
                H("A refined experiment does not reintroduce a repaired defect"),
                StatementSource.FromAuthor(NoReintroductionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Take a pair that is a target defect of the fixed concept but is separated "
                        + "after adjoining the coarser experiment. Gain monotonicity keeps that "
                        + "pair in the refined experiment's gain, so the finer joined readout "
                        + "cannot identify the pair again."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Readout(Formula index) =>
        new Formula.Subscript(F.Id("q"), index);

    private static Formula Prime(Formula value) => Seq(value, Apos);

    private static Formula Refines(Formula coarse, Formula fine) =>
        Call("Refines", coarse, fine);

    private static Formula Join(Formula concept, Formula experiment) =>
        Call("conceptJoin", concept, experiment);

    private static Formula TargetDefects(Formula readout, Formula target) =>
        Call("targetDefects", readout, target);

    private static Formula Gain(
        Formula concept,
        Formula experiment,
        Formula target) =>
        Call("experimentGain", concept, experiment, target);

    private static Formula Membership(Formula pair, Formula set) =>
        Seq(pair, Sp, InMacro, Sp, set);

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula TargetDefectsAntitoneFormula()
    {
        Formula stateType = F.Id("X");
        Formula coarseType = F.Id("D");
        Formula fineType = Prime(F.Id("D"));
        Formula targetType = F.Id("T");
        Formula coarse = Readout(coarseType);
        Formula fine = Readout(fineType);
        Formula target = F.Id("t");

        return Disp(Seq(
            Forall, Sp, stateType, Comma, Sp, coarseType, Comma, Sp,
            fineType, Comma, Sp, targetType, Colon, Sp, TypeUniverse(), Comma, RowBreak,
            Grp(), coarse, Colon, Sp, Arrow(stateType, coarseType), Comma, Sp,
            fine, Colon, Sp, Arrow(stateType, fineType), Comma, Sp,
            target, Colon, Sp, Arrow(stateType, targetType), Comma, RowBreak, Grp(),
            Refines(coarse, fine), Sp, Rightarrow, Sp,
            TargetDefects(fine, target), Sp, Subseteq, Sp,
            TargetDefects(coarse, target), Dot));
    }

    private static Formula ConceptJoinRefinementFormula()
    {
        Formula stateType = F.Id("X");
        Formula conceptType = F.Id("C");
        Formula coarseType = F.Id("E");
        Formula fineType = Prime(F.Id("E"));
        Formula concept = Readout(conceptType);
        Formula coarse = Readout(coarseType);
        Formula fine = Readout(fineType);

        return Disp(Seq(
            Forall, Sp, stateType, Comma, Sp, conceptType, Comma, Sp,
            coarseType, Comma, Sp, fineType, Colon, Sp, TypeUniverse(), Comma, RowBreak,
            Grp(), concept, Colon, Sp, Arrow(stateType, conceptType), Comma, Sp,
            coarse, Colon, Sp, Arrow(stateType, coarseType), Comma, Sp,
            fine, Colon, Sp, Arrow(stateType, fineType), Comma, RowBreak, Grp(),
            Refines(coarse, fine), Sp, Rightarrow, Sp,
            Refines(Join(concept, coarse), Join(concept, fine)), Dot));
    }

    private static Formula GainMonotonicityFormula()
    {
        var context = ExperimentContext.Create();

        return Disp(Seq(
            context.Quantification, RowBreak, Grp(),
            Refines(context.CoarseExperiment, context.FineExperiment), Sp,
            Rightarrow, Sp,
            Gain(context.Concept, context.CoarseExperiment, context.Target), Sp,
            Subseteq, Sp,
            Gain(context.Concept, context.FineExperiment, context.Target), Dot));
    }

    private static Formula NoReintroductionFormula()
    {
        var context = ExperimentContext.Create();
        Formula pair = F.Id("p");
        Formula baseDefect = Membership(
            pair,
            TargetDefects(context.Concept, context.Target));
        Formula removedByCoarse = Membership(
            pair,
            TargetDefects(
                Join(context.Concept, context.CoarseExperiment),
                context.Target));
        Formula removedByFine = Membership(
            pair,
            TargetDefects(
                Join(context.Concept, context.FineExperiment),
                context.Target));

        return Disp(Seq(
            context.Quantification,
            pair, Colon, Sp, context.PairType, Comma, RowBreak, Grp(),
            Refines(context.CoarseExperiment, context.FineExperiment), Sp,
            Land, Sp, baseDefect, Sp, Land, Sp,
            Neg, Sp, Grp(removedByCoarse), Sp, Rightarrow, RowBreak, Grp(),
            Neg, Sp, Grp(removedByFine), Dot));
    }

    private sealed record ExperimentContext(
        Formula Quantification,
        Formula Concept,
        Formula CoarseExperiment,
        Formula FineExperiment,
        Formula Target,
        Formula PairType)
    {
        public static ExperimentContext Create()
        {
            Formula stateType = F.Id("X");
            Formula conceptType = F.Id("C");
            Formula coarseType = F.Id("E");
            Formula fineType = Prime(F.Id("E"));
            Formula targetType = F.Id("T");
            Formula concept = Readout(conceptType);
            Formula coarse = Readout(coarseType);
            Formula fine = Readout(fineType);
            Formula target = F.Id("t");
            Formula pairType = Seq(stateType, Sp, Times, Sp, stateType);
            Formula quantification = Seq(
                Forall, Sp, stateType, Comma, Sp, conceptType, Comma, Sp,
                coarseType, Comma, Sp, fineType, Comma, Sp,
                targetType, Colon, Sp, TypeUniverse(), Comma, RowBreak, Grp(),
                concept, Colon, Sp, Arrow(stateType, conceptType), Comma, Sp,
                coarse, Colon, Sp, Arrow(stateType, coarseType), Comma, Sp,
                fine, Colon, Sp, Arrow(stateType, fineType), Comma, Sp,
                target, Colon, Sp, Arrow(stateType, targetType), Comma, RowBreak,
                Grp());

            return new ExperimentContext(
                quantification,
                concept,
                coarse,
                fine,
                target,
                pairType);
        }
    }
}
