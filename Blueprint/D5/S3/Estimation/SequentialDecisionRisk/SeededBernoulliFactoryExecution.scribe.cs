using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.SequentialDecisionRisk;

internal sealed class SeededBernoulliFactoryExecutionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliFactoryExecution.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Seeded Bernoulli factory execution and total-call lower bounds.",
        H("Seeded Bernoulli factory execution and total-call lower bounds"),
        Blocks(
            Paragraph(Text("A policy sees a private seed, a requested source label, and the complete acquired history. Each source action appends one actually acquired Bernoulli answer; a return action emits the complete two-bit cell. The record charges every source answer, including both labels at a finite return, and assigns infinite cost to nonreturn. The classical Bernoulli-factory existence results of Keane--O'Brien and Nacu--Peres concern terminating simulation; the stopping/likelihood transfer used here is classical. The logarithmic total-call lower bound is a repository-derived consequence for this complete-output contract.")),
            Describe.Lean(
                DescribeId.Create("seededbernoullifactoryexecution-acquired-history"),
                DeclarationHandle.Create(Prefix + "acquiredHistory"),
                H("The acquired source history"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/williams1991martingales")),
                Blocks(Paragraph(Text("Given a policy, request, answer tape and finite time n, acquiredHistory recursively appends exactly the source answer produced by each source action and leaves a return action unchanged."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("seededbernoullifactoryexecution-action-singleton-measurable"),
                DeclarationHandle.Create(Prefix + "action_singleton_measurable"),
                H("Action cells have measurable singleton events"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/williams1991martingales")),
                Blocks(Paragraph(Text("Every source or return action has a measurable singleton in the discrete sum action space."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("seededbernoullifactoryexecution-calls-stopping"),
                DeclarationHandle.Create(Prefix + "calls_stopping"),
                H("The first return time is a stopping time"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/williams1991martingales")),
                Blocks(Paragraph(Text("For a measurable policy, the first time its action belongs to the return-cell range is a stopping time for the seeded filtration."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("seededbernoullifactoryexecution-output-stopped-measurable"),
                DeclarationHandle.Create(Prefix + "output_stopped_measurable"),
                H("The stopped output is measurable"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/williams1991martingales")),
                Blocks(Paragraph(Text("The cell returned at the first return time is measurable in the sigma algebra supplied by the stopping time."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("seededbernoullifactoryexecution-acquired-history-length-before-return"),
                DeclarationHandle.Create(Prefix + "acquired_history_length_before_return"),
                H("Every pre-return prefix contains one answer per step"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/williams1991martingales")),
                Blocks(Paragraph(Text("If n is no later than the first return, the acquired history at n has length n."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("seededbernoullifactoryexecution-acquired-history-length-at-return"),
                DeclarationHandle.Create(Prefix + "acquired_history_length_at_return"),
                H("A finite return charges all acquired answers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/williams1991martingales")),
                Blocks(Paragraph(Text("When the first return occurs at n, the acquired history has length n, so the two source labels in the returned cell are included in the charged record."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("seededbernoullifactoryexecution-cost-eq-record-cost"),
                DeclarationHandle.Create(Prefix + "cost_eq_record_cost"),
                H("The abstract cost equals the charged record cost"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/williams1991martingales")),
                Blocks(Paragraph(Text("The WithTop call cost agrees pointwise with the fractional power of the acquired record length, with infinite value exactly at nonreturn."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("seededbernoullifactoryexecution-target-mass"),
                DeclarationHandle.Create(Prefix + "target_mass"),
                H("The four-cell perturbation is normalized"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/williams1991martingales")),
                Blocks(Paragraph(Text("The four real cell masses consisting of the Bernoulli base row and signed diagonal perturbation sum to one for all real u, h and beta."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("seededbernoullifactoryexecution-seeded-policy-logarithmic-total-call-cost"),
                DeclarationHandle.Create(Prefix + "seeded_policy_logarithmic_total_call_cost"),
                H("Every accurate seeded policy pays logarithmic total-call cost"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/williams1991martingales")),
                Blocks(Paragraph(Text("For B equal to 2 or 4, C at least one, positive noninteger beta and any integer moment order m above beta/2, there are positive k and delta-zero such that every measurable parameter-independent seeded policy whose complete four-cell output is delta-close throughout the legal h-window has worst-world expected record cost at least k log(delta inverse). Infinite cost is retained for nonreturn."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("seededbernoullifactoryexecution-real-policy-table-logarithmic-total-call-cost"),
                DeclarationHandle.Create(Prefix + "real_policy_table_logarithmic_total_call_cost"),
                H("Independent action tables realize the same lower bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/williams1991martingales")),
                Blocks(Paragraph(Text("Every countable table of arbitrary real-probability action rows is realized by independent private coordinates. The row marginals are exact and the same complete-output logarithmic record-cost lower bound holds."))),
                DescribeRole.Theorem))));
}
