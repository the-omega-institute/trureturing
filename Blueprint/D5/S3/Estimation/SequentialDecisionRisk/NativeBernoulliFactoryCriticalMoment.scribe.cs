using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.SequentialDecisionRisk;

internal sealed class NativeBernoulliFactoryCriticalMomentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Estimation/SequentialDecisionRisk/NativeBernoulliFactoryCriticalMoment.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native uniform innovations and the critical Bernoulli-factory moment.",
        H("Native uniform innovations and the critical Bernoulli-factory moment"),
        Blocks(
            Paragraph(Text("Uniform [0,1] innovations are converted to Bernoulli answers in acquisition order. The resulting native execution preserves the source kernel, private-seed posterior and finite-leaf table law. Bernoulli-factory existence is classical (Keane--O'Brien and Nacu--Peres); the critical fractional-cost lower bound, exact native bookkeeping and its complete-output contract are repository-derived.")),
            Describe.Lean(
                DescribeId.Create("nativebernoullifactorycriticalmoment-native-source-trace-law"),
                DeclarationHandle.Create(Prefix + "native_source_trace_law"),
                H("A labelled native source trace has the product Bernoulli law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/williams1991martingales")),
                Blocks(Paragraph(Text("For every measurable policy, source request, finite labelled trace, and measurable seed event, the native uniform implementation has the seed-section mass times the product of the requested Bernoulli cell probabilities."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nativebernoullifactorycriticalmoment-native-source-conditional-kernel"),
                DeclarationHandle.Create(Prefix + "native_source_conditional_kernel"),
                H("The next native answer has the requested conditional kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/williams1991martingales")),
                Blocks(Paragraph(Text("Conditioned on any reached trace, source action and measurable private-seed event, the next uniform-to-Bernoulli answer factors with exactly the Bernoulli law for that source rate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nativebernoullifactorycriticalmoment-native-policy-table-leaf-law"),
                DeclarationHandle.Create(Prefix + "native_policy_table_leaf_law"),
                H("A private action table gives the exact finite-leaf law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/williams1991martingales")),
                Blocks(Paragraph(Text("For any action-probability table, the probability of a finite labelled trace followed by an action is the product of the table rows along the trace and the independent source likelihood."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nativebernoullifactorycriticalmoment-native-policy-table-identity"),
                DeclarationHandle.Create(Prefix + "native_policy_table_identity"),
                H("Identity rows preserve the first source answer"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/williams1991martingales")),
                Blocks(Paragraph(Text("If a table's supported root and return rows obey the identity-row conditions, almost every private seed starts with the requested source and every finite return retains that source's first native answer."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nativebernoullifactorycriticalmoment-factory-parameters"),
                DeclarationHandle.Create(Prefix + "FactoryParameters"),
                H("Legal two-source factory parameters"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/williams1991martingales")),
                Blocks(Paragraph(Text("FactoryParameters records B, C, kappa, gain g and positive noninteger beta together with their legal bounds."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nativebernoullifactorycriticalmoment-world"),
                DeclarationHandle.Create(Prefix + "World"),
                H("Legal worlds for fixed parameters"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/williams1991martingales")),
                Blocks(Paragraph(Text("A World chooses a two-branch index, a rate multiplier in its closed legal interval, and a positive h in the prescribed window."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nativebernoullifactorycriticalmoment-native-factory-logarithmic-total-call-cost"),
                DeclarationHandle.Create(Prefix + "native_factory_logarithmic_total_call_cost"),
                H("Native uniform execution pays the critical logarithmic cost"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/williams1991martingales")),
                Blocks(Paragraph(Text("For every legal parameter record and m above beta/2, complete-output total-variation accuracy at every legal world forces a positive logarithmic lower bound on the maximum expected fractional cost of the actual native source calls."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nativebernoullifactorycriticalmoment-real-policy-factory-logarithmic-total-call-cost"),
                DeclarationHandle.Create(Prefix + "real_policy_factory_logarithmic_total_call_cost"),
                H("Arbitrary real policy tables retain the native lower bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/williams1991martingales")),
                Blocks(Paragraph(Text("Every arbitrary real-probability table satisfies the exact native leaf, conditional-kernel, posterior, history-count and identity contracts; if it returns almost surely and is complete-output accurate, its actual total-call fractional cost is at least the same logarithmic lower bound."))),
                DescribeRole.Theorem))));
}
