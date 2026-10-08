using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.BalancedThreshold;

internal sealed class BalancedThresholdRecurrenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform recurrence preserves the two palette phases.",
        H("Coloured recurrence"),
        Blocks(Describe.Lean(
            DescribeId.Create("balanced-threshold-coloured-recurrence"),
            DeclarationHandle.Create(
                "D5/S1/Words/BalancedThreshold/"
                + "BalancedThresholdRecurrence.coloured_word_uniformly_recurrent"),
            H("Bounded returns of every coloured factor"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Every zero-phase colouring of an irrational lower mechanical word "
                + "by the two-cycle and the interleaved cycles of sizes t and t+1 "
                + "is uniformly recurrent, for every positive t and real intercept. "
                + "An endpoint induction constructs a common right-stable floor interval. "
                + "Restricting physical starts to their original residue modulo "
                + "2t(t+1) turns the normalized phase into irrational rotation. "
                + "A finite compact cover bounds the return displacement. All endpoint "
                + "floors shift by the same multiple of 2t(t+1), so both occurrence-rank "
                + "phases, and hence every colour in the factor, return. This establishes "
                + "recurrence without using any unproved Sturmian-return supplier."))),
            DescribeRole.Theorem))));
}
