using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.BalancedThreshold;

internal sealed class BalancedThresholdStripDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct physical bispecial returns bound every occurrence discrepancy strictly.",
        H("Strict bispecial displacement strip"),
        Blocks(Describe.Lean(
            DescribeId.Create("balanced-threshold-mechanical-bispecial-strip"),
            DeclarationHandle.Create(
                "D5/S1/Words/BalancedThreshold/"
                + "BalancedThresholdStrip.mechanical_bispecial_strip"),
            H("The sum of two return discrepancies"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For every irrational frequency in (0,1), every characteristic "
                + "mechanical bispecial factor, every ordered occurrence pair "
                + "and any two distinct actual adjacent return blocks, the "
                + "physical displacement discrepancy is strictly smaller than "
                + "the sum of those returns' absolute discrepancies. The empty "
                + "factor is included. Strong length induction transfers "
                + "adjacency through bispecial descent and scales all errors "
                + "by the same positive factor; irrational complementation "
                + "negates the discrepancies. Convergent indexing and the "
                + "particular derived-slope identification are separate obligations."))),
            DescribeRole.Theorem))));
}
