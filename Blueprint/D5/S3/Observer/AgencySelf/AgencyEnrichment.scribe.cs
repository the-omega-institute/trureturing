using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencySelf;

internal sealed class AgencyEnrichmentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/AgencySelf/AgencyEnrichment.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Agency enrichment pairs current state and strategy, isolates the strategy residual inside current fibers, and becomes agency completion only after controlled behavior closure.",
        H("Agency Enrichment"),
        Blocks(
            Theorem(
                "current-kernel-strategy-residual-partition",
                "current_kernel_strategy_residual_partition",
                "Current Kernel Strategy Residual Partition",
                "Inside a current-state fiber, a pair either agrees under the enriched readout or is a strategy residual.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "agency-kernel-disjoint-strategy-residual",
                "agency_kernel_disjoint_strategy_residual",
                "Agency Kernel Disjoint Strategy Residual",
                "The enriched kernel and the strategy residual are disjoint.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "no-strategy-residual-iff-kernel-inclusion",
                "no_strategy_residual_iff_kernel_inclusion",
                "No Strategy Residual iff Kernel Inclusion",
                "There is no strategy residual exactly when strategy is constant on every current-state fiber.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "strategy-factorization-iff-no-residual",
                "strategy_factorization_iff_no_residual",
                "Strategy Factorization iff No Residual",
                "Vanishing strategy residual is equivalent to a unique factor from the realized current-state image to the realized strategy image.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "agency-enrichment-kernel-eq-current-iff-no-residual",
                "agency_enrichment_kernel_eq_current_iff_no_residual",
                "Agency Enrichment Kernel eq Current iff No Residual",
                "Pairing strategy adds no new distinction exactly when the strategy residual vanishes.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."))));

    private static DocumentBlock.Describe Theorem(
        string id,
        string declaration,
        string title,
        string firstParagraph,
        string secondParagraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromLean(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(firstParagraph)),
                Paragraph(Text(secondParagraph))),
            DescribeRole.Theorem);
}
