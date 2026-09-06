using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class MemoryBlockBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Geometric hard-core memory, exact path semantics and integer certificates.",
        H("Uniform Block Bounds from Complete Prefixes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hard-core-memoryblockbounds-complete-count-le-memory"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/MemoryBlockBounds.complete_count_le_memory"),
                H("Complete paths are covered by truncated memory"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every depth and common history-based policy, inclusion of initial blockers gives an upper bound on complete-process counts by truncated-memory counts."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hard-core-memoryblockbounds-fixed-order-block-bound"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/MemoryBlockBounds.fixed_order_block_bound"),
                H("A complete prefix bounds every later depth"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fix one relative ordering. For r at least k and at least one, every initial blocker set containing the parent satisfies the explicit bound at depth q times k plus s. Its coefficient is the actual complete depth-k root count raised to q, times three raised to s. Parent retention, uniform continuation domination and finite-horizon exactness supply the proof. The theory derives fixed-order growth-rate completeness from this bound; the limit theorem is not separately elaborated here."))),
                DescribeRole.Theorem))));
}
