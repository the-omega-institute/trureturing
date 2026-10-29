using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;
internal sealed class ProductMarginBlockStateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual subnormalized block-state partial traces", H("ProductMarginBlockState"), Blocks(
            Describe.Lean(DescribeId.Create("block-partial-traces"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ProductMarginBlockState.block_partial_traces"),
                H("Actual subnormalized block-state partial traces"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/codex2026productmargin")),
                Blocks(Paragraph(Text("The four blocks are (P-K)/2, K/2, K/2 and (Q-K)/2. The blockState constructor proves positivity and trace one for density states P and Q and an arbitrary complex positive semidefinite common lower matrix K. Tracing out either classical bit gives the same two row sums P/2 and Q/2; tracing out both gives (P+Q)/2. Zero blocks remain zero and are never normalized by their own trace. This module proves the physical state and matrix marginal identities; it does not assume or assert the final Zhang–Yeung entropy reduction."))), DescribeRole.Theorem))));
}
