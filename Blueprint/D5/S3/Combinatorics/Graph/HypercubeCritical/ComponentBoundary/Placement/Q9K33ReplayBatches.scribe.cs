using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9K33ReplayBatchesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Named intermediate consequences reduce the memory needed to replay a resolution proof.",
        H("Intermediate consequences of the contact certificate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("replay"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33ReplayBatches.replay"),
                H("Replay in batches"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Lean replay uses the resolution hints in their original order. When facts are used in a later batch, a theorem records that they follow from the original clauses. The kernel checks each such theorem and the final contradiction."))),
                DescribeRole.Definition)),
        []));
}
