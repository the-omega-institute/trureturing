using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class ActualJointThreePathUpdateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/ActualJointThreePathUpdate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal P and Q fragments and an actual connector form three new simple paths with exact inventories.",
        H("Recombining Three Actual Joint Paths"),
        Blocks(
            Paragraph(Text("The vertex type and simple graph are arbitrary. All paths and cycle inventories refer to the literal supplied walks. These statements provide actual graph-surgery steps; an all-order recursive Hamilton construction is a separate consumer.")),
            Describe.Lean(DescribeId.Create("actual-joint-three-path-update"),
                DeclarationHandle.Create(Prefix + "actual_joint_three_path_update"),
                H("Construct the Three New Joint Paths"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An actual distinguished path starts with the two supplied edges, and the actual route has been split into three supplied fragments. The real connector and seam explicitly assemble the three output walks. The source region has no repeated support, which earns all three path properties and the precise combined support and edge permutations; the returned walk identities expose the construction."))), DescribeRole.Theorem))));
}
