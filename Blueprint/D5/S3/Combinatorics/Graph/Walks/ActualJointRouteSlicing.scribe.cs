using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class ActualJointRouteSlicingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/ActualJointRouteSlicing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The retained joint prefix and two actual route cuts yield the literal fragments used by graph surgery.",
        H("Actual Joint and Route Fragments"),
        Blocks(
            Paragraph(Text("The vertex type and simple graph are arbitrary. All paths and cycle inventories refer to the literal supplied walks. These statements provide actual graph-surgery steps; an all-order recursive Hamilton construction is a separate consumer.")),
            Describe.Lean(DescribeId.Create("actual-joint-and-route-three-fragments"),
                DeclarationHandle.Create(Prefix + "actual_joint_and_route_three_fragments"),
                H("Recover the Actual P and Q Fragments"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The old actual vertex partition and retained supplier edges force the distinguished joint path prefix. Two cuts in distinct supplied route pieces have earned strict order on the same joined route. The output records the original joint tail and three actual simple route fragments with exact support and edge decompositions."))), DescribeRole.Theorem))));
}
