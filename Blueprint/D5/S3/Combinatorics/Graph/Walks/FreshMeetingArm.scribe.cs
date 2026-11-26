using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class FreshMeetingArmDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The next edge on the second arm is fresh in the two path disclosures.",
        H("The prefix of a second arm"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fresh-edge-after-first-arm"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/Walks/FreshMeetingArm.fresh_edge_after_first_arm"),
                H("The next edge is absent from the disclosed path edges"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take two simple paths with the same start. If the first path has "
                        + "an edge, it starts with a different edge from the second. Every "
                        + "internal vertex of the second path lies outside the first path. "
                        + "The last vertex of the second path may lie on the first path.")),
                    Paragraph(Text(
                        "For any strict prefix of the second path, the next edge appears "
                        + "neither on the first path nor in that prefix. The recorded edges "
                        + "consist of the edges traversed on the two paths through the "
                        + "end of the prefix.")),
                    Paragraph(Text(
                        "At the common start a simple path uses only its first edge "
                        + "incident to that start. At a later step the departure vertex is "
                        + "outside the first path. Within the second path every edge is "
                        + "traversed at most once."))),
                DescribeRole.Theorem))));
}
