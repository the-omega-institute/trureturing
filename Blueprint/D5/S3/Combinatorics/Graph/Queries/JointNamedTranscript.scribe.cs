using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Queries;

internal sealed class JointNamedTranscriptDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Naming multiplicities in the posterior of a graph observed through complete neighborhoods.",
        H("Conditioning on an actual named transcript"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("named-transcript-count"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/Queries/JointNamedTranscript.transcript_naming_count"),
                H("Feasible placements have equally many full namings"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fix finite vertex and name sets and prescribed initial assignments. "
                    + "Take an actual transcript of a deterministic protocol that queries a name "
                    + "and receives its complete unordered neighborhood or a miss. The transcript "
                    + "determines the seen names and the names ruled out by misses. On a candidate "
                    + "graph, a feasible placement embeds the seen names into the vertices, "
                    + "agrees with the initial assignments and realizes every reported neighbor "
                    + "set as the entire neighborhood of its queried vertex.")),
                    Paragraph(Text(
                    "The number of full namings that replay the transcript equals the number "
                    + "of feasible placements times a falling factorial. Its base is the number "
                    + "of names remaining after removing the seen and ruled-out names. Its "
                    + "order is the number of vertices outside a placement. Inside each "
                    + "placement, every full naming is an injection of those remaining vertices "
                    + "into the remaining names."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("named-transcript-graph-posterior"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/Queries/JointNamedTranscript.graph_posterior"),
                H("The posterior weights each graph by its feasible placements"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Sample a graph index from a prior probability mass function. Independently "
                    + "choose a uniform injection preserving the prescribed initial assignments. "
                    + "Condition on a positive-mass transcript of the same deterministic "
                    + "protocol. The conditional mass of each index equals its prior mass times "
                    + "the number of feasible placements on its graph, divided by the sum of "
                    + "these weights. The common count of naming extensions cancels in the "
                    + "normalization."))),
                DescribeRole.Theorem))));
}
