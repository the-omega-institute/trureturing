using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.LinearForests;

internal sealed class DirectedForestCompletionCountsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Tsaban =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/tsaban2003permutation");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact counts on a directed forest and its full-cycle completion event.",
        H("Counts for directed linear-forest completions"),
        Blocks(Describe.Lean(
            DescribeId.Create("directed-forest-edge-and-completion-mass"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/Graph/LinearForests/DirectedForestCompletionCounts.edge_and_completion_mass"),
            H("Edges and uniform full-cycle extension mass"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Tsaban),
            Blocks(
                Paragraph(Text(
                    "Let an acyclic relation on N labelled vertices have at most one incoming "
                    + "and one outgoing edge per vertex. Include the isolates in its c weak "
                    + "components and assume N and c are at least two. The edge set has N minus "
                    + "c members. For any uniform probability mass on the actual full cycles, "
                    + "the event of extending all the prescribed edges has positive mass "
                    + "equal to (c-1)! divided by (N-1)!.")),
                Paragraph(Text(
                    "Projecting each edge to its source gives a bijection onto the vertices "
                    + "with an outgoing edge. Their complement consists of the component tails. "
                    + "The completion equivalence counts the extension event, and every full "
                    + "cycle has the same mass. Summing over that event gives the stated ratio."))),
            DescribeRole.Theorem))));
}
