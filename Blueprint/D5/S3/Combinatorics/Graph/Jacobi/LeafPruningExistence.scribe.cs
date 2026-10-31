using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Jacobi;

internal sealed class LeafPruningExistenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Jacobi/LeafPruningExistence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite actual flag graph admits terminal leaf pruning", H("Every finite actual flag graph admits terminal leaf pruning"),
        Blocks(
            Describe.Lean(DescribeId.Create("finite-actual-terminal-leaf-pruning"),
                DeclarationHandle.Create(Prefix + "exists_leaf_pruning"), H("A terminal chronology exists without a supplied pruning certificate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite cyclic flag graph there exists a genuine LeafPruning: every deleted owner orbit has at most one remaining actual incident flag at deletion time, numbered anchor vertices are protected, and every terminal nonanchor orbit has at least two remaining flags. The theorem assumes neither connectedness nor stability and retains loops and parallel edges. Its proof starts with the empty chronology, bounds deletion length by the number of actual owner orbits, and chooses a longest admissible prefix. Any terminal nonanchor with at most one remaining flag would extend that prefix by one step, contradicting maximality. Both flags of a loop are counted, so a loop cannot be discarded as a degree-one adjacency. Together with the existing extraction and vanishing theorems, this supplies actual terminal prunings for later arguments; uniqueness of the retained core, the bare-circle source case, global skeleton normal form and the full four-loop theorem are separate obligations."))), DescribeRole.Theorem))));
}
