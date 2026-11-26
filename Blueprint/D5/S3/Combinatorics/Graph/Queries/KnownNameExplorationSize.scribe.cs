using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Queries;

internal sealed class KnownNameExplorationSizeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A degree bound controls the number of names seen during an exploration.",
        H("The size of a known-name exploration"),
        Blocks(Describe.Lean(
            DescribeId.Create("known-name-exploration-size"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/Graph/Queries/KnownNameExplorationSize.known_names_card_bound"),
            H("Degree bound for a known-name exploration from a root"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Injectively name the vertices of a simple graph in a finite name set. "
                + "Initially give a deterministic strategy only the root's name. "
                + "Query the graph for complete unordered neighborhoods at known names and "
                + "answer all other queries with a synthetic miss. If the root has degree at "
                + "most d and all vertices have degree at most d plus one, then the final "
                + "number of known names is at most one plus d times the number of actual calls. "
                + "A known vertex other than the root was revealed by a query to a neighbor "
                + "whose name is still known."))),
            DescribeRole.Theorem))));
}
