using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class DominatingSetAverageBoundNonstemDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/DominatingSetAverageBoundNonstem.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The neighbour-replacement argument is the strict critical-incidence comparison in the proof of Theorem 2.9 of Iain Beaton and Ben Cameron, A Tight Upper Bound on the Average Order of Dominating Sets of a Graph, arXiv:2208.10475.",
        H("Neighbour Replacement for Self-Critical Vertices"),
        Blocks(
            Node("selfcritical", "selfCritical", "Self-critical vertices", "A self-critical vertex is critical and has no private neighbour outside the selected set.", DescribeRole.Definition),
            Node("selfcritical-erase-dominates-other", "selfCritical_erase_dominates_other", "Domination after deletion", "Deleting a self-critical vertex leaves every other vertex dominated.", DescribeRole.Theorem),
            Node("selfcritical-no-selected-neighbor", "selfCritical_no_selected_neighbor", "No selected neighbour", "A self-critical vertex has no neighbour in the dominating set.", DescribeRole.Theorem),
            Node("selfcritical-neighbor-replacement", "selfCritical_neighbor_replacement", "Neighbour replacement", "A self-critical vertex can be deleted and replaced by any nonempty collection of its neighbours without destroying domination.", DescribeRole.Theorem),
            Node("selfcritical-neighbor-replacement-injective", "selfCritical_neighbor_replacement_injective", "Injective replacement", "For a fixed vertex and a fixed set of its neighbours, replacing a self-critical vertex by that set is injective among dominating sets.", DescribeRole.Theorem),
            Node("selfcriticalsets-card-le-multineighborsets", "selfCriticalSets_card_le_multiNeighborSets", "Non-strict incidence comparison", "At a vertex of degree at least two, the number of self-critical dominating sets is at most the number omitting the vertex while selecting at least two neighbours.", DescribeRole.Theorem),
            Node("neighborwitness", "neighborWitness", "A dominating set outside the replacement image", "Select every neighbour of the fixed vertex and every other vertex outside the closed neighbourhoods of these neighbours.", DescribeRole.Definition),
            Node("selfcriticalsets-card-lt-multineighborsets", "selfCriticalSets_card_lt_multiNeighborSets", "Strict incidence comparison", "At a vertex of degree at least two, the number of self-critical dominating sets is strictly smaller than the number omitting the vertex while selecting at least two neighbours. The neighbour witness is outside the image of replacement.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
