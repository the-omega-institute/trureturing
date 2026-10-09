using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class DominatingSetAverageBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/DominatingSetAverageBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The inequality is Theorem 2.9 of Iain Beaton and Ben Cameron, A Tight Upper Bound on the Average Order of Dominating Sets of a Graph, arXiv:2208.10475. Stem blocks are grouped by their vertex sets, so a two-vertex component gives one block.",
        H("Two-Thirds Bound for Dominating-Set Averages"),
        Blocks(
            Node("activeblocks", "activeBlocks", "Active stem blocks", "A leaf-stem block is active for a selected set when at least one vertex in the block is omitted.", DescribeRole.Definition),
            Node("residual", "residual", "Residual vertices", "The residual vertices lie outside the union of the active stem blocks.", DescribeRole.Definition),
            Node("core", "core", "Vertices outside all stem blocks", "The core consists of vertices belonging to no leaf-stem block.", DescribeRole.Definition),
            Node("privateneighbor-residual", "privateNeighbor_residual", "Private neighbours remain residual", "A private outside neighbour of a selected residual vertex also lies in the residual set.", DescribeRole.Theorem),
            Node("externallycritical-residual-card-le", "externallyCritical_residual_card_le", "Residual private-neighbour estimate", "The number of externally critical residual vertices is bounded by the number of residual private outside neighbours.", DescribeRole.Theorem),
            Node("selfcritical-inter-residual", "selfCritical_inter_residual", "Self-critical residual vertices", "In a dominating set, the self-critical residual vertices are precisely the self-critical vertices in the core.", DescribeRole.Theorem),
            Node("residual-total-le", "residual_total_le", "Residual incidence estimate", "In an isolate-free graph, the total number of residual critical incidences is at most the total number of residual omitted incidences.", DescribeRole.Theorem),
            Node("active-block-total-le", "active_block_total_le", "Active-block incidence estimate", "Summing over all active stem blocks and all dominating sets gives no more critical incidences than omitted incidences.", DescribeRole.Theorem),
            Node("critical-total-le-omitted-total", "critical_total_le_omitted_total", "Global incidence estimate", "The total number of critical incidences over all dominating sets is at most the total number of omitted incidences in an isolate-free finite graph.", DescribeRole.Theorem),
            Node("avd-le-two-thirds", "avd_le_two_thirds", "Beaton–Cameron inequality", "For every finite graph G without isolated vertices, avd(G) is at most 2|V(G)|/3. The empty graph is included and has average zero.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
