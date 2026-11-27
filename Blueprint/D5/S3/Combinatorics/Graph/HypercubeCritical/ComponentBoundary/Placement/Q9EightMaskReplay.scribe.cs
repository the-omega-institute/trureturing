using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9EightMaskReplayDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";
    private const string Owner = Placement + "Q9EightMaskReplay.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A checked refutation excludes exactly eight distance-two masks.",
        H("Exactly eight distance-two masks are impossible"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("minimum-displacements-card-ne-eight"),
                DeclarationHandle.Create(Owner + "minimum_displacements_card_ne_eight"),
                H("Exactly eight distance-two masks are impossible"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each participating axis has three partners or more by signed contact cancellation. The five-axis graph at equality reduces to a single chosen contact orbit. Lean proves that the normalized pair satisfies each of the 11,564 input clauses and replays the 4,104-step LRAT refutation. The certificate needs only the two realized masks {0, 3} and {0, 4}, in addition to the local degree, parity, and separation constraints. <https://arxiv.org/html/2610.09483v1#Thmproblem2>"))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9EightMaskClauses")),
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9EightMaskGraph")),
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9SharedContactGeometryReplay"))
        ]));
}
