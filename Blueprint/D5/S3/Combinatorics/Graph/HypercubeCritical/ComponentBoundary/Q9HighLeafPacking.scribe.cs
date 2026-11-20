using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9HighLeafPackingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9HighLeafPacking.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed direction sets control high-degree exterior neighbors",
        H("Signed direction sets control high-degree exterior neighbors"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-high-leaf-packing"),
                DeclarationHandle.Create(Prefix + "card_highLeafDirections_le_by_degree"),
                H("Signed direction sets control high-degree exterior neighbors"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Consider an exterior mate of vertices which each have eight neighbors "
                        + "in a balanced cubic support. The four positive directions of one such "
                        + "vertex intersect those of another in at most one direction. This "
                        + "follows from the sign around each selected triple.")),
                    Paragraph(Text("Four of these direction sets would occupy at least ten coordinates. "
                        + "Three sets exhaust the nine coordinates and leave no direction with a "
                        + "uniform sign. At most two sets can coexist when the mate has selected "
                        + "neighbors, and a mate with four or more selected neighbors permits at "
                        + "most one."))),
                DescribeRole.Theorem)),
        []));
}
