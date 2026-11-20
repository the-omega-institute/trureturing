using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9CommonBoundaryObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Large balanced components have common exterior neighbors",
        H("Large balanced components have common exterior neighbors"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-distance-two-contact-lower-bound"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9CommonBoundaryObstruction.distance_two_pairs_card_ge_12"),
                H("At least twelve pairs have Hamming distance two"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Two disjoint closed Huang-balanced cubic components of order at least 72 in a 258-vertex subcubic set have at least twelve ordered cross pairs at Hamming distance two.")),
                    Paragraph(Text("Deleting one coordinate gives a bijection from each parity side of the nine-cube to the eight-cube. Neighborhoods across parity become closed neighborhoods after this folding. The coordinate-slice degree constraints and the seven-cube neighborhood recurrence give at least 130 exterior neighbors for each component.")),
                    Paragraph(Text("Closedness puts both exterior boundaries in the 254-point complement, so they intersect in at least six vertices. Each common neighbor contributes at least four pair incidences by the exterior parity equation. A distance-two pair has exactly two common neighbors."))),
                DescribeRole.Theorem)),
        []));
}
