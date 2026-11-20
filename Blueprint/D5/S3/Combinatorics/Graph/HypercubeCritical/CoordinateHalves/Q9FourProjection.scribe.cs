using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves;

internal sealed class Q9FourProjectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four-coordinate projection sizes in the nine-cube",
        H("Every four-coordinate projection has at least eight points"),
        Blocks(Describe.Lean(
            DescribeId.Create("q9-four-projection-at-least-eight"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9FourProjection."
                    + "four_projection_card_ge_eight"),
            H("The four-coordinate projection bound"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let the support be Huang-balanced and induced cubic with 72 vertices. "
                    + "Assume that every coordinate half has at least 30 vertices. "
                    + "Every choice of four distinct coordinates realizes at least eight patterns.")),
                Paragraph(Text(
                    "A missing pattern on three of the four coordinates corresponds to a "
                    + "complement edge along the dropped axis. The constraints on pairs and triples "
                    + "force any two such edges to be antipodal. If the projection has at most seven "
                    + "points, counts in the four coordinate matchings force exactly seven and "
                    + "make every complement edge occur with its antipode.")),
                Paragraph(Text(
                    "The nine-point complement has an unpaired vertex. It is isolated in the "
                    + "complement, so its four neighbors and its antipode belong to the projection. "
                    + "Translating this vertex to zero gives a missing weight-three point whose "
                    + "three weight-two neighbors also belong to the projection. This gives the "
                    + "eighth point and excludes the assumed size.")),
                Paragraph(Text(
                    "The bound applies to the order-72 branch of Hong, Wu and Xia, "
                    + "arXiv:2610.09483v1, Section 7, Problem 2."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairProjection")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TripleProjection"))
        ]));
}
