using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class EdgeCoverLengthMetricDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/EdgeCoverLengthMetric.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Topology/mazhang2026centraledges");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Constant lengths on edge-disjoint spanning edge covers of K_n give center {0, a_1, …, a_s} and central edges their union.",
        H("Prescribed central distances from edge-cover packings"),
        Blocks(
            Describe.Lean(DescribeId.Create("length-data-def"),
                DeclarationHandle.Create(Prefix + "LengthData"), H("Length data on K_n"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Edge-disjoint spanning edge covers F_1, …, F_s of K_n (every vertex lies on an edge "
                    + "of each F_i), class lengths a_1, …, a_s, and a length for every edge outside the "
                    + "classes, these lengths pairwise distinct and different from every a_i; all lengths "
                    + "lie in a band [c, 2c] with c > 0."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("length-space-def"),
                DeclarationHandle.Create(Prefix + "LSpace"), H("The prescribed metric space"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The n vertices with distance 0 on the diagonal, a_i on the edges of F_i and the "
                    + "prescribed length on every other edge. This is a metric space because in a triangle "
                    + "of distinct vertices the longest side is at most 2c while the other two sum to at "
                    + "least 2c."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("edge-cover-length-metric"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Center and central edges of the prescribed metric"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "For n ≥ 3 the metric has distance a_i on the edges of F_i and the prescribed length on "
                        + "the remaining edges, its center is C(X) = {0, a_1, …, a_s}, and two vertices are "
                        + "joined in the central graph exactly when they are joined in some F_i.")),
                    Paragraph(Text(
                        "Each a_i is central because F_i covers every vertex. A nonzero central value is a "
                        + "distance from vertex 0; if it were a length outside the classes, a vertex z off "
                        + "that unique edge would need an edge of the same length at z, which is a different "
                        + "edge with the same length, impossible. So the positive central values are exactly "
                        + "the a_i, and the central edges are the class edges. This is equation (1) of H. Ma "
                        + "and W. Zhang (DOI 10.5281/zenodo.24369118), with the band [1, 2) generalized to "
                        + "[c, 2c] and without requiring the a_i to be distinct; it uses the narrow-band "
                        + "principle of O. Dovgoshey and O. Rovenska "
                        + "(arXiv:2610.11596, proof of Theorem 3.8, formula (19))."))),
                DescribeRole.Theorem))));
}
