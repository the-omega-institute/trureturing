using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Orthogonality;

internal sealed class BinaryLineGraphDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All nonzero binary vectors and the actual line subgraph.",
        H("A complete correspondence in every dimension"),
        Blocks(Describe.Lean(DescribeId.Create("binary-vector-line-graph-isomorphism"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/BinaryLineGraph.graphIso"),
            H("Actual one-dimensional Submodules"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                "D5/L/QuadraticForms/binarysubspace2026complete")),
            Blocks(Paragraph(Text(
                "For every natural n, map a nonzero binary coordinate vector to its actual "
                + "one-dimensional span. Every line is obtained, and over ZMod2 two nonzero "
                + "vectors with the same span are equal. The resulting bijection preserves "
                + "distinct-dot-zero adjacency in both directions. The target is the graph "
                + "induced on every line of NikandishClique.orthogonalityGraph n; there is no "
                + "restriction to coordinate lines, chosen representatives or a subfamily. "
                + "The empty n=0 domain is included. The immediate consumer is the complete "
                + "six-dimensional line chromatic theorem."))), DescribeRole.Definition)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/Orthogonality/NikandishClique"))]));
}
