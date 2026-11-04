using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Hypercube;

internal sealed class EdgeExpansionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Hypercube/EdgeExpansion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every subset of a Boolean cube has at least its smaller side many crossing edges.",
        H("Boolean cube edge expansion"),
        Blocks(
            Paragraph(Text(
                "The two coordinate halves carry smaller cubes, joined by a perfect matching. "
                    + "Splitting a vertex set along this product gives a dimension induction "
                    + "for its edge boundary.")),
            Describe.Lean(
                DescribeId.Create("vertex"),
                DeclarationHandle.Create(Prefix + "Vertex"),
                H("Recursive bit strings"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The zero-dimensional carrier is Unit. The successor carrier is Bool times the preceding carrier, so a vertex is a bit followed by its remaining coordinates."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("vertex-fintype"),
                DeclarationHandle.Create(Prefix + "vertexFintype"),
                H("Finite coordinate carrier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite enumeration is inherited recursively from Unit and the product with Bool."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("vertex-decidable-eq"),
                DeclarationHandle.Create(Prefix + "vertexDecidableEq"),
                H("Equality of bit strings"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Equality is decided recursively using equality of the leading Boolean coordinate and the tail."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("slice"),
                DeclarationHandle.Create(Prefix + "slice"),
                H("Coordinate halves"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The slice at a Boolean value consists of tails whose extension by that leading bit belongs to W. The two slice cardinalities sum to the cardinality of W."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("recursive-boundary"),
                DeclarationHandle.Create(Prefix + "edgeBoundary"),
                H("Internal edges and the matching"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In dimension zero the recursive count is zero. In a successor dimension it is the sum of the two slice boundary counts and the cardinality of the symmetric difference of the slices. The latter counts exactly those matching edges whose endpoints have different membership in W."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("adjacency"),
                DeclarationHandle.Create(Prefix + "Adjacent"),
                H("One-coordinate adjacency"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two vertices are adjacent when either their leading bits agree and their tails are adjacent, or their leading bits differ and their tails agree. The zero-dimensional carrier has no adjacent pair. This is precisely the recursive Cartesian product description of the Boolean cube."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cube-graph"),
                DeclarationHandle.Create(Prefix + "cubeGraph"),
                H("The cube as a simple graph"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The adjacency relation is symmetric and irreflexive, giving a simple graph on the recursive coordinate carrier."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("boundary-edges"),
                DeclarationHandle.Create(Prefix + "boundaryEdges"),
                H("Crossing edges counted once"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A boundary edge is an adjacent ordered pair with its first endpoint in W and its second endpoint outside W. Every undirected crossing edge has exactly one such orientation. The proof partitions this finite set into the boundaries inside the two halves and the crossing coordinate matching; the three sets are disjoint and each lifting map is injective. Consequently its cardinality equals the recursive boundary count."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("edge-expansion"),
                DeclarationHandle.Create(Prefix + "edge_expansion"),
                H("The edge expansion inequality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural dimension n and every vertex set W, the number of crossing edges is at least the minimum of the cardinality of W and two to the power n minus that cardinality. No positivity, connectivity, or size restriction is imposed on W. The proof inducts on n. If the slices have sizes a and b in halves of size M, their internal boundaries contribute at least min(a,M-a) and min(b,M-b). The symmetric difference contributes enough to bound both a-b and b-a. These inequalities imply the required bound min(a+b,2M-a-b), including the empty and full sets and dimension zero."))),
                DescribeRole.Theorem)),
        []));
}
