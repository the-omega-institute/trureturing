using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Hypercube;

internal sealed class BinaryKernelCrossingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelCrossing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Crossing pairs in the binary cube adjacency kernel",
        H("Crossing pairs in the binary cube adjacency kernel"),
        Blocks(
            Paragraph(Text("A cube vertex is the subset of coordinates with bit one. For a pivot x, the symmetric difference with x records the changed coordinates and its cardinality is Hamming distance. This lets x serve as the origin for any pivot. Each coordinate flip gives a distinct neighbor, so the mod-two adjacency equation says that the number of selected directions is even.")),
            Describe.Lean(
                DescribeId.Create("cube-binary-neighbor-directions"),
                DeclarationHandle.Create(Prefix + "neighborDirections"),
                H("Selected neighbor directions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a finite cube support R and a vertex x, retain the coordinate directions whose singleton flip of x lies in R."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cube-binary-crossing-pair-bounds"),
                DeclarationHandle.Create(Prefix + "crossing_pair_bounds"),
                H("Distance-three and total support bounds"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let k count selected neighbors of a pivot x and suppose every vertex two flips from x has an even number of neighbors in R. Each pair consisting of a selected direction i and an unselected direction j determines a two-flip vertex. Exactly one of its neighbors that undo either flip is selected. Even degree requires another selected neighbor, reached by flipping a third coordinate.")),
                    Paragraph(Text("The three changed coordinates split into selected and unselected directions at x. The product of the two part sizes is at most two, so each distance-three support vertex covers at most two crossing pairs. The k(n − k) crossing pairs give the distance-three bound. The k distinct distance-one vertices are disjoint from that layer and give the total bound 2|R| ≥ 2k + k(n − k).")),
                    Paragraph(Text("In the 10+4 rook case for an 84-vertex component in the nine-cube, the 24 forced singleton contacts form a binary kernel support in the folded eight-cube. This leaves eight further singleton sites. If the extra even dimer meets four of them, the bound requires at least eight sites at distance three and twelve in total. This excludes that rook case in the study of Hong, Wu and Xia's Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cube-binary-minimum-weight"),
                DeclarationHandle.Create(Prefix + "card_ge_dimension"),
                H("The weight of a nonzero kernel word"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In positive dimension, choose a pivot next to a support vertex. Its selected degree is positive and even, hence at least two. Since k ≤ n, the crossing bound is at least 2k + 2(n − k) = 2n. In dimension zero the claimed lower bound is zero."))),
                DescribeRole.Theorem)),
        []));
}
