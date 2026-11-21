using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Hypercube;

internal sealed class BinaryAdjacencyWeightDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Graph/Hypercube/BinaryAdjacencyWeight";
    private static readonly LibraryNoteRef CubeCode =
        LibraryNoteRef.Create("D5/L/Hamming/fishkeymwambene2009cubecodes");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weight residues for binary cube adjacency",
        H("Weight residues for binary cube adjacency"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("binary-cube-word-weight"),
                DeclarationHandle.Create(Module + ".weight"),
                H("Weight of a binary cube function"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Hamming weight is the sum of the natural representatives of the binary values, so it counts the vertices where the function is one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("binary-cube-adjacency-weight-residue"),
                DeclarationHandle.Create(Module + ".weight_adjacency_mod_four"),
                H("Binary adjacency weight modulo four"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In every dimension n, the weight of Bf is congruent to n times the weight of f modulo four. Square the unsigned neighbor count at every vertex. Modulo four the square equals the parity of that count. Each diagonal term sums to the preimage weight by a singleton translation. For distinct directions i and j, translation by their sum is a fixed-point-free involution exchanging the two factors of the correlation. The doubled correlation vanishes modulo four."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("binary-cube-adjacency-weight-coordinate-moment"),
                DeclarationHandle.Create(Module + ".weight_adjacency_mod_four_eq_coordinate_moment"),
                H("A coordinate moment gives the image weight residue"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In positive even dimension, each coordinate moment of Bf is the parity of f's weight. Multiplying its natural representative by n modulo four gives the exact weight residue of Bf. For n congruent to two modulo four, residue zero means that every preimage has even weight, and residue two means that every preimage has odd weight."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("binary-cube-adjacency-kernel-doubly-even"),
                DeclarationHandle.Create(Module + ".four_dvd_weight_of_adjacency_eq_zero"),
                H("Kernel weights are multiples of four in dimensions divisible by four"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(CubeCode),
                Blocks(
                    Paragraph(Text("Every binary adjacency kernel word in positive dimension divisible by four has weight divisible by four. Section 4, Result 2 of the cited note's source records self-duality of the positive even-dimensional adjacency code. Here the explicit contraction gives kernel equals image, and the image weight congruence gives the divisibility.")),
                    Paragraph(Text("In the Q8 fold of Hong, Wu and Xia's Q9 Problem 2, the syndrome of a support is B applied to its indicator over the binary field. Equal syndromes put the symmetric difference in the kernel. In the 114+144 regular order-17 branch, the 17 dimer centers D cannot have zero syndrome. If D has the same syndrome as a singleton q, the possible weights of D △ {q} are 16 and 18. Divisibility by four forces weight 16, so q belongs to D. In the 120+138 fold, equal-syndrome singleton supports must have symmetric difference of weight divisible by four. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        []));
}
