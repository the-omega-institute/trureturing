using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9FoldedCycleRankDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedCycleRank";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The binary Laplacian computes the residual switching rank for exact integer signed rows.",
        H("Residual switching rank of folded signed rows"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("residual-rank"),
                DeclarationHandle.Create(Module + ".residual_rank_add_twice_rank"),
                H("The Laplacian computes the residual quotient dimension"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let B be a binary vertex-by-edge matrix and write C for the kernel of incidence multiplication. The bicycle subspace is the intersection of C with the range of transpose multiplication. The residual quotient consists of cycles modulo these bicycles.")),
                    Paragraph(Text("Restrict incidence to the range of transpose multiplication. The image is the range of the product of B with its transpose, and the kernel maps isomorphically onto the bicycle subspace. Rank–nullity and equality of transpose ranks give the bicycle dimension. Quotienting the incidence kernel then yields the asserted additive rank identity.")),
                    Paragraph(Text("The cycle–cut intersection is the classical bicycle space of Rosenstiehl and Read, On the Principal Edge Tripartition of a Graph, pp. 195–226. Here the rank calculation is paired with the exact row criterion below. https://doi.org/10.1016/S0167-5060(08)70508-9"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exact-signed-rows"),
                DeclarationHandle.Create(Module + ".exact_signed_rows"),
                H("Exact signed rows are feasible precisely when an exact witness has zero class"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a finite simple graph, restrict Mathlib incidence to actual unordered edges. The transpose adds the two endpoint labels, so adding its image to the original edge bits performs a vertex switch. The integer incidence weights count negative incident edges, and reduction modulo two is multiplication by the binary incidence matrix. The signed row at each vertex is its degree minus twice its negative count.")),
                    Paragraph(Text("Fix a switch whose negative count already has the target parity. Every exact negative-count witness differs from this reference by a cycle. Its residual class vanishes exactly when the cycle is a parity-preserving switch, so a zero-class witness lifts to a vertex switch satisfying the exact signed rows. If the residual dimension is zero, every exact negative-count witness lifts."))),
                DescribeRole.Theorem),
            Paragraph(Text("For an induced cube example, label vertices by the integers represented by their binary coordinates. Join Hamming-distance-one pairs and use the Huang sign whose negative bit is the parity of the coordinates below the changed coordinate. The induced theta on sites 0, 1, 3, 4, 6, 7, 8, 10 and 11 has three paths of lengths 2, 4 and 4 between sites 0 and 3. Incidence and Laplacian have binary ranks 8 and 6, giving residual rank zero. Enumeration gives 240 distinct exact negative-degree profiles compatible with a switched parity, all attained by switches.")),
            Paragraph(Text("The induced graph on sites 0, 1, 2, 3, 4 and 5 consists of two squares sharing an edge. Incidence and Laplacian both have binary rank 5, giving residual rank two. Enumeration gives 112 exact profiles compatible with a switched parity, of which 32 are attained by switches. These counts enumerate all edge-bit vectors for the exact profiles and all vertex masks for the switched profiles.")),
            Paragraph(Text("For the folded singleton rows of the Q₉ problem, the criterion applies when the graph accounts for the row incidences and the targets account for the other fixed terms. The value of f₂(Q₉) is the question in Hong, Wu and Xia's Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
        []));
}
