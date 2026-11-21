using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9PureBoundaryBinaryTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary boundary transport in the nine-cube",
        H("Binary boundary transport in the nine-cube"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-pure-boundary-binary-transport"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PureBoundaryBinaryTransport.filter_even_boundary_kernel"),
                H("A closed odd-degree region filters a binary kernel support"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Over the binary field, the signed Huang coordinate flips reduce to the ordinary coordinate flips. Their adjacency sum A squares to the identity in dimension nine, so B = I + A squares to zero.")),
                    Paragraph(Text("Suppose D is a support whose indicator lies in the kernel of B. Let P be disjoint from D, with odd internal degree at every vertex of P and every neighbor outside P in D. The vector B applied to the indicator of P vanishes on P by odd degree and outside the union by closure. On D, it records the parity of the number of P-neighbors. Adding it to the indicator of D leaves exactly the vertices of D with even P-degree, and the resulting indicator lies in the kernel of B.")),
                    Paragraph(Text("For the separated supports in Hong, Wu and Xia's Problem 2, a balanced cubic component supplies D by its odd internal degrees and Huang exterior parity. In the zero-slack profile with 524 contacts, the pure exterior region supplies P. On a parity side with 87 near vertices of D, the filter retains the six far vertices and the unique near vertex with even P-degree. This yields the seven-point parity support used as input to the orbit enumeration. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        []));
}
