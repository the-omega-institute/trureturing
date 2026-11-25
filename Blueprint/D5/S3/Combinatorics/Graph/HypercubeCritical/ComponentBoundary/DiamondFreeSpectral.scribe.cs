using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class DiamondFreeSpectralDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/DiamondFreeSpectral";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Spectral rigidity with no shared triangle edge",
        H("Spectral rigidity with no shared triangle edge"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("diamond-free-two-step-incidence"),
                DeclarationHandle.Create(Module + ".two_step_incidence_bound"),
                H("Two-step incidence bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The neighborhood of a vertex has disjoint edges. Every external vertex can touch at most one endpoint of each such edge, giving a sharp finite incidence bound on walks of length two."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("diamond-free-eight-rigidity"),
                DeclarationHandle.Create(Module + ".card_ge_eight_and_rigidity"),
                H("Eigenvalue four forces eight vertices and rigid equality"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At a maximum of the positive eigenvector, the two-step row sum is at least sixteen. The incidence bound forces at least eight vertices, and at equality the graph is the complete bipartite graph with two parts of four."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCardinalityGap"))]));
}
