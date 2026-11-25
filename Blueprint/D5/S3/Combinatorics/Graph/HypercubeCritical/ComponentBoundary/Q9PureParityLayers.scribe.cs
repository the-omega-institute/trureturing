using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9PureParityLayersDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PureParityLayers";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coordinate translation to adjacent Hamming layers",
        H("Coordinate translation to adjacent Hamming layers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-translate-adjacent-layers"),
                DeclarationHandle.Create(Module + ".exists_translate_adjacent_layers"),
                H("One cube translation places the component on two layers"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When every direction has double fibres of just one transverse parity, a single XOR translation turns their parity choices into a common direction of weight increase. The difference between Hamming weight and the original parity bit is constant along each edge and therefore throughout the component. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9OccupiedFibreParity")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SixtySixPointSupport/WeightLayerParity"))]));
}
