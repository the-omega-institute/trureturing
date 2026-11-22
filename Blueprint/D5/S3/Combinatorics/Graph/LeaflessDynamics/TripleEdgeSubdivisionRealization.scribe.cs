using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.LeaflessDynamics;

internal sealed class TripleEdgeSubdivisionRealizationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/LeaflessDynamics/TripleEdgeSubdivisionRealization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Homeomorphism of a multigraph and its subdivided realization",
        H("Homeomorphism of a multigraph and its subdivided realization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("triple-edge-subdivision-homeomorphism"),
                DeclarationHandle.Create(Owner + "subdivisionHomeomorph"),
                H("The closed-edge quotient and its affine subdivision are homeomorphic"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Divide each closed edge interval into thirds. The two interior subdivision vertices record the edge flags. The piecewise affine map respects exactly the endpoint identifications of the original graph and descends from the compact quotient."))),
                DescribeRole.Definition))));
}
