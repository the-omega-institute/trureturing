using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Laurent;

internal sealed class Q9LaurentNormalizedBoxesDocument : IScribeDocumentDefinition
{
    private const string Boundary =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/";
    private const string Owner = Boundary + "Laurent/Q9LaurentNormalizedBoxes.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Each transverse component realizes one box with the descended height.",
        H("Normalized boxes and projected height"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("realize-normalized-component"),
                DeclarationHandle.Create(Owner + "realize_normalized_component"),
                H("Each transverse component realizes one box with the descended height"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Permute the six complementary axes to put both splits into the normalized pair. The two star centers specify a translation of the crossing pairs of the selected split. The Laurent exponent along each block equals a constant plus the corresponding translated bit."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "Laurent/Q9LaurentStarProducts")),
         DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "Q9ProjectedHeightCompatibility"))]));
}
