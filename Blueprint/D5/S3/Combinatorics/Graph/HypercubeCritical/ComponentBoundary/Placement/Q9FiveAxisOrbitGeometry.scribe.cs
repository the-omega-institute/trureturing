using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9FiveAxisOrbitGeometryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shared midpoint counts and weighted contact translations justify the finite tableau directly from the separated supports.",
        H("Geometry of the rooted contact layer"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-covered-normalization"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisOrbitGeometry.exists_covered_normalization"),
                H("Geometry of the rooted contact layer"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Shared midpoint counts and weighted contact translations justify the finite tableau directly from the separated supports."))),
                DescribeRole.Theorem)),
        []));
}
