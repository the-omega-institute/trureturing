using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9FiveAxisOrbitCoverDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The rooted even contact layer has eighteen patterns. A coordinate swap and the exchange of the two roots partition them into six orbits.",
        H("Six orbits of the rooted contact layer"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("covers"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisOrbitCover.covers"),
                H("Six orbits of the rooted contact layer"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The rooted even contact layer has eighteen patterns. A coordinate swap and the exchange of the two roots partition them into six orbits."))),
                DescribeRole.Theorem)),
        []));
}
