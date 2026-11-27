using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9FiveAxisOrbitThreeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fourth representative contradicts the local geometric and signed constraints.",
        H("Refutation of the fourth representative"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("impossible"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisOrbitThree.impossible"),
                H("Refutation of the fourth representative"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The fourth representative contradicts the local geometric and signed constraints."))),
                DescribeRole.Theorem)),
        []));
}
