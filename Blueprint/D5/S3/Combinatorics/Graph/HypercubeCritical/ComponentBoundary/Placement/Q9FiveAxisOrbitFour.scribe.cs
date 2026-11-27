using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9FiveAxisOrbitFourDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fifth representative contradicts the local geometric and signed constraints.",
        H("Refutation of the fifth representative"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("impossible"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisOrbitFour.impossible"),
                H("Refutation of the fifth representative"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The fifth representative contradicts the local geometric and signed constraints."))),
                DescribeRole.Theorem)),
        []));
}
