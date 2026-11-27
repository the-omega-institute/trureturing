using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9FiveAxisOrbitTwoDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The third representative contradicts the local geometric and signed constraints.",
        H("Refutation of the third representative"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("impossible"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisOrbitTwo.impossible"),
                H("Refutation of the third representative"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The third representative contradicts the local geometric and signed constraints."))),
                DescribeRole.Theorem)),
        []));
}
