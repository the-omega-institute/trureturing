using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9FiveAxisOrbitZeroDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first representative contradicts the local geometric and signed constraints.",
        H("Refutation of the first representative"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("impossible"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisOrbitZero.impossible"),
                H("Refutation of the first representative"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The first representative contradicts the local geometric and signed constraints."))),
                DescribeRole.Theorem)),
        []));
}
