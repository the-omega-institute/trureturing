using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9FiveAxisExteriorPolarityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonzero contribution in a zero-sum exterior row forces one of the opposite sign.",
        H("Opposite contributions on exterior rows"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-opposite-contribution"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisExteriorPolarity.exists_opposite_contribution"),
                H("Opposite contributions on exterior rows"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A nonzero contribution in a zero-sum exterior row forces one of the opposite sign."))),
                DescribeRole.Theorem)),
        []));
}
