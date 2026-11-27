using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9FiveAxisThreeLeafInputsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At an exterior hub the three aligned contributions require three compensators. Hence any four directions contain at least one occupied neighbor.",
        H("Three leaves force exterior degree six"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("coherent-exterior-triples"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisThreeLeafInputs.coherent_exterior_triples"),
                H("Three leaves force exterior degree six"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At an exterior hub the three aligned contributions require three compensators. Hence any four directions contain at least one occupied neighbor."))),
                DescribeRole.Theorem)),
        []));
}
