using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9FiveAxisCoherentHubDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The four corresponding contacts make the hub exterior. Its four coherent contributions require four further neighbors and exterior parity forces degree eight.",
        H("Four leaves force eight neighbors"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("card-le-four-of-shared-faces"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisCoherentHub.card_le_four_of_shared_faces"),
                H("Four leaves force eight neighbors"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The four corresponding contacts make the hub exterior. Its four coherent contributions require four further neighbors and exterior parity forces degree eight."))),
                DescribeRole.Theorem)),
        []));
}
