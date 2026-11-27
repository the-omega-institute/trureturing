using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9FiveAxisRepresentativeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The stabilizer moves the contact layer to its orbit representative. The normalized supports retain separation, cubical regularity, the contact masks, the midpoint and translation laws, and the exterior sign cancellation.",
        H("A signed representative for every actual pair"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-signed-representative"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisRepresentative.exists_signed_representative"),
                H("A signed representative for every actual pair"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The stabilizer moves the contact layer to its orbit representative. The normalized supports retain separation, cubical regularity, the contact masks, the midpoint and translation laws, and the exterior sign cancellation."))),
                DescribeRole.Theorem)),
        []));
}
