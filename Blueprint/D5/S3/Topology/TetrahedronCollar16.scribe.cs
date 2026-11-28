using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class TetrahedronCollar16Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The tetrahedral interval certificate",
        H("The tetrahedral interval certificate"),
        Blocks(Describe.Lean(
            DescribeId.Create("tetrahedroncollar16-result"),
            DeclarationHandle.Create("D5/S3/Topology/TetrahedronCollar16.relative_retraction"),
            H("The tetrahedral interval certificate"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text("The fixed depth-three table supplies Lipschitz heights on both main regions. Relative interval contiguity compares the heights with those of the two-cut retraction while fixing the inherited endpoint values."))),
            DescribeRole.Theorem))));
}
