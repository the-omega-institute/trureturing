using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class OrdinaryTetrahedronCollarDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two cuts on the ordered tetrahedron",
        H("The two cuts on the ordered tetrahedron"),
        Blocks(Describe.Lean(
            DescribeId.Create("ordinarytetrahedroncollar-result"),
            DeclarationHandle.Create("D5/S3/Topology/OrdinaryTetrahedronCollar.hasColour"),
            H("The two colours of the ordered tetrahedron"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text(
                "Each colour selects two ranks of the ordered tetrahedron. " +
                "The two ordinary cuts on its flags use precisely this selection."))),
            DescribeRole.Definition))));
}
