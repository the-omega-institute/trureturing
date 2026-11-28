using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StableCategory;

internal sealed class ProductRigidCoresDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordinary category of a product of finite face posets",
        H("Ordinary category of a product of finite face posets"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("least-categorical-cover"),
                DeclarationHandle.Create("D5/S3/Topology/StableCategory/ProductRigidCores.least_categorical_cover"),
                H("The seven-triangle face-poset product has ordinary category three"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
                Blocks(Paragraph(Text("Each factor admits three strongly collapsible pieces, obtained by deleting one boundary edge and its only incident triangle. Each face is retained in at least two pieces, so the three corresponding rectangles cover the product. In any two-colouring of the nine pairs of exceptional triangles, a single colour forces a full copy of the rigid boundary in one coordinate slice. The projection of a categorical contraction would contract that boundary. The calculation concerns lower sets of the original product poset."))),
                DescribeRole.Theorem))));
}
