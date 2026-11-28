using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StableCategory;

internal sealed class ProductStableLowerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stable category of the seven-triangle face-poset product",
        H("Stable category of the seven-triangle face-poset product"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("product-stable-category-eq-two"),
                DeclarationHandle.Create("D5/S3/Topology/StableCategory/ProductStableLower.product_stable_category_eq_two"),
                H("The product has stable category two"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
                Blocks(Paragraph(Text("The first projection has a section through a fixed face. The retraction survives every ordinary subdivision. A one-piece cover would contract the subdivided factor. Choosing a vertex in the image of each singleton face turns this order-map fence into a contiguity chain. In the subdivided triangular boundary, two distinct original vertices must stay fixed throughout that chain. The explicit two-piece cover at depth two therefore attains the minimum over all depths."))),
                DescribeRole.Theorem))));
}
