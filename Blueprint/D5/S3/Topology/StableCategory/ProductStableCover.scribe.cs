using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StableCategory;

internal sealed class ProductStableCoverDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two categorical pieces for the seven-triangle face-poset product",
        H("Two categorical pieces for the seven-triangle face-poset product"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("product-two-after-two-subdivisions"),
                DeclarationHandle.Create("D5/S3/Topology/StableCategory/ProductStableCover.product_two_after_two_subdivisions"),
                H("Two categorical lower sets after two ordinary subdivisions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
                Blocks(Paragraph(Text("Deleting the three up-beat boundary edges in each factor leaves a 484-point product core. A finite search supplies a partition and two coordinate trajectories for each core point. The Lean kernel checks that each row is monotone within its colour, starts at the inclusion, ends at a constant, and changes by six alternating pointwise comparisons. Pulling back along the beat retraction and applying the ordinary subdivision cover construction gives the two lower sets."))),
                DescribeRole.Theorem))));
}
