using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StableCategory;

internal sealed class MovingAnchorMixedConeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Moving the anchor across a mixed cone attachment",
        H("Moving the anchor across a mixed cone attachment"),
        Blocks(Describe.Lean(
            DescribeId.Create("moving-anchor-inherited-exact-two-cover"),
            DeclarationHandle.Create("D5/S3/Topology/StableCategory/MovingAnchorMixedCone.moving_anchor_exact_two_cover_of_adjoined_maximum"),
            H("A deformation inside the actual cone base gives an exact categorical two-cover"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text("The first retained region trims coned faces meeting its trace vertices. On the second retained region, an order-map fence keeps each wholly exclusive base face inside the actual cone base. Cone each image around the fixed apex, then insert a terminal anchor spanning the moved faces and delete the apex. Two further ordinary subdivisions give categorical lower sets with the two prescribed old intersections. The homotopy on the second piece may move its old points."))),
            DescribeRole.Theorem))));
}
