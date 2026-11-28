using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StableCategory;

internal sealed class OrderComplexNullhomotopyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Order-map fences from realization nullhomotopies",
        H("Order-map fences from realization nullhomotopies"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("order-map-fence-from-realization-nullhomotopy"),
                DeclarationHandle.Create("D5/S3/Topology/StableCategory/OrderComplexNullhomotopy.order_map_fence_of_nullhomotopy"),
                H("Fences after sufficiently many maximum projections"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
                Blocks(Paragraph(Text("If the realization of an order map is nullhomotopic, composing with enough iterated chain-maximum projections gives an order map joined to a constant by a finite fence of pointwise comparisons. The iterated maximum is supported in each original carrier. Taking the maximum of an image chain commutes with the given order map, so the first map of the fence is the exact composite."))),
                DescribeRole.Theorem))));
}
