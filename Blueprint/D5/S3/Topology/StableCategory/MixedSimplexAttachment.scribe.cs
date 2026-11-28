using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StableCategory;

internal sealed class MixedSimplexAttachmentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact categorical transport across a mixed simplex attachment",
        H("Exact categorical transport across a mixed simplex attachment"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mixed-exact-transport"),
                DeclarationHandle.Create("D5/S3/Topology/StableCategory/MixedSimplexAttachment.mixed_exact_transport"),
                H("Transport with exact old intersections"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
                Blocks(Paragraph(Text("When the two old categorical pieces meet an attaching simplex in the prescribed horns and satisfy the exterior incidence conditions, the two full regions at depth two contract in the common ambient. One further ordinary subdivision gives a two-piece cover with the prescribed old intersections exactly."))),
                DescribeRole.Theorem))));
}
