using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StableCategory;

internal sealed class ShellingExactExtensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact categorical extension across a shelling step",
        H("Exact categorical extension across a shelling step"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exact-extension-shelling"),
                DeclarationHandle.Create("D5/S3/Topology/StableCategory/ShellingExactExtension.exact_extension_shelling"),
                H("Attachment along a union of facets"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
                Blocks(
                    Paragraph(Text("A prescribed categorical two-cover on the retained triangulation extends across one shelling simplex with exact old intersections at the third ordinary barycentric subdivision. Each resulting piece is full and contracts by finite contiguity in the common ambient.")),
                    Paragraph(Text("The mixed case uses the set of omitted vertices of the facets in the second piece. It may lie in both old pieces. The two regions at the second subdivision only need to cover vertices. The final subdivision recovers both the cover and the prescribed intersections."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exact-extension-elementary-expansion"),
                DeclarationHandle.Create("D5/S3/Topology/StableCategory/ShellingExactExtension.exact_extension_elementary_expansion"),
                H("Exact retention across an elementary expansion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
                Blocks(Paragraph(Text("The shelling theorem applies to the horn of the simplex in an elementary expansion. Connectedness of the expanded complex joins the terminal constants in the monochromatic case."))),
                DescribeRole.Theorem))));
}
