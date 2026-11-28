using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StableCategory;

internal sealed class ExactCategoricalExtensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact categorical extensions",
        H("Exact categorical extensions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exact-two-piece-extension"),
                DeclarationHandle.Create("D5/S3/Topology/StableCategory/ExactCategoricalExtension.exact_two_piece_extension"),
                H("Two pieces with a categorical union"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
                Blocks(Paragraph(Text("The retained complex is full. When the second old piece can be joined with the entire attachment in a categorical subcomplex, one ordinary barycentric subdivision gives two categorical pieces with their exact prescribed intersections on the retained complex."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exact-three-piece-extension"),
                DeclarationHandle.Create("D5/S3/Topology/StableCategory/ExactCategoricalExtension.exact_three_piece_extension"),
                H("Three pieces for a categorical attachment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
                Blocks(Paragraph(Text("When the attachment is separately categorical, two pieces retain the prescribed intersections and a third piece is disjoint from the retained subdivision."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exact-extension-of-full-cover"),
                DeclarationHandle.Create("D5/S3/Topology/StableCategory/ExactCategoricalExtension.exact_extension_of_full_cover"),
                H("Prescribing intersections of a full cover"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
                Blocks(Paragraph(Text("If full categorical pieces contain the corresponding pieces of a prescribed old cover, intersect with their vertex sets after one ordinary subdivision. The resulting categorical cover has the prescribed intersections."))),
                DescribeRole.Theorem))));
}
