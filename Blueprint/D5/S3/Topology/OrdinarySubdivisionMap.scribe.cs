using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class OrdinarySubdivisionMapDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/OrdinarySubdivisionMap.";
    private static AssessedProvenance Provenance => AssessedProvenance.FromRepo(
        LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory"));

    private static DocumentBlock Entry(string id, string declaration, string heading, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration),
            H(heading), StatementSource.WithoutFormula(), Provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Naturality of two face cuts in ordinary subdivision",
        H("Naturality of two face cuts in ordinary subdivision"),
        Blocks(
            Entry("original-support-of-subdivision-map", "originalSupport_image",
                "Transport original supports under ordinary subdivision",
                "Applying a simplicial vertex map to an iterated subdivision sends each original " +
                "support to its image under that map. The map can identify vertices."),
            Entry("two-cut-retained-vertices", "inTwoCutCollar_iterate_iff",
                "Detect the retained vertices through a colour-preserving map",
                "For a colour-preserving simplicial map, a vertex of the third subdivision " +
                "survives both face cuts exactly when its image survives them."),
            Entry("two-cut-original-support", "mem_twoCutImage_support",
                "Compute the support of the two cuts",
                "The nested image flags carry exactly the original vertices of the selected " +
                "colour. Removing empty intersections and identifying repeated entries preserves their union."),
            Entry("two-cut-commutes-with-colour-map", "twoCutImage_iterate",
                "Transport the two-cut image through a colour-preserving map",
                "Intersecting old faces with one colour, deleting empty entries, and taking " +
                "the successive images of flags commute with a colour-preserving simplicial map."))));
}
