using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StableCategory;

internal sealed class TrimmedAnchorMixedConeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exclusive-vertex anchor for a relative cone cover",
        H("An exclusive-vertex anchor for a relative cone cover"),
        Blocks(Describe.Lean(
            DescribeId.Create("trimmed-anchor-exact-categorical-cover"),
            DeclarationHandle.Create("D5/S3/Topology/StableCategory/TrimmedAnchorMixedCone.trimmed_anchor_exact_two_cover"),
            H("A full first trace and an anchor on the other trace give an exact categorical two-cover"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text("Suppose the first trace on the cone base is full. Assign each exterior face with a vertex in that trace to the first piece. Trim to its first-trace vertices and then remove the apex. On the other side, adjoin one vertex that spans every base face supported entirely outside the first trace, then remove the apex. The resulting point cover preserves each old region pointwise along its relative order fence. The two regions become a categorical lower cover after two ordinary subdivisions, with the prescribed old intersections."))),
            DescribeRole.Theorem))));
}
