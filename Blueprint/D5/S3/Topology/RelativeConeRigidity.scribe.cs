using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class RelativeConeRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All-depth rigidity of the base of a relative cone",
        H("All-depth rigidity of the base of a relative cone"),
        Blocks(Describe.Lean(
            DescribeId.Create("relative-cone-base-rigidity"),
            DeclarationHandle.Create(
                "D5/S3/Topology/RelativeConeRigidity.relative_cone_all_depth_obstruction"),
            H("The retained base vertices are fixed under contiguity"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text(
                "Suppose every base vertex lies in two distinct facets and the intersection of its incident facets is that vertex. " +
                "After a positive number of relative subdivisions, each retained base facet has a unique exterior tip, distinct from the tips of other facets. " +
                "The tip distinction and the facet intersections give the maximal-face criterion. " +
                "Every contiguity chain starting from the same-depth inclusion after any further ordinary subdivision fixes the retained base vertices."))),
            DescribeRole.Theorem))));
}
