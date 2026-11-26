using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class BarycentricGraphDistanceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Graph distance under barycentric subdivision",
        H("Graph distance under barycentric subdivision"),
        Blocks(Describe.Lean(
            DescribeId.Create("barycentric-graph-distance-doubling"),
            DeclarationHandle.Create(
                "D5/S3/Topology/BarycentricGraphDistance.subdivision_edist_eq_two_mul"),
            H("Subdivision doubles the distance between subcomplexes"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text(
                "The extended distance between the two subdivided subcomplexes is twice their original vertex-set distance. " +
                "Bisecting a walk gives one inequality. A shortest walk in the subdivision alternates inclusions. " +
                "Vertices chosen in consecutive inclusion minima share the intervening face and give the reverse inequality. " +
                "The extended distance also treats empty endpoint sets and disconnected components."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("barycentric-full-neighborhood"),
            DeclarationHandle.Create(
                "D5/S3/Topology/BarycentricGraphDistance.mem_full_subcomplex_of_face_walk"),
            H("A full neighborhood persists at twice its radius"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text(
                "Suppose a full subcomplex contains every original vertex within distance D of a given subcomplex. " +
                "Then it contains each face reached from the given subcomplex by a walk of at most 2D edges in the subdivision graph. " +
                "The first inclusion minimum of a shortest walk supplies a vertex close enough to the endpoint for every vertex of the starting face to reach the given subcomplex in D steps."))),
            DescribeRole.Theorem))));
}
