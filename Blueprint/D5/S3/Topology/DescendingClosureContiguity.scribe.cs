using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class DescendingClosureContiguityDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/DescendingClosureContiguity.";
    private static AssessedProvenance Provenance => AssessedProvenance.FromRepo(
        LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory"));

    private static DocumentBlock Entry(string id, string declaration, string heading, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration), H(heading),
            StatementSource.WithoutFormula(), Provenance, Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Relative contiguity by descending rank",
        H("Relative contiguity by descending rank"),
        Blocks(
            Entry("rank-interpolation", "exists_relative_contiguity_of_le", "Bounded ranked interpolation",
                "For order maps f and g with g pointwise below f, suppose the source poset has a strictly increasing natural rank bounded by n. " +
                "At stage k use g on vertices of rank less than k and f on the others. " +
                "The stages are order maps from f at index zero to g at index n+1, stay above g, and fix every vertex on which f and g agree. " +
                "The union of adjacent stage images of any chain is a chain."),
            Entry("face-neighborhood", "face_neighborhood_relative_contiguity", "Relative deformation of a face neighborhood",
                "For a complex on a finite vertex type V with decidable equality and a selected vertex set S, take the poset of nonempty faces meeting S. " +
                "Intersection with S is a descending order map. Face cardinality gives a rank, so the identity reaches this map at index card(V)+1 through contiguous order-complex maps fixing every face contained in S."),
            Entry("flag-cover", "two_subsets_cover_face_flags", "Two vertex subsets cover the face flags",
                "If two finite vertex subsets cover V, then each chain of nonempty faces lies entirely in one of their face-poset neighborhoods. " +
                "For a nonempty chain choose a least face by cardinality and a vertex in that face. Every larger face meets the same selected subset."),
            Entry("face-image-contiguity", "faceImage_connected_by_contiguity", "Contiguous vertex maps induce a face-poset contiguity chain",
                "For complexes K and L, let the source vertex type be finite and the target vertex type have decidable equality. " +
                "Suppose f and g map every face of K to a face of L, with the union of the two images also a face of L. " +
                "The union gives a common containing order map of face posets. Applying ranked interpolation from that map to each induced face-image map yields a finite chain of contiguous order-complex maps joining the two induced maps."))));
}
