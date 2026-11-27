using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class RelativeDerivedContiguityDocument : IScribeDocumentDefinition
{
    private static AssessedProvenance Provenance => AssessedProvenance.FromRepo(
        LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory"));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Relative derived subdivision and simplicial contiguity",
        H("Relative derived subdivision and simplicial contiguity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("relative-derived-complex"),
                DeclarationHandle.Create("D5/S3/Topology/RelativeDerivedContiguity.relativeDerived"),
                H("The relative derived complex"), StatementSource.WithoutFormula(), Provenance,
                Blocks(Paragraph(Text(
                    "Use the disjoint union of the old vertex labels and the faces of K outside A. " +
                    "A nonempty finite set of these labels is a face when its old labels, if nonempty, form a face of A, " +
                    "its outside faces form an inclusion chain, and every outside face contains all its old labels. " +
                    "Taking a nonempty subset preserves these three conditions."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("relative-subdivision-contiguity"),
                DeclarationHandle.Create("D5/S3/Topology/RelativeDerivedContiguity.relative_subdivision_preserves_contiguity"),
                H("Contiguity after relative derived subdivision"), StatementSource.WithoutFormula(), Provenance,
                Blocks(Paragraph(Text(
                    "Let K and L be complexes on vertex types V and W, with V finite and W having decidable equality. " +
                    "Assume A is contained in K and every face of K or L whose vertices lie in A or B, respectively, belongs to that base. " +
                    "For each vertex of K, both vertex maps f and g preserve and reflect membership in the base, and the union of their images of each face of K is a face of L. " +
                    "Then a finite simplicial contiguity chain joins the induced maps on the relative derived complexes. " +
                    "Each induced map sends old labels by the original vertex map and outside faces to their images outside B. " +
                    "The proof uses the union of the two face images as a common exterior map, interpolates the exterior by face cardinality while holding the base map fixed, and changes the base map once at the common exterior map. " +
                    "The retained base is full, and each intermediate map sends base and exterior vertices to the corresponding parts of the target. " +
                    "Each adjacent step therefore satisfies the hypotheses for another relative subdivision."))), DescribeRole.Theorem))));
}
