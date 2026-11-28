using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StableCategory;

internal sealed class RelativeHornCoverDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first-subdivision relative covering number of a simplex horn",
        H("The first-subdivision relative covering number of a simplex horn"),
        Blocks(Describe.Lean(
            DescribeId.Create("simplex-horn-first-relative-cover-number"),
            DeclarationHandle.Create("D5/S3/Topology/StableCategory/RelativeHornCover.isLeast_horn_relative_lower_cover"),
            H("A simplex horn needs exactly one relative piece per facet at the first subdivision"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text("Adjoin a greatest element to the nonempty face poset of a horn in a simplex of dimension at least two. After one chain subdivision, cover by lower sets that contain the entire old region and admit order homotopies into it fixing it pointwise. Cyclic maximal chains in the horn are pairwise disjoint, and the predecessor criterion allows only one of these chains through the new maximum per relative piece. A chart for every horn facet attains the lower bound."))),
            DescribeRole.Theorem))));
}
