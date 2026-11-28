using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StableCategory;

internal sealed class MaximalChainCoverExtensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Extending categorical covers across maximal elements",
        H("Extending categorical covers across maximal elements"),
        Blocks(Describe.Lean(
            DescribeId.Create("relative-two-cover-by-maximal-lower-chains"),
            DeclarationHandle.Create("D5/S3/Topology/StableCategory/MaximalChainCoverExtension.exists_relative_two_cover_of_maximal_lower_chains"),
            H("A covering condition on maximal lower chains extends two prescribed categorical pieces"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text("Delete a selected set of maximal elements of a finite poset. Suppose two categorical lower sets of chains cover the chains that avoid those elements. For each deleted maximum choose a strict predecessor on each side. Every maximal lower chain at that maximum must belong to one of the prescribed pieces and contain the predecessor chosen for that side. The proof extends each piece with the chains on which adjoining the chosen predecessor and then removing the maximum retracts the chain into that piece. The two comparisons and the retraction fix the old chains, so the extended cover has the prescribed old intersections."))),
            DescribeRole.Theorem))));
}
