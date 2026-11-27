using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class ConnectedCategoryGraftDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordinary category of a connected finite-space graft",
        H("Ordinary category of a connected finite-space graft"),
        Blocks(Describe.Lean(
            DescribeId.Create("categorical-graft-cover"),
            DeclarationHandle.Create(
                "D5/S3/Topology/ConnectedCategoryGraft.hasCategoricalCover_graft_iff"),
            H("The exact categorical cover number of the graft"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text(
                "Glue the height-one poset with two minima and m common maxima to a connected poset at a shared minimal point. " +
                "The graft has a categorical lower cover with n pieces exactly when the original poset has such a cover and m is at most n. " +
                "Each principal lower set of the height-one poset contracts to the shared point while fixing it. " +
                "These contractions extend a cover of the original poset to the union. " +
                "Any piece containing two new maxima would contract a retract whose identity is isolated among comparable maps, so the maxima require distinct pieces."))),
            DescribeRole.Theorem))));
}
