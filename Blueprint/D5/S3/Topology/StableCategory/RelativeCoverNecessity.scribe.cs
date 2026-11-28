using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StableCategory;

internal sealed class RelativeCoverNecessityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact relative criterion for extending two categorical pieces",
        H("An exact relative criterion for extending two categorical pieces"),
        Blocks(Describe.Lean(
            DescribeId.Create("relative-two-cover-exact-predecessor-criterion"),
            DeclarationHandle.Create("D5/S3/Topology/StableCategory/RelativeCoverNecessity.exists_relative_two_cover_iff"),
            H("Relative extension is equivalent to hitting the maximal lower chains"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text("Let two categorical lower regions cover the chains avoiding a chosen set of maximal elements. Assume each chosen maximum has a strict predecessor. An extension at the first chain subdivision, with the prescribed old intersections and order homotopies fixing them, exists exactly when one predecessor per maximum and per side suffices to hit every maximal lower chain in an eligible old region. To prove necessity, follow the singleton of a chosen maximum through a relative homotopy. Its first increase must add an element common to all maximal lower chains assigned to that side, because the homotopy fixes those old chains. The preceding extension theorem supplies the converse."))),
            DescribeRole.Theorem))));
}
