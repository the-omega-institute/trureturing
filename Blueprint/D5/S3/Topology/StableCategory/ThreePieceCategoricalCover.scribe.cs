using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StableCategory;

internal sealed class ThreePieceCategoricalCoverDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three categorical pieces in dimensions four and five",
        H("Three categorical pieces in dimensions four and five"),
        Blocks(Describe.Lean(
            DescribeId.Create("three-pieces-of-contractible"),
            DeclarationHandle.Create("D5/S3/Topology/StableCategory/ThreePieceCategoricalCover.three_pieces_of_contractible"),
            H("The contractible three-piece bound"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(
                Paragraph(Text("A finite simplicial complex of dimension at most five with contractible realization admits three categorical subcomplexes at one ordinary barycentric subdivision depth.")),
                Paragraph(Text("The first two face ranks form a graph. In each round the graph parameter advances by four subdivisions while the ambient advances by three. The other region factors through a complex with four face ranks, including isolated vertices for exceptional components. Contractibility supplies a nullhomotopy of its final parameter map. Two categorical regions for that map pull back to collars, which together with the categorical graph collar cover at a common depth."))),
            DescribeRole.Theorem))));
}
