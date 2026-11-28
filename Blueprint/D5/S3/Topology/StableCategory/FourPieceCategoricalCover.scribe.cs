using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StableCategory;

internal sealed class FourPieceCategoricalCoverDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four categorical pieces from two ranked regions",
        H("Four categorical pieces from two ranked regions"),
        Blocks(Describe.Lean(
            DescribeId.Create("four-pieces-of-two-categorical-colours"),
            DeclarationHandle.Create("D5/S3/Topology/StableCategory/FourPieceCategoricalCover.four_pieces_of_two_categorical_colours"),
            H("A common-depth categorical cover"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(
                Paragraph(Text("Suppose the vertices split into two induced subcomplexes, each properly coloured with four ranks, whose realization inclusions are nullhomotopic in the connected ambient complex. Some ordinary subdivision of the ambient has a cover by four subcomplexes with categorical inclusions.")),
                Paragraph(Text("Take the relative two-piece covers at the maximum of their two depths and pull them back along the subdivided face-intersection maps. The contractions stay in the ambient subdivision at the resulting common depth."))),
            DescribeRole.Theorem))));
}
