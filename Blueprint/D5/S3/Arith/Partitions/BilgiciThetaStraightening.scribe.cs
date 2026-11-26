using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Partitions;

internal sealed class BilgiciThetaStraighteningDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Partitions/BilgiciThetaStraightening.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Fourier/bilgici2026ninecolored");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A four-word span for degree seven.",
        H("A four-word span for degree seven"),
        Blocks(
            Describe.Lean(DescribeId.Create("bilgici-centered-degree-seven-span"),
                DeclarationHandle.Create(Prefix + "centered_degree_seven_span"), H("The centered span"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Every projected word of length seven and centered weight zero belongs to the span of "
                    + "the projections of 5899999, 3777999, 1677899, and 1278999. The induction reduces one "
                    + "multiplicity profile at a time. Local relations express the intermediate base words in "
                    + "the listed four-word family."))), DescribeRole.Theorem))));
}
