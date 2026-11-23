using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Partitions;

internal sealed class BilgiciThetaStraighteningRowsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Partitions/BilgiciThetaStraighteningRows.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Fourier/bilgici2026ninecolored");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local reductions of degree-seven multiplicities.",
        H("Local reductions of degree-seven multiplicities"),
        Blocks(
            Describe.Lean(DescribeId.Create("bilgici-reduce3211"),
                DeclarationHandle.Create(Prefix + "reduce3211"), H("The multiplicity profile 3, 2, 1, 1"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("After normalizing the triple label, the centered relation either gives a smaller re- "
                    + "pairing or reduces to the base word with multiplicities 3, 2, 1, 1."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bilgici-reduce31111"),
                DeclarationHandle.Create(Prefix + "reduce31111"), H("The multiplicity profile 3, 1, 1, 1, 1"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The normalized triple with four distinct single labels has a centered re-pairing of "
                    + "smaller rank."))), DescribeRole.Theorem))));
}
