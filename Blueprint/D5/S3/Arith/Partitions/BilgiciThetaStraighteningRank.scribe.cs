using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Partitions;

internal sealed class BilgiciThetaStraighteningRankDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Partitions/BilgiciThetaStraighteningRank.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Fourier/bilgici2026ninecolored");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A well-founded rank for re-pairing.",
        H("A well-founded rank for re-pairing"),
        Blocks(
            Describe.Lean(DescribeId.Create("bilgici-repair-identity"),
                DeclarationHandle.Create(Prefix + "rePair_identity"), H("The two re-pairings"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Solving a theta relation for the original pairing expresses its class in terms of two "
                    + "re-paired words."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bilgici-repair-center"),
                DeclarationHandle.Create(Prefix + "rePair_center"), H("Centered weight under re-pairing"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The re-pairings preserve the sum of the squares of the signed labels."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bilgici-precedes-wf"),
                DeclarationHandle.Create(Prefix + "precedes_wf"), H("Well-founded descent"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The primary rank is the sum of powers of ten of the multiplicities. The secondary rank "
                    + "compares residue data after common nonzero scaling. Lexicographic order on these two "
                    + "natural numbers is well founded."))), DescribeRole.Theorem))));
}
