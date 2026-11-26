using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Golomb;

internal sealed class NotikSubtreeReplayDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Golomb/NotikSubtreeReplay.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        GeneralHeader("D5/S3/Combinatorics/Golomb/NotikSubtreeReplay",
            "Checked subtree certificates compose in branch order.",
            "kernel-replayed-certificate"),
        H("Composing Golomb subtree certificates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golomb-subtree-certificate"),
                DeclarationHandle.Create(Prefix + "SubtreeCertificate"),
                H("A subtree passes both checks at its inherited path"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A certificate for a target, static rows, relation witnesses, inherited path, "
                    + "tree and leaf table gives two equations. The bound check returns true and "
                    + "the equality check consumes the full table, returning an empty remainder."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("golomb-subtree-branch"),
                DeclarationHandle.Create(Prefix + "branch"),
                H("Child certificates compose at a branch"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If the branch relation has a witness, the negative branch row extends the inherited "
                    + "path for the left child and the positive row extends it for the right child. "
                    + "Given certificates for the two children on these paths, the parent has a "
                    + "certificate with the left leaf table followed by the right leaf table. "
                    + "Appending entries to a successfully covered table leaves the appended "
                    + "entries untouched, so the left check hands exactly the right table to the right check."))),
                DescribeRole.Theorem)), []));
}
