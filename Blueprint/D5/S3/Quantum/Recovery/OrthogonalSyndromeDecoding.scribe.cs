using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class OrthogonalSyndromeDecodingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite orthogonal syndrome copies preserve the complete logical matrix. The decoder here is support-restricted; complete-positive extension and global bundle statements are not asserted by these declarations.",
        H("OrthogonalSyndromeDecoding"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("decoding-syndrome-block"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/OrthogonalSyndromeDecoding.decoding_syndrome_block"),
                H("decoding syndrome block"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Finite orthogonal syndrome copies preserve the complete logical matrix. The decoder here is support-restricted; complete-positive extension and global bundle statements are not asserted by these declarations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("orthogonal-syndrome-recovery"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/OrthogonalSyndromeDecoding.orthogonal_syndrome_recovery"),
                H("orthogonal syndrome recovery"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Finite orthogonal syndrome copies preserve the complete logical matrix. The decoder here is support-restricted; complete-positive extension and global bundle statements are not asserted by these declarations."))),
                DescribeRole.Theorem))));
}
