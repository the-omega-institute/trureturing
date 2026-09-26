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
            StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Finite orthogonal syndrome copies preserve the complete logical matrix. The decoder here is support-restricted; complete-positive extension and global bundle statements are not asserted by these declarations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("orthogonal-syndrome-recovery"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/OrthogonalSyndromeDecoding.orthogonal_syndrome_recovery"),
                H("orthogonal syndrome recovery"),
            StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Finite orthogonal syndrome copies preserve the complete logical matrix. The decoder here is support-restricted; complete-positive extension and global bundle statements are not asserted by these declarations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("trace-one-syndrome-recovery"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/OrthogonalSyndromeDecoding.trace_one_syndrome_recovery"),
                H("trace one syndrome recovery"),
            StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Finite orthogonal syndrome copies preserve the complete logical matrix. The decoder here is support-restricted; complete-positive extension and global bundle statements are not asserted by these declarations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("syndrome-transport-orthogonal"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/OrthogonalSyndromeDecoding.syndrome_transport_orthogonal"),
                H("syndrome transport orthogonal"),
            StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Finite orthogonal syndrome copies preserve the complete logical matrix. The decoder here is support-restricted; complete-positive extension and global bundle statements are not asserted by these declarations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("transported-syndrome-recovery"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/OrthogonalSyndromeDecoding.transported_syndrome_recovery"),
                H("transported syndrome recovery"),
            StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Finite orthogonal syndrome copies preserve the complete logical matrix. The decoder here is support-restricted; complete-positive extension and global bundle statements are not asserted by these declarations."))),
                DescribeRole.Theorem))));
}
