using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EntanglementBreaking;

internal sealed class SignMatrixPartialTransposeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        H("Partial transpose of a finite Hermitian sign matrix"),
        Blocks(
            Describe.Lean(DescribeId.Create("eb-signmatrixpartialtranspose-ptbittransform"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixPartialTranspose.ptBitTransform"),
                H("Boolean transformation for output partial transpose"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The output index swap transports each upper entry. If the order reverses, the imaginary sign is complemented and the real sign is preserved. The diagonal and unused lower coordinates are fixed."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("eb-signmatrixpartialtranspose-signcubesample-partialtranspose-quadratic-tail"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixPartialTranspose.signCubeSample_partialTranspose_quadratic_tail"),
                H("Fixed-vector tail after partial transpose"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The Boolean transformation is an involution and preserves uniform measure. Entrywise equality transfers the original quadratic tail with the same constants."))),
                DescribeRole.Theorem))));
}
