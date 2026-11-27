using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EntanglementBreaking;

internal sealed class SignMatrixPartialTransposeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Output partial transpose preserves the Hermitian sign matrix distribution.",
        H("Partial transpose of a finite Hermitian sign matrix"),
        Blocks(
            Describe.Lean(DescribeId.Create("eb-signmatrixpartialtranspose-ptbittransform"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixPartialTranspose.ptBitTransform"),
                H("Boolean transformation for output partial transpose"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The output index swap transports each upper entry. If the order reverses, the imaginary sign is complemented and the real sign is preserved. The diagonal and unused lower coordinates are fixed."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("eb-signmatrixpartialtranspose-signcubesample-partialtranspose-quadratic-tail"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixPartialTranspose.signCubeSample_partialTranspose_quadratic_tail"),
                H("Fixed-vector tail after partial transpose"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The Boolean transformation is an involution and preserves uniform measure. Entrywise equality transfers the original quadratic tail with the same constants."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("eb-signmatrixpartialtranspose-ptindex"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixPartialTranspose.PTIndex"),
                H("Ptindex"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The input and output indices for the square bipartite matrix are a pair in Fin d times Fin d."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("eb-signmatrixpartialtranspose-ptlt"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixPartialTranspose.ptLt"),
                H("Pt lt"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Order the pairs by their images under the standard Fin product equivalence."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("eb-signmatrixpartialtranspose-ptlt-decidable"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixPartialTranspose.ptLt_decidable"),
                H("Pt lt decidable"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Decide this comparison in the resulting finite linear order."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("eb-signmatrixpartialtranspose-ptcross"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixPartialTranspose.ptCross"),
                H("Pt cross"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Exchange the output coordinates between the two product indices while holding their input coordinates fixed."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("eb-signmatrixpartialtranspose-partialtranspose-signcubesample"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixPartialTranspose.partialTranspose_signCubeSample"),
                H("Partial transpose sign cube sample"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Taking the output partial transpose of the sample equals evaluating the sample at the transformed Boolean assignment."))),
                DescribeRole.Theorem))));
}
