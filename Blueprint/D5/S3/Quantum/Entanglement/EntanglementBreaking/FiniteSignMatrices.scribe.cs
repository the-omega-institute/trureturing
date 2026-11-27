using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EntanglementBreaking;

internal sealed class FiniteSignMatricesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        H("Finite Hermitian sign matrices"),
        Blocks(
            Describe.Lean(DescribeId.Create("eb-finitesignmatrices-finitesignmatrix"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignMatrix"),
                H("Hermitian sign matrix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The diagonal vanishes. Each upper entry is a complex number with real and imaginary parts in {−3/5, 3/5}, and the lower entries are its conjugates."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("eb-finitesignmatrices-finitesignmatrix-energy"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignMatrix_energy"),
                H("Deterministic energy of the sign matrix"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Each off-diagonal entry contributes 18/25 to the squared Frobenius norm. Hermiticity turns the sum of entrywise squared moduli into the real trace of the square."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("eb-finitesignmatrices-finitesignsample-conditional"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignSample_conditional"),
                H("The sign matrix construction under three bounds"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The sign choices supply Hermiticity, tracelessness and sufficient energy. The remaining hypotheses impose the Schmidt-restricted quadratic bound and positive semidefiniteness of both trace tests."))),
                DescribeRole.Theorem))));
}
