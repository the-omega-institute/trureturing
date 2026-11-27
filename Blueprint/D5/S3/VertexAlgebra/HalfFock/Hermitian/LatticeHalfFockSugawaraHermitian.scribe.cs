using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.HalfFock.Hermitian;

internal sealed class LatticeHalfFockSugawaraHermitianDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hermitian adjoints for the original half-current normal products",
        H("Adjoints of the Half-Current Normal Products"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("normal-pair-adjoint"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockSugawaraHermitian.normalPair_adjoint"),
                H("Normal-ordered pair"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Half-current adjoints reverse the two operators of a normal pair. "
                    + "The adjoint acts by the same normal pair at the reflected indices −j−1 and −k−1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normal-sum-adjoint"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockSugawaraHermitian.normalSum_adjoint"),
                H("Normal sum at opposite mode"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The pointwise finite-support theorem writes each normal sum on a common "
                    + "finite interval containing both supports. The reflection j ↦ −j−1 permutes this interval. "
                    + "The normal-pair identity then gives the adjoint of the sum at the opposite mode."))),
                DescribeRole.Theorem))));
}
