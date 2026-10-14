using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeSugawaraHermitianDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native finite neutral Sugawara adjoints",
        H("Native finite neutral Sugawara adjoints"),
        Blocks(
            Paragraph(Text("The original matter Carrier includes all finite charge families and all oscillator polynomials. hermitianForm and all integer neutral adjoints, including the real charge-dependent zero mode, are directly reused from LatticeChargedFockForms. Both inverse-Gram equations against the actual integral real symmetric Gram are explicit. They prove inverse symmetry and entrywise reality without any positivity or signature assumption. The actual normal-summand supports of both inputs lie in one common finite symmetric integer interval. The zero-zero term uses the native zero-mode Heisenberg commutator. Only finite sums are reindexed. These are classical inverse-Gram oscillator identities, not full charged PCT or a no-ghost theorem.")),
            Describe.Lean(
                DescribeId.Create("latticesugawarahermitian-inverse-gram-symmetric"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeSugawaraHermitian.inverse_gram_symmetric"),
                H("inverse gram symmetric"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compiled declaration supplies the exact native telescope, carriers and conditions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticesugawarahermitian-inverse-gram-real"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeSugawaraHermitian.inverse_gram_real"),
                H("inverse gram real"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compiled declaration supplies the exact native telescope, carriers and conditions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticesugawarahermitian-sugawara-adjoint"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeSugawaraHermitian.sugawara_adjoint"),
                H("sugawara adjoint"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compiled declaration supplies the exact native telescope, carriers and conditions."))),
                DescribeRole.Theorem))));
}
