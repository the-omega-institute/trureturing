using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMIdentityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Jacobi on the Original Rank 24 Twisted Module",
        H("Jacobi on the Original Rank 24 Twisted Module"),
        Blocks(Describe.Lean(DescribeId.Create("original-fourm-jacobi"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMIdentity.original_fourM_jacobi"),
            H("The original three twisted input Jacobi identity"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The A and D boundary comparison joins the A and B comparison on the real overlap. The Laurent selectors eliminate every detector monomial of a different degree. The resulting sector identity gives the original vector Jacobi relation for every signed integer mode triple and all three negative parity inputs."))),
            DescribeRole.Theorem))));
}
