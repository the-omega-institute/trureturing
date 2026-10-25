using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.HalfFock;
internal sealed class ActualMobiusChargedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original charged special-conformal base", H("Charged L1 base"), Blocks(
        Describe.Lean(DescribeId.Create("actual-mobius-charged-l1-base"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/HalfFock/ActualMobiusCharged.charged_l1_coefficient"),
            H("Charged special-conformal coefficient base"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
            Blocks(Paragraph(Text("For every original D, determinant-unit proof hu, signed charge a and integer e, the commutator of tensorL at mode 1 with chargedCoefficient at e equals ((e-2)/2+B(a,a)) times chargedCoefficient at e-2, as an endomorphism of the original actual tensor module. The proof expands the pointwise finite quadratic sum, retains the j=0 boundary, contracts both inverse Gram identities and consumes the original physical seed identity. The full-source proof uses this charged base. No positivity, rank restriction or homogeneous target is assumed."))), DescribeRole.Theorem))));
}
