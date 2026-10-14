using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeBcGhostHermitianFormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unrestricted native tensor Hermitian form",
        H("Unrestricted native tensor Hermitian form"),
        Blocks(
            Paragraph(Text("State is literally the native matter Carrier tensor unrestricted exterior bc Fock over Complex. Two real tensor-product lifts construct the pairing from the existing charge-diagonal matter hermitianForm and rotated HplusForm. Their semilinear and linear laws hold for arbitrary finite mixed tensor sums. No form record assumes adjoints, positivity, sector restriction or nondegeneracy. The actual pure-tensor readout multiplies the two native forms, and the resulting form is Hermitian. This is the classical algebraic tensor pairing, not a physical norm or an isometry claim.")),
            Describe.Lean(
                DescribeId.Create("latticebcghosthermitianform-f-tmul"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostHermitianForm.F_tmul"),
                H("F tmul"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compiled declaration supplies the exact native telescope, carriers and conditions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghosthermitianform-f-hermitian"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostHermitianForm.F_hermitian"),
                H("F hermitian"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compiled declaration supplies the exact native telescope, carriers and conditions."))),
                DescribeRole.Theorem))));
}
