using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeDualCosetVirasoroDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complex Dual Contractions and the Actual Conformal Shift",
        H("Complex Dual Contractions and the Actual Conformal Shift"),
        Blocks(
            Paragraph(Text("H is a two-sided inverse of the ORIGINAL complex Gram matrix. u is an arbitrary complex vector with G u=beta. Both finite contractions H beta=u and beta^T H=u^T follow without an additional symmetry assumption on H. The actual original-omega operator equals the original Sugawara mode plus sum_i u_i H_i(m) plus delta(m,0) times one half of u^T G u. Choosing u=H beta supplies this representation without rationality or positivity. These equalities are proved about the action-based moduleL definition.")),
            Paragraph(Text("Classical construction context: Bakalov-Kac, math/0402315v1, section 4.1. The imported Sugawara architecture retains Kalle Kytola's Apache-2.0 attribution and VirasoroProject revision 5ff4245383b2cdd4eea7a0524bc1274c32041eb4. The finite reductions and actual-action connections are native mathematical proofs; no external novelty is asserted.")),
            Describe.Lean(
                DescribeId.Create("latticedualcosetvirasoro-shiftCurrent"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetVirasoro.shiftCurrent"),
                H("shiftCurrent"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration below uses the objects and hypotheses stated above."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticedualcosetvirasoro-halfNorm"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetVirasoro.halfNorm"),
                H("halfNorm"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration below uses the objects and hypotheses stated above."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticedualcosetvirasoro-inverse-dual-contractions"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetVirasoro.inverse_dual_contractions"),
                H("inverse dual contractions"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration below uses the objects and hypotheses stated above."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetvirasoro-moduleL-shift-complex"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetVirasoro.moduleL_shift_complex"),
                H("moduleL shift complex"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration below uses the objects and hypotheses stated above."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetvirasoro-inverse-dual-vector"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetVirasoro.inverse_dual_vector"),
                H("inverse dual vector"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration below uses the objects and hypotheses stated above."))),
                DescribeRole.Theorem))));
}
