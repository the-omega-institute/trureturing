using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeBcGhostHermitianAdjointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Corrected individual original BRST summand adjoints",
        H("Corrected individual original BRST summand adjoints"),
        Blocks(
            Paragraph(Text("Every statement uses the unrestricted original State. Pi is the actual tensor lift of occupation parity, not energy rotation. Both Gram inverse equations remain explicit. The actual N branch changes at n>=-1. Reversing middle modes -1,0,1 gives the original commutator [G(-n),C(n)]=n C(0). The individual A(n) transpose retains -(n*d0(n)/2) F(Pi(x),C(0)y), where d0 is one exactly on that middle interval. Individual uncorrected skew-adjointness is not asserted. This is the classical graded transpose calculation with the exact native normal-order correction.")),
            Describe.Lean(
                DescribeId.Create("latticebcghosthermitianadjoint-f-m"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostHermitianAdjoint.F_M"),
                H("F M"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compiled declaration supplies the exact native telescope, carriers and conditions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghosthermitianadjoint-f-g"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostHermitianAdjoint.F_G"),
                H("F G"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compiled declaration supplies the exact native telescope, carriers and conditions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghosthermitianadjoint-f-c"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostHermitianAdjoint.F_C"),
                H("F C"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compiled declaration supplies the exact native telescope, carriers and conditions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghosthermitianadjoint-f-a"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostHermitianAdjoint.F_A"),
                H("F A"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compiled declaration supplies the exact native telescope, carriers and conditions."))),
                DescribeRole.Theorem))));
}
