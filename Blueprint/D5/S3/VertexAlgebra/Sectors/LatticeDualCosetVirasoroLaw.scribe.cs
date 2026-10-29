using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeDualCosetVirasoroLawDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Universal Dual-Coset Virasoro Law",
        H("Universal Dual-Coset Virasoro Law"),
        Blocks(
            Paragraph(Text("For every finite rank and all integer m,n, both original inverse-Gram equations imply [moduleL_m,moduleL_n]=(m-n)moduleL_(m+n)+delta(m+n,0) rank(D)(m^3-m)/12 times identity. No rational shift, positive Gram or auxiliary inverse is required. The accepted original Virasoro, current and Heisenberg laws are used. The current correction contributes m u^T G u at m+n=0; since m-n=2m, the constant half-norm shift is exactly absorbed into moduleL_0.")),
            Paragraph(Text("Classical construction context: Bakalov-Kac, math/0402315v1, section 4.1. The imported Sugawara architecture retains Kalle Kytola's Apache-2.0 attribution and VirasoroProject revision 5ff4245383b2cdd4eea7a0524bc1274c32041eb4. The finite reductions and actual-action connections are native mathematical proofs; no external novelty is asserted.")),
            Describe.Lean(
                DescribeId.Create("latticedualcosetvirasorolaw-modulel-virasoro"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeDualCosetVirasoroLaw.moduleL_virasoro"),
                H("moduleL virasoro"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All integer actual original-omega modes obey Virasoro with central charge rank(D), including rank zero, under the two original inverse equations alone."))),
                DescribeRole.Theorem))));
}
