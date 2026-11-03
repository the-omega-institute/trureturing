using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeDualCosetConformalShiftDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Normal-Current Boundary Expansion",
        H("Actual Normal-Current Boundary Expansion"),
        Blocks(
            Paragraph(Text("The actual current is H_i(m)+beta_i delta(m,0). At conformal index m the normal-product coefficient is m+1. Expanding its two vectorwise finite halves gives the original quadratic coefficient plus beta_j H_i(m), beta_i H_j(m), and beta_i beta_j delta(m,0) times identity. In the negative half the right shift occurs at offset -m-1 for m<0. In the other half the first shift occurs at offset zero and the other at offset m for m>=0. The constant term occurs once at m=0. No ambient translation invariance or auxiliary Gram inverse is used.")),
            Paragraph(Text("Classical construction context: Bakalov-Kac, math/0402315v1, section 4.1. The imported Sugawara architecture retains Kalle Kytola's Apache-2.0 attribution and VirasoroProject revision 5ff4245383b2cdd4eea7a0524bc1274c32041eb4. The finite reductions and actual-action connections are native mathematical proofs; no external novelty is asserted.")),
            Describe.Lean(
                DescribeId.Create("latticedualcosetconformalshift-normal-current-shift"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformalShift.normal_current_shift"),
                H("normal current shift"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The normal coefficient at m+1 equals its unshifted value plus beta_j H_i(m), beta_i H_j(m), and beta_i beta_j delta(m,0) times identity. All sums are vectorwise finite."))),
                DescribeRole.Theorem))));
}
