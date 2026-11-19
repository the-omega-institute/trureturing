using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMSewnProjectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four original occupation sums from one native sewn Gaussian readout",
        H("Sewn Occupation Projection"),
        Blocks(Describe.Lean(DescribeId.Create("fourm-boxed-four-sewn-projection"),
            DeclarationHandle.Create(
                "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSewnProjection.boxed_four_sewn_projection"),
            H("Joint polynomial readout in the original four occupation sums"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The native Gaussian evaluates the product of the four boxed "
                + "oscillator polynomials in their original native order. Each supported tuple "
                + "has its original sewn charge factor and four factorial weights."))),
            DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fourm-radial-spatial-four-occupation"),
                DeclarationHandle.Create(
                    "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSewnProjection.radial_spatial_four_occupation"),
                H("Simultaneous spatial coefficient of the native charge summand"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In radial charts A and B, the marked spatial Taylor coefficient of a "
                    + "fixed charge equals the four original occupation sums after the slotwise inverse "
                    + "transforms. The native nome relation is an explicit hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fourm-radial-sector-four-occupation"),
                DeclarationHandle.Create(
                    "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSewnProjection.radial_sector_four_occupation"),
                H("Convergent four-occupation projection of a radial sector"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In charts A and B the Taylor coefficient of the full "
                    + "physical sector equals the convergent charge sum of the literal native "
                    + "four-occupation readout at the stated nome."))), DescribeRole.Theorem))));
}
