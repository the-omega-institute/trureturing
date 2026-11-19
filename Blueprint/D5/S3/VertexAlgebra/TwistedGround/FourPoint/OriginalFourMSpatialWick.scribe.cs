using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMSpatialWickDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Spatial Taylor selection of the original simultaneous marked Gaussian",
        H("Spatial Taylor Selection"),
        Blocks(Describe.Lean(DescribeId.Create("fourm-spatial-marked-gaussian"),
            DeclarationHandle.Create(
                "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick.spatial_marked_gaussian"),
            H("Spatial coefficients through the marked Wick recurrence"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("In the recursion the selected occurrence belongs to either "
                + "a singleton or a pair. Its spatial Taylor coefficient acts on that factor, "
                + "leaving the remaining coordinate selections to the remaining marks."))),
            DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fourm-radial-spatial-occupation"),
                DeclarationHandle.Create(
                    "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick.radial_spatial_occupation"),
                H("A native occupation after the simultaneous spatial Taylor coefficient"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a fixed charge on radial A or B, the simultaneous "
                    + "coefficient of the physical Gaussian gives the literal native affine "
                    + "occupation after the four inverse-lowered words."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fourm-physical-product-marked-charge-fiber"),
                DeclarationHandle.Create(
                    "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick.physical_product_marked_charge_fiber"),
                H("Marked charge summands of the actual physical product"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In the actual charge fiber of each physical chart, the "
                    + "relative source signs multiply each occurrence weight and the original "
                    + "period factor multiplies the full sum."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fourm-radial-spatial-sewn-charge"),
                DeclarationHandle.Create(
                    "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick.radial_spatial_sewn_charge"),
                H("Original sewn readout of a marked charge summand"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the native radial nome, the readout includes the "
                    + "original determinant, charge energy and scalar. The period normalization "
                    + "adds the cube of the complementary parameter."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fourm-spatial-coefficient-has-sum"),
                DeclarationHandle.Create(
                    "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick.spatialCoefficient_hasSum"),
                H("Taylor extraction for a normally convergent series"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A summable majorant on a common polydisk lets each coordinate "
                    + "Taylor extraction pass through the infinite sum."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fourm-physical-chart-jet-has-sum"),
                DeclarationHandle.Create(
                    "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick.physical_chart_jet_hasSum"),
                H("Taylor extraction through the physical charge fiber"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Positive definite lattice energy dominates the linear marked "
                    + "charge source on a common external polydisk. The coefficient sum uses the "
                    + "original mod-two charge fiber and period normalization."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fourm-physical-chart-coefficient-overlap"),
                DeclarationHandle.Create(
                    "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick.physical_chart_coefficient_overlap"),
                H("Sector identities of the simultaneous marked Taylor coefficients"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Normal convergence at the marked origin lets Taylor "
                    + "extraction preserve the actual Fourier and quadratic sector identities "
                    + "and the original B-chart period multiplier."))), DescribeRole.Theorem))));
}
