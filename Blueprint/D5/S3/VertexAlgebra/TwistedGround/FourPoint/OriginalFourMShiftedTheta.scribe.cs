using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMShiftedThetaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shifted theta of the original rank-24 charge sectors",
        H("Source transformation"), Blocks(
        Describe.Lean(DescribeId.Create("original-fourm-shifted-quadratic-phase-reducecharge"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.quadratic_phase_reduceCharge"),
            H("The quadratic sign"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("On the class of the original Gram image of an integral charge, the doubled Gram quadratic phase equals the original mod-two quadratic sign."))),
            DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("original-fourm-shifted-pairing-phase-reducecharge"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.pairing_phase_reduceCharge"),
            H("The pairing sign"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The pairing phase of two original Gram images equals the original mod-two Fourier sign."))),
            DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("original-fourm-shifted-chargetheta-real-s"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.chargeTheta_real_S"),
            H("Rank-24 real-source inversion"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The exact finite sum has the original Fourier signs. Its normalization is the inverse of two to the twelfth power times the inverse twelfth power of the period factor. Its inverse source multiplier is the exponential of minus pi times the imaginary unit times the doubled Gram quadratic form divided by the period."))),
            DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("original-fourm-shifted-chargetheta-eq-charge-sum"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.chargeTheta_eq_charge_sum"),
            H("The integral charge series"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The literal sector is the sum over integral charges of the specified reduction. Its quadratic energy is half the original Gram norm and its linear source uses the original Gram form."))),
            DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("original-fourm-shifted-chargetheta-s"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.chargeTheta_S"),
            H("Forward rank-24 inversion"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The forward law evaluates theta at minus the reciprocal period and the source divided by the period. Its coefficient is the twelfth power of minus the imaginary unit times the period, multiplied by the exponential of the doubled Gram source quadratic and the normalized original finite Fourier transform."))),
            DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("original-fourm-shifted-chargetheta-t"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.chargeTheta_T"),
            H("Translation of the theta argument"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Adding one to the theta argument leaves the complex source fixed and multiplies the sector by its original quadratic sign."))),
            DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("original-fourm-shifted-original-finite-weil"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.original_finite_weil"),
            H("Rank-24 finite Weil relations"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The actual doubled Gram Fourier operator squares to the identity, and its composite with the quadratic phase operator cubes to the identity."))),
            DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("original-fourm-shifted-chart-source-multipliers"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.chart_source_multipliers"),
            H("Source multipliers of the B and D charts"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("At each chart source the forward exponential from theta inversion equals the exponential of half the complementary covariance discrepancy times the original Gram quadratic of that chart's source vector."))),
            DescribeRole.Theorem))));
}
