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
            DescribeRole.Theorem))));
}
