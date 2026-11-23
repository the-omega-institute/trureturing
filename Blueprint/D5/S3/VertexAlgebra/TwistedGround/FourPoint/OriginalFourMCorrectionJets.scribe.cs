using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMCorrectionJetsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCorrectionJets.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Same-puncture covariance Taylor coefficients",
        H("The subtracted physical correction"),
        Blocks(
            Describe.Lean(DescribeId.Create("original-fourm-same-puncture-correction-coefficient"),
                DeclarationHandle.Create(Prefix + "coefficient_neg_slotCorrection_div_jac"),
                H("Two-variable contraction coefficients"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real 0 < x < 1, any chart and any puncture, take the degree p "
                    + "coefficient in the first displacement and degree q in the second of the negative "
                    + "same-puncture correction divided by both half-Jacobians. For all natural p and q, "
                    + "the result is the negative lowering parameter divided by the scale, raised to "
                    + "p+q+1, times the inverse lowering contraction scalar at p and q."))),
                DescribeRole.Theorem))));
}
