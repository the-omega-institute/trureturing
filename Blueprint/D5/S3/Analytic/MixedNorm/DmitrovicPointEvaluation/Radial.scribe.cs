using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation;

internal sealed class RadialDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mixed norms and power-family point evaluations.",
        H("Radial"), Blocks(
            Describe.Lean(DescribeId.Create("dm-radial-radialintegral"),
                DeclarationHandle.Create("D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Radial.radialIntegral"),
                H("The radial norm integral"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For finite positive p and q, this real interval integral is the q-th power of the power-family mixed norm. Its parameter t is the square of the affine parameter a. The weight may have an integrable singularity at radius one."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("dm-radial-evaluationexcess"),
                DeclarationHandle.Create("D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Radial.evaluationExcess"),
                H("The normalized evaluation power"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Put c=1/(1+alpha p). The expression (1+ct) raised to 2q/p times (1-c squared t) raised to alpha q+q/p is the q-th power of the normalized evaluation at ca, where t=a squared."))),
                DescribeRole.Definition))));
}
