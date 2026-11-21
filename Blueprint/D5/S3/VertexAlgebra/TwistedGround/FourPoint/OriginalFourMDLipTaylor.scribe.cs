using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMDLipTaylorDocument : IScribeDocumentDefinition
{
    private const string FourPoint = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/";
    private const string Prefix = FourPoint + "OriginalFourMDLipTaylor.";
    private const string SlitTaylor = FourPoint + "OriginalFourMSlitTaylor.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Taylor entries of the native D-lip mean and covariance and their slit agreement",
        H("Holomorphic boundary entries and agreement on the open lip"),
        Blocks(
            D("d-lip-mean-entry", "dLipMeanEntry", "D-lip mean entry", DescribeRole.Definition,
                Text("Take the signed mean on the selected D lip, multiply by minus the leg sign "
                    + "and divide by the D period before taking the ordinary external coefficient of order p. "),
                Ref(FourPoint + "OriginalFourMDLipMean.dLipMean")),
            D("d-lip-mean-entry-analytic", "dLipMeanEntry_analyticAt", "Holomorphic D-lip mean entries",
                DescribeRole.Theorem,
                Text("For either lip, every leg, sign and Taylor order gives an analytic function at "
                    + "each real t > 1 viewed in ℂ. The source is jointly holomorphic and the D period "
                    + "is nonzero at t, so taking the fixed external coefficient preserves analyticity. "),
                Ref(FourPoint + "OriginalFourMDLipMean.dLipMean_joint_analytic")),
            D("d-lip-mean-entry-slit", "dLipMeanEntry_eq_slit", "Mean entry agreement on the open lip",
                DescribeRole.Theorem,
                Text("At every point on the selected open D lip, equality of the source germs near "
                    + "the external origin and equality of the periods identify the two mean entries. "),
                Ref(FourPoint + "OriginalFourMDLipMean.dLipMean_eventuallyEq"), Text(", "),
                Ref(FourPoint + "OriginalFourMPeriodSource.dPeriod_eq_slit"), Text(", "),
                Ref(SlitTaylor + "slitMeanEntry")),
            D("d-lip-covariance-entry", "dLipCovarianceEntry", "D-lip covariance entry", DescribeRole.Definition,
                Text("Multiply the selected D-lip covariance by the complex Gram entry of the labels "
                    + "and take ordinary Taylor coefficients at zero in u and v using their mode orders. "),
                Ref(FourPoint + "OriginalFourMDLipCovariance.dLipCovariance")),
            D("d-lip-covariance-entry-analytic", "dLipCovarianceEntry_analyticAt",
                "Holomorphic D-lip covariance entries", DescribeRole.Theorem,
                Text("For every real t > 1 the D-lip covariance is jointly holomorphic at (0,0,t). "
                    + "Two successive applications of the analytic slice argument give boundary "
                    + "analyticity of the fixed entry for either lip and every pair of signed labels. "),
                Ref(FourPoint + "OriginalFourMDLipCovariance.dLipCovariance_joint_analytic")),
            D("d-lip-covariance-entry-slit", "dLipCovarianceEntry_eq_slit",
                "Covariance entry agreement on the open lip", DescribeRole.Theorem,
                Text("Fix r on the selected open D lip. Mean agreement holds near each external origin, "
                    + "so covariance agreement holds near both origins. Germ congruence for each "
                    + "Taylor extraction identifies the full entry, including the Gram factor. "),
                Ref(FourPoint + "OriginalFourMDLipCovariance.dLipCovariance_eq_of_means"), Text(", "),
                Ref(SlitTaylor + "slitCovarianceEntry")))));

    private static DocumentBlock D(string id, string declaration, string title, DescribeRole role,
        params Inline[] content) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(content)), role);
}
