using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMCauchyTaylorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCauchyTaylor.";

    private static DocumentBlock Result(string id, string declaration, string heading, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Taylor coefficients of the original same-puncture free subtraction",
        H("Same-Puncture Cauchy Taylor Coefficients"),
        Blocks(
            Result("fourm-chart-free-correction-coefficient", "chart_free_correction_coefficient",
                "Taylor coefficient of the chart subtraction",
                "The analytic binomial roots and the inverse of their sum have the same "
                + "ordinary Taylor coefficients as the regular Laurent-chamber expression. "
                + "Each pair of indices gives the finite lowering contraction."),
            Result("fourm-native-free-correction-coefficient", "native_free_correction_coefficient",
                "Pair in the native order of the Taylor selectors",
                "Exchanging the two creators in the original oscillator word preserves its highest "
                + "lowering coefficient. This identifies the Gram-weighted subtraction in the "
                + "order used by the native covariance selectors."),
            Result("fourm-inverse-physical-free-correction-coefficient",
                "inverse_physical_free_correction_coefficient",
                "The original inverse-coordinate pair",
                "The normalized inverse lift gives the contraction at the negative lowering "
                + "parameter, with one inverse scale factor at each incoming mode."),
            Result("fourm-inverse-physical-two-leg-coefficient", "inverse_physical_two_leg_coefficient",
                "Finite Taylor transform in both legs",
                "The native order of the selectors preserves the two independent finite "
                + "transforms and the half-current scale in each leg."),
            Result("fourm-selected-physical-covariance", "selected_physical_covariance",
                "Taylor entries of the regular physical covariance",
                "Every chart block has the two creator transforms. Only the same-puncture "
                + "block contributes the additional Gram-weighted lowering contraction."),
            Result("fourm-selected-radial-physical-covariance", "selected_radial_physical_covariance",
                "Literal sewn covariance entries on the native radial charts",
                "On A and B the signed Taylor selectors in the finite transform are the "
                + "original tagged entries of the sewn effective matrix."))));
}
