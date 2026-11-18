using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMChartProductDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChartProduct.";

    private static DocumentBlock Result(string id, string declaration, string heading, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rank-24 cancellation for the native four-point Gaussian and charge-sector product",
        H("Four-Point Gaussian and Theta Product"),
        Blocks(
            Result("fourm-pulled-covariance-off-diagonal", "pulled_covariance_off_diagonal",
                "Pulled covariance in common coordinates",
                "Off the geometric poles the signed A overlap gives the B and D elliptic covariances "
                + "with the common A free subtraction. The original mixed free block is included."),
            Result("fourm-native-sample-mean", "native_sample_mean", "Native signed charge mean",
                "The actual Gaussian mean sums to the signed half-coordinate source contracted "
                + "with the colour and charge and divided by the slit period."),
            Result("fourm-physical-source-signs", "physical_source_signs", "Physical source signs",
                "The relative sign at S in the B chart and at Q and R in the D chart "
                + "agrees with the chosen lift at each physical puncture."),
            Result("fourm-chart-product-charge-sum", "chart_product_charge_sum", "Original charge fiber",
                "The product is the original mod-two charge sum. Its linear exponent is the "
                + "weighted sum of the signed transported charge means."),
            Result("fourm-native-rank24-determinant", "native_rank24_determinant", "Native rank-24 determinant",
                "On the open disk the oscillator determinant contributes the inverse third "
                + "power of one minus the period argument and the inverse twelfth power of the Euler period."),
            Result("fourm-native-chart-product", "native_chart_product", "Complementary cancellation",
                "For every finite family of external source weights the forward theta exponential "
                + "cancels the Gram-contracted Gaussian correction. The D comparison uses the normalized "
                + "original Fourier row. The B comparison first uses the Pfaff translation and then "
                + "complementary inversion, with the quadratic sign in the Fourier summand and "
                + "the inverse twelfth power of the Pfaff root."),
            Result("fourm-chart-product-b-from-d", "chart_product_B_from_D",
                "The common B and D sector expression",
                "The rank-24 finite Weil relations give the B product from the D products. "
                + "The summand uses the original quadratic sign of the sum of the two sectors."),
            Result("fourm-pulled-sample-differentials", "pulled_sample_differentials",
                "Signed half-differentials at native samples",
                "The source at each nonpunctured sample is the pullback of the half-differential "
                + "on the target elliptic cubic for both lifts."),
            Result("fourm-physical-free-subtraction-difference", "physical_free_subtraction_difference",
                "Free subtraction in common physical coordinates",
                "For any two of the actual charts the difference of the same-puncture free kernels "
                + "is the difference of the two regular lowering corrections."))));
}
