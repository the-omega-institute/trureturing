using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMSlitTaylorDocument : IScribeDocumentDefinition
{
    private const string FourPoint = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/";
    private const string Prefix = FourPoint + "OriginalFourMSlitTaylor.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact Taylor entries of the native signed Gaussian on the Euler slit",
        H("Signed mean and covariance coefficients"),
        Blocks(
            D("analytic-coefficient-slice", "analytic_coefficient_slice",
                "Analytic dependence of a Taylor coefficient", DescribeRole.Theorem,
                Text("Let f be complex analytic at (0,y) on the product of ℂ and a complex normed "
                    + "space. For every n, the ordinary order-n coefficient at zero of the first "
                    + "variable is analytic in the remaining variable at y."), Text(" Iterate the "
                    + "directional Fréchet derivative in the first coordinate, restrict to the slice "
                    + "at zero and divide by n factorial. Near y those directional derivatives "
                    + "agree with the iterated one-variable derivatives.")),
            D("slit-mean-entry", "slitMeanEntry", "Slit mean entry", DescribeRole.Definition,
                Text("At a fixed leg and sign, take the ordinary coefficient of order p at the external "
                    + "origin of the slit mean multiplied by minus the leg sign and divided by the Euler period. "
                    + "The lattice pairing with the charge supplies the remaining linear factor. "),
                Ref(FourPoint + "OriginalFourMSlitMean.slitMean")),
            D("slit-mean-entry-analytic", "slitMeanEntry_analyticOnNhd", "Holomorphic mean entries",
                DescribeRole.Theorem,
                Text("Every fixed Taylor entry of the signed mean is holomorphic in r on the Euler slit. "
                    + "Iterate the Fréchet derivative in the external coordinate, restrict to the external "
                    + "origin, and divide by p factorial. This agrees locally with the one-variable derivative."),
                Text(" The joint germ is supplied by "),
                Ref(FourPoint + "OriginalFourMSlitMean.slitMean_joint_analytic"), Text(".")),
            D("slit-covariance-entry", "slitCovarianceEntry", "Slit covariance entry", DescribeRole.Definition,
                Text("Multiply the signed covariance germ by the complex Gram entry of the two labels. "
                    + "Take the ordinary Taylor coefficient in each external variable at zero, using their "
                    + "respective mode orders. "),
                Ref(FourPoint + "OriginalFourMSlitCovariance.slitCovariance")),
            D("slit-covariance-entry-analytic", "slitCovarianceEntry_analyticOnNhd",
                "Holomorphic covariance entries", DescribeRole.Theorem,
                Text("For all leg choices and signed external labels the iterated coefficient is "
                    + "holomorphic in r on the Euler slit. Apply the analytic slice argument first to u "
                    + "with (v,r) as parameters and then to v with r as parameter. "),
                Ref(FourPoint + "OriginalFourMSlitCovariance.slitCovariance_joint_analytic")),
            D("slit-covariance-entry-native", "slitCovarianceEntry_eq_native",
                "Identification with the original covariance entry", DescribeRole.Theorem,
                Text("For every complex opening w with |w| < 1, the slit coefficient at r = w² equals "
                    + "the actual effective kernel at the two tagged modes. The covariance germs agree "
                    + "on small external disks, hence their successive derivatives at zero agree. "),
                Ref(FourPoint + "OriginalFourMSignedCovariance.native_tagged_entry"), Text(", "),
                Ref(FourPoint + "OriginalFourMSlitCovariance.slitCovariance_eq_native")),
            D("slit-mean-entry-native", "slitMeanEntry_eq_native",
                "Identification with the original charge-linear entry", DescribeRole.Theorem,
                Text("For each charge and tagged mode at |w| < 1, pairing the charge with the label's "
                    + "unit charge and multiplying by the slit entry at w² gives the actual Gaussian mean. "
                    + "The native source-amplitude series converges around the external origin. "
                    + "Coefficient extraction recovers its p-th amplitude with the period and leg factors. "),
                Ref(FourPoint + "OriginalFourMSlitMean.slitMean_eq_sourceMode"), Text(", "),
                Ref(FourPoint + "OriginalFourMSignedCovariance.native_mean")))));

    private static DocumentBlock D(string id, string declaration, string title, DescribeRole role,
        params Inline[] content) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(content)), role);
}
