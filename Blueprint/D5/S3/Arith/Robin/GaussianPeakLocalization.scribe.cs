using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class GaussianPeakLocalizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/GaussianPeakLocalization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A local upper bound for H controls the full signed Gaussian response, including its tails.",
        H("Signed Gaussian peak localization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gaussian-peak-localization"),
                DeclarationHandle.Create(Prefix + "gaussian_peak_localization"),
                H("Absence of a positive peak bounds the full response"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let m>=1 and gamma>10. Use the Gaussian density g with mean 16*m "
                        + "and variance 2*m, coordinate u=(y-16*m)/(2*m), the oscillatory "
                        + "kernel K, and its nonnegative envelope v=2*(u^2+gamma^2+1)*g. "
                        + "Suppose H*K and H*v are integrable, |H(y)|<=2*exp(max(y,0)), "
                        + "|K|<=v, and |integral H*v|<=1000*(gamma+10)^2*exp(-83*m). "
                        + "If H(y)<=(4*y+11)*exp(y/2) on [4*m,28*m], then "
                        + "integral H*K<=2000*m*(gamma+10)^2*exp(33*m/4).")),
                    Paragraph(Text(
                        "The signed identity integral H*K=integral H*(K+v)-integral H*v "
                        + "retains the entire envelope integral. Since 0<=K+v<=2*v, "
                        + "three nonnegative Gaussian polynomial majorants control the "
                        + "response on the interval, on its nonnegative complement, and "
                        + "on the negative half-line. Their whole-line integrals give "
                        + "upper bounds for those three contributions; no exterior term is discarded.")),
                    Paragraph(Text(
                        "On the interval, exponential tilting moves the Gaussian mean to 17*m "
                        + "and gives exp(33*m/4). With z=y-17*m, the identity "
                        + "81*m+2*z^2-(4*y+11)=13*(m-1)+2*(z-1)^2 and "
                        + "u^2<=1/2+z^2/(2*m^2) reduce the integral to the second and "
                        + "fourth central moments 2*m and 12*m^2. The resulting contribution "
                        + "is at most 600*m*(gamma+10)^2*exp(33*m/4).")),
                    Paragraph(Text(
                        "On the nonnegative exterior, tilting gives mean 18*m and "
                        + "|y-18*m|>=10*m. Splitting the Gaussian exponent into equal halves "
                        + "leaves variance 4*m and pays exp(-25*m/2). Its contribution is "
                        + "at most 24*(gamma+10)^2*exp(9*m/2). On the negative half-line, "
                        + "|y-16*m|>=16*m pays exp(-32*m), giving at most "
                        + "16*(gamma+10)^2*exp(-32*m). Together with the full envelope "
                        + "integral these bounds are below the stated constant 2000.")),
                    Paragraph(Text(
                        "The scalar even moments are supplied by the existing "
                        + "CountableGaussianQuadraticFourthMoment.centralMoment_two_mul theorem. "
                        + "The localization statement applies to any real H meeting the displayed "
                        + "growth, integrability, kernel and envelope conditions, including the "
                        + "complete zero response at the scale selected by full_zero_gaussian_response."))),
                DescribeRole.Theorem))));
}
