using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class TriangularMeanSquareDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/TriangularMeanSquare.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The variance band asymptotic determines fixed-length profile mean squares.",
        H("Fixed-length profile mean square"),
        Blocks(
            Paragraph(Text(
                "Let E be a Borel real function bounded on compact intervals, "
                + "D_u(x)=E(x+u)-E(x), and let g be an integrable real profile on [0,1]. "
                + "Write P_(h,g)(x)=h^(-1) integral from zero to one of g(s)D_(sh)(x), "
                + "and Q(g) for the double integral of g(s)g(t)min(s,t) on the unit square. "
                + "Assume 0<alpha<theta<beta<1 and cumulative variance asymptotic "
                + "Y*h*log(Y/h), uniformly for Y^alpha<=h<=Y^beta.")),
            Describe.Lean(
                DescribeId.Create("interval-square-tendsto-of-l2-negligible"),
                DeclarationHandle.Create(Prefix + "interval_square_tendsto_of_l2_negligible"),
                H("Negligible perturbations preserve normalized square limits"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let f and g be square integrable on ordered intervals whose endpoints depend on X, and let S(X) be eventually positive. If the square integral of g divided by S tends to a nonnegative L and that of f-g divided by S tends to zero, then the square integral of f divided by S also tends to L. The reverse triangle inequality first compares the square roots, then squaring recovers the limit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("min-kernel-integrable"),
                DeclarationHandle.Create(Prefix + "min_kernel_integrable"),
                H("Integrability of the min-kernel energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every integrable real profile g on the unit interval, the function g(s)g(t)min(s,t) is integrable on the unit square. The product g(s)g(t) is integrable by Fubini, and min(s,t) lies between zero and one on the square."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fixed-length-profile-mean-square-tendsto"),
                DeclarationHandle.Create(Prefix + "fixed_length_profile_mean_square_tendsto"),
                H("The fixed-length profile mean square"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix 1<=a<b<=2 and c>0. With h=c*X^theta and ell=log(X/h), "
                        + "the integral of P_(h,g)(x)^2 over [a*X,b*X], divided by "
                        + "(X/h)*ell, tends to (b-a)*Q(g).")),
                    Paragraph(Text(
                        "Rescaling to the unit interval and absolute Fubini express the "
                        + "normalized square mass as the integral of g(s)g(t) times the "
                        + "normalized increment covariance on the full unit square. "
                        + "The covariance tends pointwise to (b-a)*min(s,t). The uniform "
                        + "shorter-increment square bound and Cauchy-Schwarz bound its "
                        + "absolute value by one constant C. The integrable majorant "
                        + "C*abs(g(s)g(t)) permits dominated convergence for every L1 "
                        + "profile, without a small-length cutoff or a separate "
                        + "short-interval mean-square hypothesis."))),
                DescribeRole.Theorem))));
}
