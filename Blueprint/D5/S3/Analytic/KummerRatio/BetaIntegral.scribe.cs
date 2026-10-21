using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KummerRatio;

internal sealed class BetaIntegralDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Beta moments and integral formulas for the Kummer function.",
        H("Beta integral representation"), Blocks(
            Describe.Lean(DescribeId.Create("kummer-real-beta-integral"),
                DeclarationHandle.Create("D5/S3/Analytic/KummerRatio/BetaIntegral.integral_beta"),
                H("Real beta moments"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive real p and q, the integral over the unit interval of t raised to p minus one times one minus t raised to q minus one equals Gamma(p) Gamma(q) divided by Gamma(p+q). The complex beta identity transfers to this real integral because both bases are nonnegative on the integration interval."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("kummer-beta-integrability"),
                DeclarationHandle.Create("D5/S3/Analytic/KummerRatio/BetaIntegral.intervalIntegrable_beta"),
                H("Integrable beta weight"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive shape parameters, the real beta weight is integrable over the unit interval. This follows by taking the real part of the convergent complex beta integrand."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("kummer-beta-representation"),
                DeclarationHandle.Create("D5/S3/Analytic/KummerRatio/BetaIntegral.kummer_eq_betaIntegral"),
                H("The beta representation of Kummer's function"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When zero is less than s and s is less than c, Kummer's function M(s;c;x) is the integral of exp(xt) against the beta weight t^(s-1)(1-t)^(c-s-1), multiplied by Gamma(c)/(Gamma(s) Gamma(c-s)). The exponential series is integrated term by term. The terms in absolute value are bounded by the beta weight multiplied by |x|^n/n!, whose sum is integrable. The Gamma and ascending Pochhammer identity identifies each resulting beta moment with the pinned Kummer coefficient."))),
                DescribeRole.Theorem))));
}
