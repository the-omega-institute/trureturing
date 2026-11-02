using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class OriginalHalfBinomialEndpointDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/OriginalHalfBinomialEndpoint.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complementary original half-binomial period determines the radial nome normalization.",
        H("Original Period Endpoint and Nome"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("original-period-log16"),
                DeclarationHandle.Create(Prefix + "original_period_log16"),
                H("The complementary logarithmic constant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let F(r) be the real part of OriginalHalfBinomialPeriod.period "
                        + "at the real argument r. This is the literal sum of halfBinomial(n)^2 "
                        + "times r^n. As r tends to zero through positive real numbers, "
                        + "pi F(1-r)+log(r) tends to log(16). No endpoint expansion or "
                        + "normalization is assumed, and no value at the singular argument 1 "
                        + "is assigned to the totalized series.")),
                    Paragraph(Text("The exact Euler sine integral, reflected through pi/4, "
                        + "writes (pi/2) F(1-r) as the integral of "
                        + "A(r,theta)=1/sqrt(r+(1-r) sin(theta)^2) over [0,pi/2]. Subtract "
                        + "B(r,theta)=cos(theta)/sqrt(r+sin(theta)^2). For 0<r<1 their "
                        + "difference lies between zero and two on that whole angle interval. "
                        + "At each positive angle it tends to sin(theta)/(1+cos(theta)). "
                        + "Dominated convergence applies with the constant integrable bound two. "
                        + "The limiting integral is log(2), by the primitive "
                        + "-log(1+cos(theta)). The primitive of B is "
                        + "log(sin(theta)+sqrt(r+sin(theta)^2)); its boundary difference is "
                        + "log(1+sqrt(1+r))-log(r)/2. Adding these two integrals gives "
                        + "the constant log(16)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-nome-quotient"),
                DeclarationHandle.Create(Prefix + "original_nome_quotient"),
                H("The immediately normalized radial nome"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The quotient exp(-pi F(1-r)/F(r))/r tends to 1/16 as "
                        + "r tends to zero through positive real numbers. The convention is "
                        + "q=exp(pi i tau), with tau=i F(1-r)/F(r). The conclusion concerns "
                        + "this literal quotient on its radial limiting filter; no total "
                        + "extension of the nome at zero is needed.")),
                    Paragraph(Text("The original integral at zero gives F(0)=1. The native "
                        + "complex differentiability supplied by the original Picard-Fuchs "
                        + "theorem restricts to a real derivative at zero. Differentiating "
                        + "the reciprocal therefore gives a finite limit for "
                        + "(1/F(r)-1)/r. Multiplication by r log(r), which tends to zero, "
                        + "pays the correction log(r)(1/F(r)-1). The exponent identity "
                        + "-pi F(1-r)/F(r)-log(r)=-(pi F(1-r)+log(r))/F(r)"
                        + "+log(r)(1/F(r)-1) then gives the limit -log(16). Exponentiation "
                        + "and exp(log(r))=r for r>0 give the asserted quotient.")),
                    Paragraph(Text("These are classical elliptic-period asymptotics for the "
                        + "original coefficient series. They supply an analytic normalization; "
                        + "Wronskians, a nome derivative, infinite determinants, a physical "
                        + "Gaussian realization, string theory and an AdS/CFT correspondence "
                        + "require further results."))),
                DescribeRole.Theorem))));
}
