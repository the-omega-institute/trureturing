using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class LogarithmicEndpointVariationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/LogarithmicEndpointVariation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cubic Mellin endpoint moments pay the entire logarithmic fourth variation.",
        H("Logarithmic Endpoint Variation"),
        Blocks(
            Paragraph(Text(
                "Positive mixing of a full family of power moments reaches the weight "
                + "m/log(m)^4. The proof first integrates finite prefixes and then bounds "
                + "all nonnegative partial sums, so logarithmic summability is a conclusion.")),
            Describe.Lean(
                DescribeId.Create("cubic-endpoint-logarithmic-payment"),
                DeclarationHandle.Create(Prefix + "log_four_variation_of_cubic_endpoint_moments"),
                H("Cubic endpoint moments pay the full logarithmic weight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a(m)>=0 and C>=0. For every 0<beta<=1/2 assume every "
                        + "finite prefix over m>=8 of m^(1-beta)*a(m) is at most C/beta^3. "
                        + "Then m/log(m)^4*a(m) is summable over all integers m>=2, "
                        + "and its infinite sum is at most its exact six-term sum over "
                        + "2<=m<=7 plus 2*exp(1)*C.")),
                    Paragraph(Text(
                        "For m>=8, integrate beta^3*m^(1-beta) over 0<beta<1/2. "
                        + "Its restriction to 0<beta<1/log(m) pays at least "
                        + "m/(4*exp(1)*log(m)^4). The same mixed finite prefix is at "
                        + "most C/2. The finite head is preserved and all partial sums "
                        + "are bounded before the infinite-sum theorem is applied."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("envelope-logarithmic-four-variation"),
                DeclarationHandle.Create(Prefix + "logarithmic_four_weighted_variation"),
                H("The logarithmic envelopes pay the complete Robin variation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let rho be measurable, d,a,mu>=0, x>1, and assume the same "
                        + "pointwise envelopes |rho(y)|<=d*y+a*(-log(y)*y) for "
                        + "0<y<=1 and |rho(y)|<=mu*(1+log(y)) for y>=1. "
                        + "Write L=log(x), h1=1+1/L, h2=1+2/L+2/L^2, and "
                        + "C=(h1/2+h2)*(a+d/2+3*mu/2)/L.")),
                    Paragraph(Text(
                        "With the existing clipped integral P(rho,x,m), the complete "
                        + "sequence m/log(m)^4*|P(rho,x,m)-P(rho,x,m+1)| for m>=2 "
                        + "is summable. Its infinite sum is at most the exact six-term "
                        + "sum over 2<=m<=7 plus 2*exp(1)*C. The strict cutoff "
                        + "x/m<y, including zero at equality, is the existing genericP.")),
                    Paragraph(Text(
                        "The logarithmic Mellin reserve directly supplies the entire "
                        + "family alpha=1-beta, 0<beta<=1/2. Its bound grows at most "
                        + "as C/beta^3. The preceding theorem then pays the full "
                        + "logarithmic fourth variation. Arithmetic coefficient growth, "
                        + "interchange in the original integral variable and the final "
                        + "signed Robin estimate still require their own proofs."))),
                DescribeRole.Theorem))));
}
