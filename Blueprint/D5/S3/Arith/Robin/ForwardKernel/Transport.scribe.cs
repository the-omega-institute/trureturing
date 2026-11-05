using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class TransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/Transport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original complete Chebyshev response has an exact finite signed price-kernel representation.",
        H("Transport of the original forward kernel"),
        Blocks(
            Paragraph(Text(
                "Write E(t)=psi(t)-t, H(x)=x^(4/5), B(x)=x+H(x), "
                + "lambda(t)=1/(t*log(t)), and w(t)=(log(t)+1)/(t^2*log(t)^2). "
                + "The functions H, B, lambda, w, and E are the existing width, "
                + "endpoint, g, weight, and discrepancy functions. The response is "
                + "T(x)=sqrt(x)/H(x)^2 times the integral from 0 to H(x) of "
                + "(E(x+u)-E(x))*w(x+u)/w(x).")),
            Describe.Lean(
                DescribeId.Create("forward-response-interval-integrable"),
                DeclarationHandle.Create(Prefix + "forwardResponse_intervalIntegrable"),
                H("Existence of the finite response integral"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every x>1 the integrand defining T(x) is interval integrable. "
                    + "Monotonicity makes psi integrable on compact intervals; "
                    + "subtracting the continuous coordinate and multiplying by "
                    + "the continuous weight preserves this property."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-response-signed-price"),
                DeclarationHandle.Create(Prefix + "forwardResponse_eq_signed_price"),
                H("The complete finite signed price identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every x>1, T(x)=sqrt(x)/(w(x)*H(x)^2) times "
                        + "the sum of Lambda(n)*(lambda(n)-lambda(B(x))) over "
                        + "x<n<=B(x), minus the integral from x to B(x) of "
                        + "lambda(t)-lambda(B(x)). The arithmetic sum is written "
                        + "as the difference of two right-closed weighted prefixes. "
                        + "Thus an initial atom is excluded, and a terminal atom "
                        + "has zero price difference. Every prime power carries "
                        + "the full von Mangoldt weight.")),
                    Paragraph(Text(
                        "The finite arithmetic integration-by-parts identity and "
                        + "its continuous counterpart are applied to the same "
                        + "price curve. Subtracting them produces E(t)-E(x). "
                        + "Translation t=x+u and the exact normalization give "
                        + "the stated original response."))),
                DescribeRole.Theorem))));
}
